"""Null-space (reduced) solver for the MC systems: eliminates all equality constraints with an orthonormal
null-space basis (well conditioned, no redundancy), then solves the pure-PSD problem with Clarabel or SCS.
Memory is checked before any dense allocation."""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sp
import scipy.linalg as sla
from memguard import mem_gb

MAX_DENSE_GB = float(os.environ.get('GYNI_MAX_DENSE_GB', '2.0'))


def _check(nbytes, what):
    gb = nbytes / 1e9
    if gb > MAX_DENSE_GB:
        raise MemoryError(f"refusing dense allocation of {gb:.2f} GB for {what}")


def eq_matrix(rows, n):
    r, c, v, b = [], [], [], []
    for i, (d, rhs) in enumerate(rows):
        for k, x in d.items():
            r.append(i); c.append(k); v.append(x)
        b.append(rhs)
    return sp.csr_matrix((v, (r, c)), shape=(len(rows), n)), np.array(b, float)


def nullspace(Aeq, beq, tol=1e-9):
    n = Aeq.shape[1]
    _check(8 * n * n * 3, "A^T A eigendecomposition")
    AtA = (Aeq.T @ Aeq).toarray()
    w, V = np.linalg.eigh(AtA)
    wmax = max(w.max(), 1.0)
    null_mask = w < tol * wmax
    N = V[:, null_mask]
    R = V[:, ~null_mask]
    # particular solution: minimum-norm least squares restricted to row space
    Atb = Aeq.T @ beq
    z0 = R @ ((R.T @ Atb) / w[~null_mask])
    res = np.abs(Aeq @ z0 - beq).max() if Aeq.shape[0] else 0.0
    return z0, N, res, int((~null_mask).sum())


class AffineUF:
    """union-find with multiplicative relations x_i = f_i * x_parent ; index n is the constant ONE (x=1)."""

    def __init__(self, n):
        self.n = n
        self.parent = list(range(n + 1))
        self.fac = [1.0] * (n + 1)

    def find(self, i):
        # returns (root, factor) with x_i = factor * x_root ; path compression
        path = []
        f = 1.0
        j = i
        while self.parent[j] != j:
            path.append(j)
            j = self.parent[j]
        root = j
        # compress
        for k in reversed(path):
            p = self.parent[k]
            if p != root:
                self.fac[k] *= self.fac[p]
                self.parent[k] = root
        return root, (self.fac[i] if i != root else 1.0)

    def relate(self, i, j, a):
        """impose x_i = a * x_j. Returns False if inconsistent."""
        ri, fi = self.find(i)
        rj, fj = self.find(j)
        ONE = self.n
        # x_ri = (a fj / fi) x_rj
        if fi == 0:
            # x_i = 0 * x_ri : relation says a*fj*x_rj = 0
            if a * fj == 0:
                return True
            return self._set_zero(rj)
        r = a * fj / fi
        if ri == rj:
            if abs(r - 1.0) < 1e-12:
                return True
            if ri == ONE:
                return False
            return self._set_zero(ri)   # x_ri = r x_ri with r != 1 -> x_ri = 0
        if ri == ONE:
            # attach rj under ONE: x_rj = x_ri / r  (if r == 0 -> x_ONE = 0 impossible)
            if r == 0:
                return False
            self.parent[rj] = ONE; self.fac[rj] = 1.0 / r
            return True
        self.parent[ri] = rj; self.fac[ri] = r
        return True

    def _set_zero(self, r):
        ONE = self.n
        if r == ONE:
            return False
        self.parent[r] = ONE; self.fac[r] = 0.0
        return True


def reduce_rows_uf(rows, n, verbose=True):
    """Solve simple rows exactly via affine union-find; return (uf, remaining rows over roots)."""
    uf = AffineUF(n)
    ONE = n
    pending = list(rows)
    changed = True
    rounds = 0
    while changed:
        changed = False
        rounds += 1
        rest = []
        for row, rhs in pending:
            # rewrite over roots
            acc = {}
            const = rhs
            for v, c in row.items():
                r, f = uf.find(v)
                if f == 0:
                    continue
                if r == ONE:
                    const -= c * f
                else:
                    acc[r] = acc.get(r, 0.0) + c * f
            acc = {r: c for r, c in acc.items() if abs(c) > 1e-13}
            if not acc:
                if abs(const) > 1e-9:
                    raise ValueError(f"inconsistent row (residual {const})")
                continue
            items = list(acc.items())
            if len(items) == 1:
                (r, c), = items
                ok = uf.relate(r, ONE, const / c)
                if not ok:
                    raise ValueError("inconsistent")
                changed = True
            elif len(items) == 2 and abs(const) < 1e-15:
                (r1, c1), (r2, c2) = items
                ok = uf.relate(r1, r2, -c2 / c1)
                if not ok:
                    raise ValueError("inconsistent")
                changed = True
            else:
                rest.append((acc, const))
        pending = rest
    roots = sorted({uf.find(i)[0] for i in range(n)} - {ONE})
    if verbose:
        print(f"  [uf] {n} vars -> {len(roots)} free roots, {len(pending)} multi-term rows ({rounds} rounds)", flush=True)
    return uf, roots, pending


def nullspace_components(Ar, br, tol=1e-9, verbose=True):
    """Null space of a sparse system A_r y = b_r that decomposes into connected components (rows <-> columns).
    Returns (y0, N) with N SPARSE (block structure) and orthonormal columns; each column lives in one component."""
    from scipy.sparse.csgraph import connected_components
    m, nr = Ar.shape
    Ab = Ar.copy().tocsr(); Ab.data[:] = 1.0
    G = sp.bmat([[None, Ab], [Ab.T, None]]).tocsr()
    ncomp, lab = connected_components(G, directed=False)
    row_lab = lab[:m]; col_lab = lab[m:]
    Arc = Ar.tocsc()
    y0 = np.zeros(nr)
    Nr, Nc, Nv = [], [], []
    k = 0
    maxsize = 0
    worst = 0.0
    order_cols = np.argsort(col_lab, kind='stable')
    order_rows = np.argsort(row_lab, kind='stable')
    cstarts = np.searchsorted(col_lab[order_cols], np.arange(ncomp + 1))
    rstarts = np.searchsorted(row_lab[order_rows], np.arange(ncomp + 1))
    for c in range(ncomp):
        cols = order_cols[cstarts[c]:cstarts[c + 1]]
        if len(cols) == 0:
            continue
        rws = order_rows[rstarts[c]:rstarts[c + 1]]
        maxsize = max(maxsize, len(cols))
        if len(rws) == 0:
            for j in cols:
                Nr.append(j); Nc.append(k); Nv.append(1.0); k += 1
            continue
        A = Ar[rws][:, cols].toarray()
        b = br[rws]
        U, s, Vt = np.linalg.svd(A, full_matrices=True)
        smax = max(s.max() if len(s) else 0.0, 1.0)
        rank = int(np.sum(s > np.sqrt(tol) * smax))
        Vn = Vt[rank:].T                      # null vectors of the component
        yc = Vt[:rank].T @ ((U[:, :rank].T @ b) / s[:rank]) if rank else np.zeros(len(cols))
        worst = max(worst, np.abs(A @ yc - b).max() if len(b) else 0.0,
                    np.abs(A @ Vn).max() if Vn.size else 0.0)
        y0[cols] = yc
        for t in range(Vn.shape[1]):
            v = Vn[:, t]
            nz = np.nonzero(np.abs(v) > 1e-15)[0]
            Nr.extend(cols[nz].tolist()); Nc.extend([k] * len(nz)); Nv.extend(v[nz].tolist())
            k += 1
    N = sp.csr_matrix((Nv, (Nr, Nc)), shape=(nr, k))
    if verbose:
        print(f"  [uf] components {ncomp}, largest {maxsize} roots, nullity {k}, max residual {worst:.2e}", flush=True)
    if worst > 1e-8:
        raise ValueError(f"component null space inaccurate ({worst:.2e})")
    return y0, N


def nullspace_uf(rows, n, tol=1e-9, verbose=True, factored=False, consume=False, components=False):
    """Feasible set {x : rows} = {x0 + Bm theta}; Bm dense (n x k).
    consume=True clears the caller's row list after the union-find pass (frees memory before the eigensolver)."""
    uf, roots, rest = reduce_rows_uf(rows, n, verbose)
    if consume:
        rows.clear()
        import gc; gc.collect()
    ridx = {r: t for t, r in enumerate(roots)}
    nr = len(roots)
    # reduced system over roots
    rr_, cc_, vv_ = [], [], []
    br = np.zeros(len(rest))
    for i, (acc, const) in enumerate(rest):
        for r, c in acc.items():
            rr_.append(i); cc_.append(ridx[r]); vv_.append(c)
        br[i] = const
    Ar = sp.csr_matrix((vv_, (rr_, cc_)), shape=(len(rest), nr))
    del rest, rr_, cc_, vv_
    if len(br) and components:
        y0, N = nullspace_components(Ar, br, tol=tol, verbose=verbose)
        res = np.abs(Ar @ y0 - br).max()
    elif len(br):
        if nr <= 12000:
            _check(8 * nr * nr * 3.2, "reduced nullspace")
            AtA = (Ar.T @ Ar).toarray()
            w, V = np.linalg.eigh(AtA)              # divide & conquer, full spectrum (robust for big null clusters)
            del AtA
            wmax = max(w.max(), 1.0)
            k0 = int(np.sum(w < tol * wmax))        # eigenvalues ascending -> null space = first k0 columns
            assert np.all(w[:k0] < tol * wmax) and np.all(w[k0:] >= tol * wmax)
            N = V[:, :k0]; R = V[:, k0:]            # views, no copies
            y0 = R @ ((R.T @ (Ar.T @ br)) / w[k0:])
            res = np.abs(Ar @ y0 - br).max()
            N = np.ascontiguousarray(N)
            del V, R
            nres = np.abs(Ar @ N).max() if N.shape[1] else 0.0
            if verbose:
                print(f"  [uf] dense eigh: nullity {k0}, gap [{w[k0-1] if k0 else 0:.1e}, {w[k0]:.1e}], max |Ar N| = {nres:.2e}", flush=True)
            if nres > 1e-8:
                raise ValueError(f"null-space basis inaccurate: max |Ar N| = {nres:.2e}")
        else:
            # large case: only the (near-)null eigenvectors of A^T A (MRRR subset), particular solution by LSQR
            import scipy.linalg as sla
            import scipy.sparse.linalg as spla
            _check(8 * nr * nr * 1.6, "reduced nullspace (subset)")
            AtA_s = (Ar.T @ Ar).tocsr()
            wmax = max(float(np.abs(AtA_s).sum(axis=1).max()), 1.0)   # Gershgorin bound
            AtA = AtA_s.toarray(); del AtA_s
            w, N = sla.eigh(AtA, subset_by_value=(-np.inf, tol * wmax), driver='evr', overwrite_a=True,
                            check_finite=False)
            del AtA
            nres = np.abs(Ar @ N).max() if N.shape[1] else 0.0
            if verbose:
                print(f"  [uf] subset eigh: {N.shape[1]} vectors below {tol*wmax:.2e}; max |Ar N| = {nres:.2e}", flush=True)
            if nres > 1e-8:
                raise ValueError(f"null-space basis inaccurate: max |Ar N| = {nres:.2e}")
            sol = spla.lsqr(Ar, br, atol=1e-15, btol=1e-15, iter_lim=100000)
            y0 = sol[0]
            y0 = y0 - N @ (N.T @ y0)
            res = np.abs(Ar @ y0 - br).max()
            N = np.ascontiguousarray(N)
    else:
        N = np.eye(nr); y0 = np.zeros(nr); res = 0.0
    # expansion x = x_one + P y
    x_one = np.zeros(n)
    Pr, Pc, Pv = [], [], []
    for i in range(n):
        r, f = uf.find(i)
        if r == n:
            x_one[i] = f
        elif f != 0:
            Pr.append(i); Pc.append(ridx[r]); Pv.append(f)
    P = sp.csr_matrix((Pv, (Pr, Pc)), shape=(n, nr))
    x0 = x_one + P @ y0
    if factored:
        if verbose:
            print(f"  [uf] reduced rank {nr - N.shape[1]}, nullity {N.shape[1]}, residual {res:.1e} (factored)", flush=True)
        return x0, (P, N), res, nr - N.shape[1]
    _check(8 * n * N.shape[1], "expanded nullspace basis")
    Bm = P @ N
    if verbose:
        print(f"  [uf] reduced rank {nr - N.shape[1]}, nullity {N.shape[1]}, residual {res:.1e}", flush=True)
    return x0, Bm, res, nr - N.shape[1]


def svec_matrix(n, terms, F0, nvar, order):
    """returns S (svec_len x nvar sparse) and f0 (svec_len) with svec(F0 + sum z_j F_j) = f0 + S z."""
    if order == "clarabel":
        idx = [(i, j) for j in range(n) for i in range(j + 1)]
    else:
        idx = [(i, j) for j in range(n) for i in range(j, n)]
    pos = {p: t for t, p in enumerate(idx)}
    rr, cc, vv = [], [], []
    for (var, F) in terms:
        F = sp.coo_matrix(F)
        for a, b_, x in zip(F.row, F.col, F.data):
            key = (a, b_) if (order == "clarabel" and a <= b_) or (order != "clarabel" and a >= b_) else None
            if key is None:
                continue
            sc = 1.0 if a == b_ else np.sqrt(2)
            rr.append(pos[key]); cc.append(var); vv.append(x * sc)
    S = sp.csr_matrix((vv, (rr, cc)), shape=(len(idx), nvar))
    f0 = np.zeros(len(idx))
    F0 = sp.coo_matrix(F0)
    for a, b_, x in zip(F0.row, F0.col, F0.data):
        key = (a, b_) if (order == "clarabel" and a <= b_) or (order != "clarabel" and a >= b_) else None
        if key is None:
            continue
        f0[pos[key]] += x * (1.0 if a == b_ else np.sqrt(2))
    return S, f0


def solve_reduced(nvar, eq_rows, psd, qmin, solver="clarabel", eps=1e-9, max_iter=500, verbose=False,
                  scs_iters=400000, ineqs=None, verbose_uf=False):
    """minimise qmin . z  s.t. eq_rows, psd cones (n, terms, F0), ineqs [(coef dict, const)]: const+coef.z>=0.
    Returns dict with value (of qmin.z), z, per-cone dual matrices, status."""
    t0 = time.time()
    z0, N, eqres, rank = nullspace_uf(eq_rows, nvar, verbose=verbose_uf)
    k = N.shape[1]
    q = np.zeros(nvar)
    for i, x in qmin.items():
        q[i] += x
    order = "clarabel" if solver == "clarabel" else "scs"
    blocksA, blocksb, sizes = [], [], []
    total = 0
    for (n, terms, F0) in psd:
        S, f0 = svec_matrix(n, terms, F0, nvar, order)
        total += S.shape[0] * k
        _check(8 * total, "reduced PSD data")
        blocksA.append(S @ N)          # dense svec_len x k
        blocksb.append(f0 + S @ z0)
        sizes.append(n)
    # conic form: s = b - A theta ; s_psd = f0 + S z0 + S N theta  -> A = -S N
    Apsd = -np.vstack(blocksA)
    bpsd = np.concatenate(blocksb)
    Alist, blist = [], []
    n_nn = 0
    if ineqs:
        G = np.zeros((len(ineqs), nvar)); h = np.zeros(len(ineqs))
        for i, (coef, const) in enumerate(ineqs):
            for v, x in coef.items():
                G[i, v] += x
            h[i] = const
        Alist.append(-(G @ N)); blist.append(h + G @ z0)
        n_nn = len(ineqs)
    Alist.append(Apsd); blist.append(bpsd)
    Afull = np.vstack(Alist)
    c = N.T @ q
    const = q @ z0
    # prune directions of theta that affect no cone (lineality space)
    Ured, sv, Vt = np.linalg.svd(Afull, full_matrices=False)
    keep = sv > 1e-10 * max(sv.max(), 1.0)
    Vr = Vt[keep].T                     # k x k'
    c_ker = c - Vr @ (Vr.T @ c)
    if np.abs(c_ker).max() > 1e-8:
        raise ValueError(f"objective has a component {np.abs(c_ker).max():.2e} along directions not constrained by any cone (unbounded)")
    A = sp.csc_matrix(Afull @ Vr)
    b = np.concatenate(blist)
    c = Vr.T @ c
    N = N @ Vr
    k = N.shape[1]
    if solver == "clarabel":
        import clarabel
        cones = []
        if n_nn: cones.append(clarabel.NonnegativeConeT(n_nn))
        cones += [clarabel.PSDTriangleConeT(n) for n in sizes]
        st = clarabel.DefaultSettings()
        st.verbose = verbose; st.max_iter = max_iter
        st.tol_gap_abs = eps; st.tol_gap_rel = eps; st.tol_feas = eps
        st.direct_solve_method = "faer"; st.chordal_decomposition_enable = False; st.max_threads = 8
        s = clarabel.DefaultSolver(sp.csc_matrix((k, k)), c, A, b, cones, st)
        sol = s.solve()
        theta = np.array(sol.x); y = np.array(sol.z); status = str(sol.status)
        pobj = sol.obj_val + const
        dobj = (sol.obj_val_dual + const) if hasattr(sol, 'obj_val_dual') else np.nan
    else:
        import scs
        data = dict(A=A, b=b, c=c)
        cone = dict(l=n_nn, s=sizes)
        s = scs.SCS(data, cone, eps_abs=eps, eps_rel=eps, max_iters=scs_iters, verbose=verbose,
                    acceleration_lookback=10)
        sol = s.solve()
        theta = sol['x']; y = sol['y']; status = sol['info']['status']
        pobj = sol['info']['pobj'] + const; dobj = sol['info']['dobj'] + const
    z = z0 + N @ theta
    # unpack dual matrices per PSD cone
    duals = []
    pos = n_nn
    for n in sizes:
        m = n * (n + 1) // 2
        yv = y[pos:pos + m]
        if order == "clarabel":
            idx = [(i, j) for j in range(n) for i in range(j + 1)]
        else:
            idx = [(i, j) for j in range(n) for i in range(j, n)]
        Y = np.zeros((n, n))
        for t, (i, j) in enumerate(idx):
            if i == j:
                Y[i, i] = yv[t]
            else:
                Y[i, j] = Y[j, i] = yv[t] / np.sqrt(2)
        duals.append(Y)
        pos += m
    return dict(status=status, pobj=pobj, dobj=dobj, z=z, theta=theta, duals=duals, time=time.time() - t0,
                rank=rank, nullity=k, eqres=eqres, ineq_dual=y[:n_nn] if n_nn else None, mem=mem_gb())
