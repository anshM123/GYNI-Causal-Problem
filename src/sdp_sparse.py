"""Minimal sparse conic SDP builder -> Clarabel / SCS directly (no cvxpy; low memory).

Problem form (maximisation is handled by negating):
    minimise  q^T z
    s.t.      A_eq z = b_eq
              sum_j z_j F^k_j + F^k_0  PSD      for each PSD block k   (F symmetric, real)
              z_i >= 0  (optional nonneg list)
Hermitian blocks are passed through their real embedding.
"""
import numpy as np
import scipy.sparse as sp
import time
import os


def mem_gb():
    from memguard import mem_gb as _m; return _m()


class SDP:
    def __init__(self):
        self.nvar = 0
        self.eq_rows = []   # list of (dict var->coef, rhs)
        self.psd = []       # list of (n, list of (var index or -1, sparse sym matrix))
        self.nonneg = []    # list of (dict, rhs) meaning  rhs - coef.z >= 0  ... we store expr >= 0 as (coef, const)
        self.q = None

    def add_vars(self, n):
        i0 = self.nvar
        self.nvar += n
        return np.arange(i0, i0 + n)

    def add_eq(self, coef, rhs):
        """coef: dict {var: value} ; constraint sum coef*z = rhs"""
        self.eq_rows.append((coef, rhs))

    def add_ineq(self, coef, const):
        """constraint  const + sum coef*z >= 0"""
        self.nonneg.append((coef, const))

    def add_psd(self, n, terms, F0):
        """PSD constraint  F0 + sum_j z_{v_j} F_j  >= 0 ; terms: list of (var, sparse n x n symmetric)."""
        self.psd.append((n, terms, sp.csr_matrix(F0)))

    def set_objective_min(self, qdict):
        q = np.zeros(self.nvar)
        for k, v in qdict.items():
            q[k] += v
        self.q = q

    # ---------- svec helpers ----------
    @staticmethod
    def _svec_index(n, order):
        """returns (rows, cols, scale) arrays of the triangular entries in solver order."""
        r, c, s = [], [], []
        if order == "clarabel":  # upper triangle, column-major
            for j in range(n):
                for i in range(j + 1):
                    r.append(i); c.append(j); s.append(1.0 if i == j else np.sqrt(2))
        else:  # scs: lower triangle column-major
            for j in range(n):
                for i in range(j, n):
                    r.append(i); c.append(j); s.append(1.0 if i == j else np.sqrt(2))
        return np.array(r), np.array(c), np.array(s)

    def _svec_sparse(self, M, n, order, pos_cache):
        M = sp.coo_matrix(M)
        # keep triangle entries
        if order == "clarabel":
            mask = M.row <= M.col
        else:
            mask = M.row >= M.col
        rr, cc, vv = M.row[mask], M.col[mask], M.data[mask]
        idx = pos_cache[rr, cc]
        scale = np.where(rr == cc, 1.0, np.sqrt(2))
        return idx, vv * scale

    def build(self, order="clarabel"):
        nv = self.nvar
        # equality block
        Ar, Ac, Av, b = [], [], [], []
        row = 0
        for coef, rhs in self.eq_rows:
            for k, v in coef.items():
                if v != 0:
                    Ar.append(row); Ac.append(k); Av.append(v)
            b.append(rhs); row += 1
        n_eq = row
        # nonneg block:  s = const + coef z >= 0  ->  -coef z + s = const
        for coef, const in self.nonneg:
            for k, v in coef.items():
                if v != 0:
                    Ar.append(row); Ac.append(k); Av.append(-v)
            b.append(const); row += 1
        n_nn = len(self.nonneg)
        cones_psd = []
        for (n, terms, F0) in self.psd:
            pos = -np.ones((n, n), dtype=np.int64)
            r, c, s = self._svec_index(n, order)
            pos[r, c] = np.arange(len(r))
            m = len(r)
            for (var, F) in terms:
                idx, vals = self._svec_sparse(F, n, order, pos)
                Ar.extend(row + idx); Ac.extend([var] * len(idx)); Av.extend(-vals)
            bb = np.zeros(m)
            idx, vals = self._svec_sparse(F0, n, order, pos)
            np.add.at(bb, idx, vals)
            b.extend(bb); row += m
            cones_psd.append(n)
        A = sp.csc_matrix((np.array(Av, float), (np.array(Ar), np.array(Ac))), shape=(row, nv))
        A.sum_duplicates()
        return A, np.array(b, float), n_eq, n_nn, cones_psd

    def solve(self, solver="clarabel", verbose=False, eps=1e-8, max_iter=200, scs_iters=200000, settings=None):
        t0 = time.time()
        if solver == "clarabel":
            import clarabel
            A, b, n_eq, n_nn, cps = self.build("clarabel")
            P = sp.csc_matrix((self.nvar, self.nvar))
            cones = []
            if n_eq: cones.append(clarabel.ZeroConeT(n_eq))
            if n_nn: cones.append(clarabel.NonnegativeConeT(n_nn))
            for n in cps: cones.append(clarabel.PSDTriangleConeT(n))
            st = clarabel.DefaultSettings()
            st.verbose = verbose
            st.tol_gap_abs = eps; st.tol_gap_rel = eps; st.tol_feas = eps
            st.max_iter = max_iter
            st.max_threads = 8
            for k_, v_ in (settings or {}).items():
                setattr(st, k_, v_)
            s = clarabel.DefaultSolver(P, self.q, A, b, cones, st)
            sol = s.solve()
            res = dict(status=str(sol.status), primal=sol.obj_val, dual=getattr(sol, 'obj_val_dual', None),
                       z=np.array(sol.x), y=np.array(sol.z), s=np.array(sol.s), time=time.time() - t0,
                       A=A, b=b, n_eq=n_eq, n_nn=n_nn, cones=cps)
        else:
            import scs
            A, b, n_eq, n_nn, cps = self.build("scs")
            data = dict(A=A, b=b, c=self.q)
            cone = dict(z=n_eq, l=n_nn, s=cps)
            s = scs.SCS(data, cone, eps_abs=eps, eps_rel=eps, max_iters=scs_iters, verbose=verbose, **(settings or {}))
            sol = s.solve()
            res = dict(status=sol['info']['status'], primal=sol['info']['pobj'], dual=sol['info']['dobj'],
                       z=sol['x'], y=sol['y'], s=sol['s'], time=time.time() - t0,
                       A=A, b=b, n_eq=n_eq, n_nn=n_nn, cones=cps)
        res['mem_gb'] = mem_gb()
        return res
