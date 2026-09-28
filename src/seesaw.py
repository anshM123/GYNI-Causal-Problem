"""Seesaw lower bounds for GYNI with REAL process matrices and REAL general instruments, local dim d
(A_I = A_O = B_I = B_O = C^d). Sparse Clarabel SDPs. Used (i) to get explicit high-value strategies for
containment tests of the MC relaxation, (ii) as cheap lower bounds."""
import os, sys, time, itertools, argparse, pickle
os.environ.setdefault("OMP_NUM_THREADS", "8"); os.environ.setdefault("MKL_NUM_THREADS", "8")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb
start_watchdog(6.0, period=0.1)
import numpy as np
import scipy.sparse as sp
from sdp_sparse import SDP
from pm_core import allowed

HERE = os.path.dirname(os.path.abspath(__file__))


def real_gm(d):
    """list of (matrix, is_antisym) : real symmetric off-diag, real antisymmetric, diagonal (traceless)."""
    out = []
    for j in range(d):
        for k in range(j + 1, d):
            S = np.zeros((d, d)); S[j, k] = S[k, j] = 1.0
            out.append((S, False))
            A = np.zeros((d, d)); A[j, k] = 1.0; A[k, j] = -1.0
            out.append((A, True))
    for l in range(1, d):
        D = np.zeros((d, d))
        D[:l, :l] = np.eye(l); D[l, l] = -l
        out.append((D / np.sqrt(l * (l + 1) / 2), False))
    return out


class RealProcessBasis:
    def __init__(self, d):
        self.d = d
        self.D = d ** 4
        gm = real_gm(d)
        opts = [[(np.eye(d), False, False)] + [(m, anti, True) for m, anti in gm] for _ in range(4)]
        self.mats = []
        for combo in itertools.product(*opts):
            pat = [c[2] for c in combo]
            if not any(pat):
                continue
            if not allowed(pat):
                continue
            nanti = sum(1 for c in combo if c[1])
            if nanti % 2:
                continue
            M = combo[0][0]
            for c in combo[1:]:
                M = np.kron(M, c[0])
            self.mats.append(sp.csr_matrix(M))
        self.F0 = sp.identity(self.D, format='csr') * (d * d / self.D)

    def W(self, c):
        W = self.F0.toarray()
        for ci, M in zip(c, self.mats):
            W = W + ci * M.toarray()
        return W


def omega(MA, MB, coef):
    """Omega = sum coef[a,b,x,y] MA[x][a] (x) MB[y][b]"""
    O = 0
    for x in range(len(MA)):
        for y in range(len(MB)):
            for a in (0, 1):
                for b in (0, 1):
                    if coef[a, b, x, y] != 0:
                        O = O + coef[a, b, x, y] * np.kron(MA[x][a], MB[y][b])
    return O


def w_step(basis, Om):
    sdp = SDP()
    idx = sdp.add_vars(len(basis.mats))
    sdp.add_psd(basis.D, list(zip(idx, basis.mats)), basis.F0)
    q = {int(i): -float(M.multiply(Om.T).sum()) for i, M in zip(idx, basis.mats)}
    sdp.set_objective_min(q)
    res = sdp.solve("clarabel", eps=1e-9, max_iter=200, settings=dict(direct_solve_method="faer"))
    const = float(np.trace(basis.F0.toarray() @ Om))
    return basis.W(res['z']), const - res['primal'], res['status']


def inst_step(R, d):
    """maximise sum_{a,x} Tr[M_{a|x} R[x][a]] over real instruments (M on A_I (x) A_O, dims d*d)."""
    n = d * d
    sdp = SDP()
    iu = np.triu_indices(n)
    nx = len(R)
    var = {}
    for x in range(nx):
        for a in (0, 1):
            idx = sdp.add_vars(len(iu[0]))
            var[(x, a)] = idx
            terms = []
            for t, (i, j) in enumerate(zip(*iu)):
                if i == j:
                    E = sp.csr_matrix(([1.0], ([i], [i])), shape=(n, n))
                else:
                    E = sp.csr_matrix(([1.0, 1.0], ([i, j], [j, i])), shape=(n, n))
                terms.append((idx[t], E))
            sdp.add_psd(n, terms, sp.csr_matrix((n, n)))
        # Tr_{AO} (M0 + M1) = 1_{AI}: entry (i,i') of AI: sum_o M[(i,o),(i',o)]
        for i in range(d):
            for ip in range(i, d):
                row = {}
                for a in (0, 1):
                    for o in range(d):
                        r_, c_ = i * d + o, ip * d + o
                        rr, cc = min(r_, c_), max(r_, c_)
                        t = np.where((iu[0] == rr) & (iu[1] == cc))[0][0]
                        row[int(var[(x, a)][t])] = row.get(int(var[(x, a)][t]), 0.0) + 1.0
                sdp.add_eq(row, 1.0 if i == ip else 0.0)
    q = {}
    for x in range(nx):
        for a in (0, 1):
            for t, (i, j) in enumerate(zip(*iu)):
                val = R[x][a][i, j] if i == j else R[x][a][i, j] + R[x][a][j, i]
                q[int(var[(x, a)][t])] = -float(val)
    sdp.set_objective_min(q)
    res = sdp.solve("clarabel", eps=1e-9, max_iter=200)
    M = []
    for x in range(nx):
        Mx = []
        for a in (0, 1):
            z = res['z'][var[(x, a)]]
            X = np.zeros((n, n))
            X[iu] = z; X = X + X.T - np.diag(np.diag(X))
            Mx.append(X)
        M.append(Mx)
    return M, -res['primal']


def reduced_for_alice(W, MB, coef, d):
    n = d * d
    W4 = W.reshape(n, n, n, n)
    R = [[np.zeros((n, n)) for a in (0, 1)] for x in (0, 1)]
    for x in (0, 1):
        for a in (0, 1):
            N = 0
            for y in (0, 1):
                for b in (0, 1):
                    if coef[a, b, x, y] != 0:
                        N = N + coef[a, b, x, y] * MB[y][b]
            if isinstance(N, int):
                continue
            # Tr_B[W (1 (x) N)] -> R[i,j] = sum_{b,c} W[i,b,j,c] N[c,b]
            R[x][a] = np.einsum('ibjc,cb->ij', W4, N)
    return R


def reduced_for_bob(W, MA, coef, d):
    n = d * d
    W4 = W.reshape(n, n, n, n)
    R = [[np.zeros((n, n)) for b in (0, 1)] for y in (0, 1)]
    for y in (0, 1):
        for b in (0, 1):
            Mx = 0
            for x in (0, 1):
                for a in (0, 1):
                    if coef[a, b, x, y] != 0:
                        Mx = Mx + coef[a, b, x, y] * MA[x][a]
            if isinstance(Mx, int):
                continue
            R[y][b] = np.einsum('aibj,ba->ij', W4, Mx)
    return R


def random_real_instrument(d, rng):
    import strategies as S
    return [C.real for C in S.random_instrument(d, d, rng, nkraus=2, real=True)]


def gyni_coef():
    c = np.zeros((2, 2, 2, 2))
    for x in (0, 1):
        for y in (0, 1):
            c[y, x, x, y] = 0.25
    return c


def seesaw(d, seed, iters=60, tol=1e-8, verbose=False, basis=None):
    rng = np.random.default_rng(seed)
    coef = gyni_coef()
    basis = basis or RealProcessBasis(d)
    MA = [random_real_instrument(d, rng) for _ in range(2)]
    MB = [random_real_instrument(d, rng) for _ in range(2)]
    last = -1
    for it in range(iters):
        W, v, st = w_step(basis, omega(MA, MB, coef))
        MA, v = inst_step(reduced_for_alice(W, MB, coef, d), d)
        MB, v = inst_step(reduced_for_bob(W, MA, coef, d), d)
        if verbose:
            print(f"  it {it} value {v:.8f}", flush=True)
        if v - last < tol:
            break
        last = v
    return v, W, MA, MB


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, default=2)
    ap.add_argument("--starts", type=int, default=5)
    ap.add_argument("--iters", type=int, default=60)
    ap.add_argument("--seed0", type=int, default=0)
    a = ap.parse_args()
    basis = RealProcessBasis(a.d)
    print(f"d={a.d}: {len(basis.mats)} real valid basis elements", flush=True)
    best = None
    for s in range(a.seed0, a.seed0 + a.starts):
        t = time.time()
        v, W, MA, MB = seesaw(a.d, s, a.iters, basis=basis)
        print(f"seed {s}: GYNI {v:.8f}  ({time.time()-t:.1f}s)", flush=True)
        if best is None or v > best[0]:
            best = (v, W, MA, MB, s)
    with open(os.path.join(HERE, f"seesaw_d{a.d}.pkl"), "wb") as f:
        pickle.dump(dict(value=best[0], W=best[1], MA=best[2], MB=best[3], seed=best[4]), f)
    print(f"best d={a.d}: {best[0]:.8f} (seed {best[4]}), peak mem {peak_gb():.2f} GB")
