"""Level-L symmetric hierarchy solved with the custom Schur-complement IPM (ipm.py)."""
import os, sys, time, argparse, pickle
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb, mem_gb
start_watchdog(6.5, period=0.1)
import numpy as np
import scipy.sparse as sp
import mc3
from nssolve import nullspace_uf, _check
from ipm import solve_lmi

HERE = os.path.dirname(os.path.abspath(__file__))


def build_reduced(L, verbose=True):
    t0 = time.time()
    M, rows, obj = mc3.build(L, sym=True, verbose=verbose)
    psd, (Qp, Qm) = mc3.psd_block00_split(M)
    x0, (P, N), res, rank = nullspace_uf(rows, M.nvar, verbose=verbose, factored=True, consume=True,
                                         components=True)
    k = N.shape[1]
    if verbose:
        print(f"  null space ready: k = {k}, mem {mem_gb():.2f} GB ({time.time()-t0:.1f}s)", flush=True)
    o = np.zeros(M.nvar)
    for v, c in obj.items():
        o[v] += c
    C, Amats = [], []
    for (n, terms, F0) in psd:
        rr, cc, vv = [], [], []
        for (v, F) in terms:
            Fc = sp.coo_matrix(F)
            rr.extend((Fc.row * n + Fc.col).tolist()); cc.extend([v] * Fc.nnz); vv.extend(Fc.data.tolist())
        T = sp.csr_matrix((vv, (rr, cc)), shape=(n * n, M.nvar))
        _check(8 * n * n * k, "block A matrix")
        Ablk = (T @ P) @ N                 # (n^2, k), never forms the full basis
        if sp.issparse(Ablk):
            Ablk = Ablk.toarray()
        C.append((T @ x0).reshape(n, n))
        Amats.append(Ablk)
    Bm = None
    # prune lineality directions via the k x k Gram matrix (no big SVD)
    Gm = sum(Ab.T @ Ab for Ab in Amats)
    wv, Vv = np.linalg.eigh(Gm)
    keep = wv > 1e-12 * wv.max()
    V = Vv[:, keep]
    c = np.asarray(N.T @ (P.T @ o)).ravel()
    ck = c - V @ (V.T @ c)
    if np.abs(ck).max() > 1e-8:
        raise ValueError("unbounded direction in objective")
    del Gm
    A = []
    for (n, terms, F0), Ablk in zip(psd, Amats):
        Ar = (Ablk @ V).T.reshape(-1, n, n)     # (k', n, n) = F_i
        A.append(-Ar)                            # A_i = -F_i
    b = V.T @ c
    const = o @ x0
    if verbose:
        print(f"  reduced: nullity {k}, kept {V.shape[1]} directions, cones {[a.shape[1] for a in A]}, "
              f"{time.time()-t0:.1f}s, mem {mem_gb():.2f} GB", flush=True)
    return dict(M=M, obj=obj, Qp=Qp, Qm=Qm, x0=x0, P=P, N=N, V=V, C=C, A=A, b=b, const=const)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=int, default=4)
    ap.add_argument("--tol", type=float, default=1e-9)
    ap.add_argument("--maxit", type=int, default=80)
    ap.add_argument("--save", default=None)
    a = ap.parse_args()
    t0 = time.time()
    R = build_reduced(a.L)
    sol = solve_lmi(R['C'], R['A'], R['b'], maxit=a.maxit, tol=a.tol)
    theta = R['V'] @ sol['y']
    z = R['x0'] + R['P'] @ np.asarray(R['N'] @ theta).ravel()
    val = sum(c * z[v] for v, c in R['obj'].items())
    print(f"HIER-IPM L={a.L}: dual(b.y)+const {sol['dobj'] + R['const']:.10f}  primal <C,X>+const {sol['pobj'] + R['const']:.10f} "
          f" obj(z) {val:.10f}  gap {sol['gap']:.1e} pinf {sol['pinf']:.1e} dinf {sol['dinf']:.1e}  it {sol['it']}  "
          f"total {time.time()-t0:.1f}s peak {peak_gb():.2f} GB", flush=True)
    if a.save:
        with open(os.path.join(HERE, a.save), "wb") as f:
            pickle.dump(dict(L=a.L, z=z, duals=sol['X'], value=val, upper=sol['pobj'] + R['const']), f)
