"""Primal-dual IPM (HKM direction, Mehrotra predictor-corrector) for LMIs with SPARSE constraint matrices:
    (D) max b.y  s.t.  S = C - sum_i y_i A_i >= 0 (block diagonal)      (P) min <C,X>  s.t. <A_i, X> = b_i, X >= 0.
Per block the A_i are stored as one sparse matrix Asp (k x n^2, rows = vec(A_i)).  Schur complement
M_ij = <A_i, X A_j S^-1> is formed as Asp @ T with T = [vec(X A_j S^-1)]_j, computed using only the non-zero rows
of A_j (cost ~ k * n^2 * r instead of k * n^3)."""
import numpy as np
import scipy.sparse as sp
import time
from ipm import _pd_fix, _max_step


def solve_lmi_sparse(C, Asp, b, maxit=100, tol=1e-9, verbose=True, max_step_frac=0.95, pinf_tol=1e-6):
    """stopping: gap < tol, dinf < tol and pinf < pinf_tol (the y/S side, which defines W, stays exactly
    feasible (S > 0); the X side only certifies near-optimality)."""
    nb = len(C)
    k = len(b)
    ns = [c.shape[0] for c in C]
    ntot = sum(ns)
    AspT = [A.T.tocsr() for A in Asp]
    # stacked sparse (k*n x n) matrices: rows i*n..(i+1)*n-1 hold A_i (block j)
    Abig = []
    for j in range(nb):
        n = ns[j]
        Aj = Asp[j].tocoo()
        rr = Aj.row * n + Aj.col // n
        cc = Aj.col % n
        Abig.append(sp.csr_matrix((Aj.data, (rr, cc)), shape=(k * n, n)))
    X = [np.eye(n) for n in ns]
    S = [np.eye(n) for n in ns]
    y = np.zeros(k)
    normC = max(np.abs(c).max() for c in C) + 1.0
    normb = np.abs(b).max() + 1.0
    t0 = time.time()

    def Aop(Xs):
        return sum(Asp[j] @ Xs[j].reshape(-1) for j in range(nb))

    def Aadj(v):
        return [(AspT[j] @ v).reshape(ns[j], ns[j]) for j in range(nb)]

    Ay = Aadj(y)
    for it in range(maxit):
        rp = b - Aop(X)
        Rd = [C[j] - S[j] - Ay[j] for j in range(nb)]
        mu = sum(np.sum(X[j] * S[j]) for j in range(nb)) / ntot
        pobj = sum(np.sum(C[j] * X[j]) for j in range(nb))
        dobj = b @ y
        pinf = np.abs(rp).max() / normb
        dinf = max(np.abs(r).max() for r in Rd) / normC
        gap = abs(pobj - dobj) / (1 + abs(pobj) + abs(dobj))
        if verbose:
            print(f"   it {it:3d} pobj {pobj: .10f} dobj {dobj: .10f} gap {gap:.1e} pinf {pinf:.1e} dinf {dinf:.1e} mu {mu:.1e} ({time.time()-t0:.0f}s)", flush=True)
        if gap < tol and pinf < pinf_tol and dinf < tol:
            break
        # dual (W-side) stagnation: y is feasible (S > 0) and b.y has converged -> stop (X side may stall)
        hist_d = locals().setdefault('hist_d', [])
        hist_d.append(dobj)
        if mu < 1e-12 and dinf < tol and len(hist_d) >= 4 and max(hist_d[-4:]) - min(hist_d[-4:]) < 1e-11:
            break
        Sinv = [np.linalg.inv(S[j]) for j in range(nb)]
        Sinv = [(s + s.T) / 2 for s in Sinv]
        M = np.zeros((k, k))
        for j in range(nb):
            n = ns[j]
            Z = (Abig[j] @ Sinv[j]).reshape(k, n, n)          # A_i S^-1
            T = np.matmul(X[j][None, :, :], Z)                  # X A_i S^-1
            del Z
            M += Asp[j] @ T.reshape(k, n * n).T
            del T
        M = (M + M.T) / 2
        try:
            Lm = np.linalg.cholesky(M)
        except np.linalg.LinAlgError:
            M += 1e-12 * np.eye(k) * np.abs(np.diag(M)).max()
            Lm = np.linalg.cholesky(M)

        def solve_M(r):
            return np.linalg.solve(Lm.T, np.linalg.solve(Lm, r))

        def direction(sigma_mu, corr=None):
            Tl = []
            for j in range(nb):
                Tj = sigma_mu * Sinv[j] - X[j] - X[j] @ Rd[j] @ Sinv[j]
                if corr is not None:
                    Tj = Tj - corr[0][j] @ corr[1][j] @ Sinv[j]
                Tl.append(Tj)
            r = rp - Aop(Tl)
            dy = solve_M(r)
            Ady = Aadj(dy)
            dS = [Rd[j] - Ady[j] for j in range(nb)]
            dX = []
            for j in range(nb):
                d = sigma_mu * Sinv[j] - X[j] - X[j] @ dS[j] @ Sinv[j]
                if corr is not None:
                    d = d - corr[0][j] @ corr[1][j] @ Sinv[j]
                dX.append((d + d.T) / 2)
            return dy, dX, dS

        dy, dX, dS = direction(0.0)
        ap = min(_max_step(X[j], dX[j]) for j in range(nb))
        ad = min(_max_step(S[j], dS[j]) for j in range(nb))
        mu_aff = sum(np.sum((X[j] + ap * dX[j]) * (S[j] + ad * dS[j])) for j in range(nb)) / ntot
        sigma = min(1.0, (mu_aff / mu) ** 3)
        dy, dX, dS = direction(sigma * mu, corr=(dX, dS))
        ap = min(1.0, max_step_frac * min(_max_step(X[j], dX[j]) for j in range(nb)))
        ad = min(1.0, max_step_frac * min(_max_step(S[j], dS[j]) for j in range(nb)))
        X = [_pd_fix(X[j] + ap * dX[j]) for j in range(nb)]
        S = [_pd_fix(S[j] + ad * dS[j]) for j in range(nb)]
        y = y + ad * dy
        Ay = Aadj(y)
    return dict(y=y, X=X, S=S, pobj=pobj, dobj=dobj, gap=gap, pinf=pinf, dinf=dinf, it=it, time=time.time() - t0)
