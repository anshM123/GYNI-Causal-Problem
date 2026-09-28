"""Small dense primal-dual interior-point method (HKM direction, Mehrotra predictor-corrector) for SDPs in LMI form:
    maximise c^T y   s.t.   S(y) = F0 + sum_i y_i F_i  >= 0      (block diagonal, real symmetric)
with dual   minimise -<F0, X> ... ;  here we use the standard pair
    (D) max b^T y  s.t.  C - sum_i y_i A_i = S >= 0,      (P) min <C, X>  s.t.  <A_i, X> = b_i, X >= 0
with C = F0, A_i = -F_i, b = c.  The Schur complement costs O(k^2 n^2 + k n^3) per iteration (no svec Hessians),
which is what makes high hierarchy levels affordable.  Returns y, X (the certificate matrix), S, objective values."""
import numpy as np
import time


def _chol_inv(M):
    L = np.linalg.cholesky(M)
    Li = np.linalg.inv(L)
    return Li.T @ Li, L


def _pd_fix(M, floor=1e-15):
    """symmetrise; if not numerically positive definite, clip eigenvalues (robustness guard)."""
    M = (M + M.T) / 2
    try:
        np.linalg.cholesky(M)
        return M
    except np.linalg.LinAlgError:
        w, V = np.linalg.eigh(M)
        w = np.maximum(w, floor * max(1.0, np.abs(w).max()))
        return (V * w) @ V.T


def _max_step(M, D):
    """largest alpha in (0,1] with M + alpha D >= 0 (M > 0)."""
    try:
        L = np.linalg.cholesky(M)
    except np.linalg.LinAlgError:
        L = np.linalg.cholesky(_pd_fix(M))
    Li = np.linalg.inv(L)
    T = Li @ D @ Li.T
    ev = np.linalg.eigvalsh((T + T.T) / 2).min()
    if ev >= 0:
        return 1.0
    return min(1.0, -1.0 / ev)


def solve_lmi(C, A, b, maxit=100, tol=1e-9, verbose=True, max_step_frac=0.95):
    """C: list of (n_b, n_b) arrays; A: list of (k, n_b, n_b) arrays (A[blk][i] = A_i block); b: (k,)"""
    nb = len(C)
    k = len(b)
    ntot = sum(c.shape[0] for c in C)
    X = [np.eye(c.shape[0]) for c in C]
    S = [np.eye(c.shape[0]) for c in C]
    y = np.zeros(k)
    normC = max(np.abs(c).max() for c in C) + 1.0
    normb = np.abs(b).max() + 1.0
    t0 = time.time()

    def Aop(Xs):
        return sum(np.einsum('kij,ij->k', A[j], Xs[j]) for j in range(nb))

    def Aadj(v):
        return [np.einsum('k,kij->ij', v, A[j]) for j in range(nb)]

    for it in range(maxit):
        AX = Aop(X)
        rp = b - AX
        Rd = [C[j] - S[j] - Aadj(y)[j] for j in range(nb)] if it == 0 else [C[j] - S[j] - Ay[j] for j in range(nb)]
        mu = sum(np.sum(X[j] * S[j]) for j in range(nb)) / ntot
        pobj = sum(np.sum(C[j] * X[j]) for j in range(nb))
        dobj = b @ y
        pinf = np.abs(rp).max() / normb
        dinf = max(np.abs(r).max() for r in Rd) / normC
        gap = abs(pobj - dobj) / (1 + abs(pobj) + abs(dobj))
        if verbose:
            print(f"   it {it:3d} pobj {pobj: .10f} dobj {dobj: .10f} gap {gap:.1e} pinf {pinf:.1e} dinf {dinf:.1e} mu {mu:.1e} ({time.time()-t0:.0f}s)", flush=True)
        if gap < tol and pinf < tol and dinf < tol:
            break
        Sinv = [np.linalg.inv(S[j]) for j in range(nb)]
        Sinv = [(s + s.T) / 2 for s in Sinv]
        # Schur complement M_ij = <A_i, X A_j S^{-1}>
        M = np.zeros((k, k))
        G = []
        for j in range(nb):
            Gj = np.matmul(np.matmul(X[j][None, :, :], A[j]), Sinv[j][None, :, :])  # (k,n,n)
            G.append(Gj)
            M += A[j].reshape(k, -1) @ Gj.reshape(k, -1).T
        M = (M + M.T) / 2
        try:
            Lm = np.linalg.cholesky(M)
        except np.linalg.LinAlgError:
            M += 1e-12 * np.eye(k) * np.abs(np.diag(M)).max()
            Lm = np.linalg.cholesky(M)

        def solve_M(r):
            return np.linalg.solve(Lm.T, np.linalg.solve(Lm, r))

        def direction(sigma_mu, corr=None):
            # rhs: M dy = rp - A(sigma mu S^-1) + A(X) + A(X Rd S^-1) [+ corrector: + A(dXa dSa S^-1)]
            T = []
            for j in range(nb):
                Tj = sigma_mu * Sinv[j] - X[j] - X[j] @ Rd[j] @ Sinv[j]
                if corr is not None:
                    Tj = Tj - corr[0][j] @ corr[1][j] @ Sinv[j]
                T.append(Tj)
            r = rp - Aop(T)
            dy = solve_M(r)
            Ady = Aadj(dy)
            dS = [Rd[j] - Ady[j] for j in range(nb)]
            dX = []
            for j in range(nb):
                d = sigma_mu * Sinv[j] - X[j] - X[j] @ dS[j] @ Sinv[j]
                if corr is not None:
                    d = d - corr[0][j] @ corr[1][j] @ Sinv[j]
                dX.append((d + d.T) / 2)
            return dy, dX, dS, Ady

        # predictor
        dy, dX, dS, _ = direction(0.0)
        ap = min(_max_step(X[j], dX[j]) for j in range(nb))
        ad = min(_max_step(S[j], dS[j]) for j in range(nb))
        mu_aff = sum(np.sum((X[j] + ap * dX[j]) * (S[j] + ad * dS[j])) for j in range(nb)) / ntot
        sigma = min(1.0, (mu_aff / mu) ** 3)
        # corrector
        dy, dX, dS, Ady = direction(sigma * mu, corr=(dX, dS))
        ap = min(1.0, max_step_frac * min(_max_step(X[j], dX[j]) for j in range(nb)))
        ad = min(1.0, max_step_frac * min(_max_step(S[j], dS[j]) for j in range(nb)))
        X = [X[j] + ap * dX[j] for j in range(nb)]
        S = [S[j] + ad * dS[j] for j in range(nb)]
        y = y + ad * dy
        Ay = Aadj(y)
        X = [_pd_fix(x) for x in X]; S = [_pd_fix(s) for s in S]
    return dict(y=y, X=X, S=S, pobj=pobj, dobj=dobj, gap=gap, pinf=pinf, dinf=dinf, it=it, time=time.time() - t0)
