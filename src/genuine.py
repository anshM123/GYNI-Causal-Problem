"""Genuine strategies -> moment variables z for the mc2 BlockMoment; residual checks."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import mc2
from pm_core import trace_replace, is_valid_process


def LV(W, dims):
    tr = lambda X, S: trace_replace(X, dims, S)
    AI, AO, BI, BO = 0, 1, 2, 3
    return (tr(W, [AO]) + tr(W, [BO]) - tr(W, [AO, BO]) - tr(W, [BI, BO]) + tr(W, [AO, BI, BO])
            - tr(W, [AI, AO]) + tr(W, [AI, AO, BO]))


def random_valid(dims, rng, frac=0.95):
    D = int(np.prod(dims))
    X = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))
    X = X + X.conj().T
    Y = LV(X, dims)
    Y = Y - np.trace(Y) / D * np.eye(D)
    W0 = np.eye(D) * dims[1] * dims[3] / D
    ev = np.linalg.eigvalsh(Y).min()
    return W0 + frac * (dims[1] * dims[3] / D) / abs(ev) * Y


def random_proj(d, rank, rng):
    Z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    Q, _ = np.linalg.qr(Z)
    V = Q[:, :rank]
    return V @ V.conj().T


def word_op(w, Ps):
    d = Ps[0].shape[0]
    O = np.eye(d, dtype=complex)
    for c in w:
        O = O @ Ps[c]
    return O


def choi_vec(w, r, Ps, nreg):
    d = Ps[0].shape[0]
    Wop = word_op(w, Ps)
    v = np.zeros(d * d, dtype=complex)
    for i in range(d):
        e = np.zeros(d); e[i] = 1
        v += np.kron(e, Wop @ e)
    reg = np.zeros(nreg); reg[r] = 1
    return np.kron(v, reg)


def z_from_strategy(M, W, PA, PB):
    """W on [H_A, H_A (x) X_A, H_B, H_B (x) X_B] (Lueders form); PA list of nA projectors A_x=P_{0|x}."""
    A, B = M.A, M.B
    vA = [choi_vec(w, r, PA, A.nset) for (w, r) in A.basis]
    vB = [choi_vec(w, r, PB, B.nset) for (w, r) in B.basis]
    z = np.zeros(M.nvar)
    for (rA, rB, nsz, off) in M.blocks:
        ks = A.reg_members[rA]; ls = B.reg_members[rB]
        V = np.array([np.kron(vA[k], vB[l]) for k in ks for l in ls]).T
        G = (V.conj().T @ W @ V).real
        for j in range(nsz):
            for i in range(j + 1):
                z[off + j * (j + 1) // 2 + i] = G[i, j]
    return z


def check_system(system, z, tol=1e-9, verbose=True):
    worst = 0.0
    for row, rhs in system['eqs']:
        r = sum(c * z[v] for v, c in row.items()) - rhs
        worst = max(worst, abs(r))
    mins = []
    for (n, terms, F0) in system['psd']:
        X = F0.toarray().astype(float)
        for v, F in terms:
            X = X + z[v] * F.toarray()
        mins.append(np.linalg.eigvalsh((X + X.T) / 2).min())
    if verbose:
        print(f"  max eq residual {worst:.2e}; min PSD eig over cones {min(mins):.3e}")
    return worst, min(mins)
