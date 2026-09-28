"""Genuine process-matrix strategies with GENERAL instruments (for testing the WLOG reduction / containment)."""
import numpy as np
from genuine import LV


def kron(*ops):
    out = np.array([[1.0 + 0j]])
    for o in ops:
        out = np.kron(out, o)
    return out


def random_instrument(dI, dO, rng, nkraus=2, real=False):
    """2-outcome instrument: list [Choi_0, Choi_1] on A_I (x) A_O."""
    K = []
    for a in range(2):
        for k in range(nkraus):
            X = rng.normal(size=(dO, dI)) + (0 if real else 1j * rng.normal(size=(dO, dI)))
            K.append((a, X))
    S = sum(X.conj().T @ X for _, X in K)
    w, U = np.linalg.eigh(S)
    Sm = U @ np.diag(w ** -0.5) @ U.conj().T
    K = [(a, X @ Sm) for a, X in K]
    chois = []
    for a in range(2):
        C = np.zeros((dI * dO, dI * dO), dtype=complex)
        for aa, X in K:
            if aa != a:
                continue
            v = np.zeros(dI * dO, dtype=complex)
            for i in range(dI):
                e = np.zeros(dI); e[i] = 1
                v += np.kron(e, X @ e)
            # Choi of rho -> X rho X^+ : sum_ij |i><j| (x) X|i><j|X^+ = |v><v|
            C += np.outer(v, v.conj())
        chois.append(C)
    return chois


def probs(W, MA, MB):
    """MA[x] = [Choi_0, Choi_1]; returns p[a,b,x,y]"""
    nA, nB = len(MA), len(MB)
    p = np.zeros((2, 2, nA, nB))
    for x in range(nA):
        for y in range(nB):
            for a in range(2):
                for b in range(2):
                    p[a, b, x, y] = np.trace(W @ np.kron(MA[x][a], MB[y][b])).real
    return p


def random_valid_boundary(dims, rng, frac=1.0):
    D = int(np.prod(dims))
    X = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))
    X = X + X.conj().T
    Y = LV(X, dims)
    Y = Y - np.trace(Y) / D * np.eye(D)
    W0 = np.eye(D) * dims[1] * dims[3] / D
    ev = np.linalg.eigvalsh(Y).min()
    return W0 + frac * (dims[1] * dims[3] / D) / abs(ev) * Y


def random_unitary(d, rng):
    Z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    Q, R = np.linalg.qr(Z)
    return Q @ np.diag(np.diag(R) / np.abs(np.diag(R)))


def random_channel_choi(dIn, dOut, rng, nk=2):
    K = [rng.normal(size=(dOut, dIn)) + 1j * rng.normal(size=(dOut, dIn)) for _ in range(nk)]
    S = sum(X.conj().T @ X for X in K)
    w, U = np.linalg.eigh(S)
    Sm = U @ np.diag(w ** -0.5) @ U.conj().T
    C = np.zeros((dIn * dOut, dIn * dOut), dtype=complex)
    for X in K:
        X = X @ Sm
        v = np.zeros(dIn * dOut, dtype=complex)
        for i in range(dIn):
            e = np.zeros(dIn); e[i] = 1
            v += np.kron(e, X @ e)
        C += np.outer(v, v.conj())
    return C


def causal_A_before_B(d, rng):
    """W = rho_{AI} (x) Choi(C: AO->BI) (x) 1_{BO}, dims (d,d,d,d); plus random classical mixing done outside."""
    psi = rng.normal(size=d) + 1j * rng.normal(size=d)
    rho = np.outer(psi, psi.conj()); rho /= np.trace(rho)
    C = random_channel_choi(d, d, rng)
    return np.kron(np.kron(rho, C), np.eye(d))


def causal_B_before_A(d, rng):
    """W = Choi(C: BO->AI) placed on AI,BO ; rho on BI ; 1 on AO. Order [AI,AO,BI,BO]."""
    psi = rng.normal(size=d) + 1j * rng.normal(size=d)
    rho = np.outer(psi, psi.conj()); rho /= np.trace(rho)
    C = random_channel_choi(d, d, rng)  # on BO (x) AI
    # build on [BO, AI] then permute to [AI, AO, BI, BO]
    big = np.kron(np.kron(C, np.eye(d)), rho)  # order [BO, AI, AO, BI]
    big = big.reshape([d] * 8)
    perm = [1, 2, 3, 0]
    big = big.transpose(perm + [p + 4 for p in perm])
    return big.reshape(d ** 4, d ** 4)


def ocb_process():
    I = np.eye(2); X = np.array([[0, 1], [1, 0]]); Z = np.diag([1., -1.])
    return 0.25 * (kron(I, I, I, I) + (1 / np.sqrt(2)) * (kron(I, Z, Z, I) + kron(Z, I, X, Z)))


def local_unitary_conj(W, dims, rng):
    Us = [random_unitary(d, rng) for d in dims]
    U = kron(*Us)
    return U @ W @ U.conj().T
