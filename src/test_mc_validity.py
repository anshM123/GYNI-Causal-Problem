"""Validity test of the moment + canonical-image relaxation:
build random genuine strategies (W valid process on H_A (x) (H_A (x) X) (x) ..., projective measurements),
compute Gamma, and check (V2) constraints, canonical-image validity/PSD and that the objective matches."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb
start_watchdog(4.0)
import numpy as np
from mc_relax import Party, Moment, validity_constraints, canonical_image, gyni_objective, Pw, pmul, red
from pm_core import trace_replace, is_valid_process


def LV(W, dims):
    """projector onto valid subspace (Araujo et al. 2015), dims=[dAI,dAO,dBI,dBO]"""
    AI, AO, BI, BO = 0, 1, 2, 3
    tr = lambda X, S: trace_replace(X, dims, S)
    return (tr(W, [AO]) + tr(W, [BO]) - tr(W, [AO, BO]) - tr(W, [BI, BO]) + tr(W, [AO, BI, BO])
            - tr(W, [AI, AO]) + tr(W, [AI, AO, BO]))


def random_valid(dims, rng, eps=None):
    D = int(np.prod(dims))
    X = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D))
    X = X + X.conj().T
    Y = LV(X, dims)
    Y = Y - np.trace(Y) / D * np.eye(D)
    W0 = np.eye(D) * dims[1] * dims[3] / D
    ev = np.linalg.eigvalsh(Y).min()
    t = 0.95 * (dims[1] * dims[3] / D) / abs(ev)
    return W0 + t * Y


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


def choi_vec(w, r, Ps):
    d = Ps[0].shape[0]
    Wop = word_op(w, Ps)
    phi = np.zeros((d, d), dtype=complex)
    # |w> = sum_i |i> (x) W|i>  ; as vector on A_I (x) H_A_out, then (x) |r>
    v = np.zeros(d * d, dtype=complex)
    for i in range(d):
        e = np.zeros(d); e[i] = 1
        v += np.kron(e, Wop @ e)
    reg = np.zeros(2); reg[r] = 1
    return np.kron(v, reg)


def main(seed=0, dA=2, dB=2):
    rng = np.random.default_rng(seed)
    dims = [dA, 2 * dA, dB, 2 * dB]
    W = random_valid(dims, rng)
    print("W valid:", is_valid_process(W, dims)['ok'])
    PA = [random_proj(dA, max(1, dA // 2), rng) for _ in range(2)]
    PB = [random_proj(dB, max(1, dB // 2), rng) for _ in range(2)]
    WORDS = [(), (0,), (1,), (0, 1), (1, 0)]
    A, B = Party(WORDS), Party(WORDS)
    M = Moment(A, B)
    vA = [choi_vec(w, r, PA) for (w, r) in A.basis]
    vB = [choi_vec(w, r, PB) for (w, r) in B.basis]
    V = np.array([np.kron(a, b) for a in vA for b in vB]).T  # columns
    G = V.conj().T @ W @ V
    G = G.real  # real part (imag part is also a valid-compatible object; relaxation uses real Gamma WLOG)
    z = G[M.iu]
    # (V2)
    cons, sizes = validity_constraints(M)
    err = max(abs(sum(c * z[v] for v, c in row.items()) - rhs) for row, rhs in cons)
    print("#V2 constraints", len(cons), "sizes", sizes, " max violation (real part):", err)
    # objective vs direct probability
    obj = gyni_objective(M)
    val = sum(c * z[v] for v, c in obj.items())
    # direct
    def lud(Ps, a, x):
        P = Ps[x] if a == 0 else np.eye(Ps[x].shape[0]) - Ps[x]
        d = P.shape[0]
        v = np.zeros(d * d, dtype=complex)
        for i in range(d):
            e = np.zeros(d); e[i] = 1
            v += np.kron(e, P @ e)
        reg = np.zeros(2); reg[x] = 1
        v = np.kron(v, reg)
        return np.outer(v, v.conj())
    direct = 0
    for x in (0, 1):
        for y in (0, 1):
            direct += 0.25 * np.trace(W @ np.kron(lud(PA, y, x), lud(PB, x, y))).real
    print("objective from Gamma %.10f  direct %.10f" % (val, direct))
    # normalisation of all Lueders channels
    # canonical images
    for xi in (0, 1):
        for eta in (0, 1):
            blocks = canonical_image(M, xi, eta)
            Wc = np.zeros((64, 64))
            # assemble full canonical W' in qubit order [AI, AO1, AO2, BI, BO1, BO2]
            for (rA, rB), E in blocks.items():
                for cp in range(16):
                    for c in range(16):
                        val_ = sum(cc * z[v] for v, cc in E[cp][c].items())
                        iA, oA, iB, oB = (cp >> 3) & 1, (cp >> 2) & 1, (cp >> 1) & 1, cp & 1
                        jA, pA, jB, pB = (c >> 3) & 1, (c >> 2) & 1, (c >> 1) & 1, c & 1
                        row = (iA << 5) | (oA << 4) | (rA << 3) | (iB << 2) | (oB << 1) | rB
                        col = (jA << 5) | (pA << 4) | (rA << 3) | (jB << 2) | (pB << 1) | rB
                        Wc[row, col] = val_
            chk = is_valid_process(Wc, [2, 4, 2, 4], tol=1e-8)
            print(f"piece ({xi},{eta}) canonical image valid: {chk['ok']}  c1={chk['c1']:.1e} c2={chk['c2']:.1e} c3={chk['c3']:.1e} mineig={chk['mineig']:.3e} tr={chk['trace_err']:.1e}")
    print("peak GB %.2f" % peak_gb())


if __name__ == "__main__":
    for s in range(2):
        main(seed=s, dA=2, dB=2)
    main(seed=5, dA=3, dB=2)
