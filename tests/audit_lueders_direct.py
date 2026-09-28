"""P-AUDIT: (i) generic Lueders-form strategies drawn DIRECTLY: random valid W~ on H_A (x) (H_A (x) X) (x) H_B (x)
(H_B (x) Y) (complex, NOT register-diagonal, boundary of the PSD cone) with random projector pairs of all rank
patterns incl. degenerate realisations (P=0, P=1, P0=P1, commuting, orthogonal) in d = 1..4, levels 2..8;
Gamma is taken literally (full complex Gram matrix), then Re + register blocks.  (ii) group average computed from the
8 explicitly transformed strategies at the W~ level.  (iii) NEGATIVE CONTROLS showing the test has teeth."""
import os, sys, time, zlib
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit_core as C
import audit_rows as AR


def rand_proj(d, r, rng):
    if r == 0:
        return np.zeros((d, d), dtype=complex)
    V = C.haar_isometry(d, r, rng)
    return V @ V.conj().T


def projector_pair(kind, d, rng):
    if kind == "generic":
        return [rand_proj(d, int(rng.integers(0, d + 1)), rng), rand_proj(d, int(rng.integers(0, d + 1)), rng)]
    if kind == "equal":
        P = rand_proj(d, max(1, d // 2), rng); return [P, P.copy()]
    if kind == "commuting":
        U = C.haar_unitary(d, rng)
        D1 = np.diag(rng.integers(0, 2, d).astype(float)); D2 = np.diag(rng.integers(0, 2, d).astype(float))
        return [U @ D1 @ U.conj().T, U @ D2 @ U.conj().T]
    if kind == "trivial":
        return [np.zeros((d, d), dtype=complex), np.eye(d, dtype=complex)]
    if kind == "orthogonal":
        U = C.haar_unitary(d, rng); k = max(1, d // 2)
        D1 = np.diag([1.0] * k + [0.0] * (d - k)); D2 = np.diag([0.0] * k + [1.0] * (d - k))
        return [U @ D1 @ U.conj().T, U @ D2 @ U.conj().T]
    raise ValueError(kind)


def party(P0, nX=2):
    d = P0[0].shape[0]
    return dict(P0=P0, P=[[P0[x], np.eye(d) - P0[x]] for x in range(nX)], dH=d, nX=nX)


# ---- group action at the W~ level ------------------------------------------------------------------------------
def flip_reg(Wt, dimsT, who):
    """W~ -> F W~ F with F flipping the register of Alice (who=0) or Bob (who=1)"""
    dHA, dOA, dHB, dOB = dimsT
    T = Wt.reshape(dHA, dOA // 2, 2, dHB, dOB // 2, 2, dHA, dOA // 2, 2, dHB, dOB // 2, 2)
    axes = (2, 8) if who == 0 else (5, 11)
    T = np.flip(np.flip(T, axis=axes[0]), axis=axes[1])
    return T.reshape(Wt.shape)


def swapW(Wt, dimsT):
    dA = dimsT[0] * dimsT[1]; dB = dimsT[2] * dimsT[3]
    return Wt.reshape(dA, dB, dA, dB).transpose(1, 0, 3, 2).reshape(dA * dB, dA * dB)


def orbit(Wt, dimsT, pA, pB, wrong_fx=False):
    def lsw(p):
        return party([p['P0'][1], p['P0'][0]])

    def ofl(p):
        d = p['dH']; return party([np.eye(d) - p['P0'][0], np.eye(d) - p['P0'][1]])

    def fx(S):
        W_, dT, a, b = S
        return ((W_ if wrong_fx else flip_reg(W_, dT, 0)), dT, lsw(a), ofl(b))

    def fy(S):
        W_, dT, a, b = S
        return (flip_reg(W_, dT, 1), dT, ofl(a), lsw(b))

    def sw(S):
        W_, dT, a, b = S
        return (swapW(W_, dT), [dT[2], dT[3], dT[0], dT[1]], b, a)
    out = []
    for s in (0, 1):
        for f1 in (0, 1):
            for f2 in (0, 1):
                S = (Wt, dimsT, pA, pB)
                if f1: S = fx(S)
                if f2: S = fy(S)
                if s: S = sw(S)
                out.append(S)
    return out


def gamma_direct(Wt, pA, pB, basis, word_mode="dihedral"):
    if word_mode == "dihedral":
        VA = C.word_vectors(basis, pA['P0']); VB = C.word_vectors(basis, pB['P0'])
    else:   # NEGATIVE CONTROL: idempotent words (A_x = P_{0|x}) used where the dihedral basis is expected
        def wv(p):
            cols = []
            for (w, r) in basis:
                M = np.eye(p['dH'], dtype=complex)
                for c in w:
                    M = M @ p['P0'][c]
                cols.append(np.kron(C.vecop(M), np.eye(2)[r]))
            return np.array(cols).T
        VA, VB = wv(pA), wv(pB)
    return C.gamma_from_Wtilde(Wt, VA, VB)


def lueders_gyni(Wt, pA, pB):
    p = np.zeros((2, 2, 2, 2))
    for x in (0, 1):
        for y in (0, 1):
            for a in (0, 1):
                for b in (0, 1):
                    u = np.kron(np.kron(C.vecop(pA['P'][x][a]), np.eye(2)[x]), np.kron(C.vecop(pB['P'][y][b]), np.eye(2)[y]))
                    p[a, b, x, y] = (u.conj() @ Wt @ u).real
    return C.gyni_value(p)


def main():
    levels = [2, 3, 4, 5, 6, 7, 8]
    Rs = {L: AR.load(L) for L in levels}
    kinds = ["generic", "equal", "commuting", "trivial", "orthogonal"]
    worst = dict(v2=0, sym=0, obj=0, mineig=0, full_mineig=0)
    ncase = 0
    for (dA, dB) in [(1, 2), (2, 2), (2, 3), (3, 3), (4, 2), (4, 4)]:
        for kA in kinds:
            kB = kinds[(kinds.index(kA) + 2) % len(kinds)]
            for seed in (1, 2):
                rng = np.random.default_rng(zlib.crc32(f"{dA},{dB},{kA},{seed}".encode()))
                dimsT = [dA, 2 * dA, dB, 2 * dB]
                Wt = C.random_valid_W(dimsT, rng, boundary=1.0)
                vr = C.validity_report(Wt, dimsT)
                pA = party(projector_pair(kA, dA, rng)); pB = party(projector_pair(kB, dB, rng))
                I = lueders_gyni(Wt, pA, pB)
                orb = orbit(Wt, dimsT, pA, pB)
                t0 = time.time()
                msg = []
                for L in levels:
                    R = Rs[L]
                    G = gamma_direct(Wt, pA, pB, R['basis'])
                    z, bl, asym = AR.z_from_gamma(R, G)
                    ev = AR.evaluate(R, z, bl)
                    Gb = sum(gamma_direct(S[0], S[2], S[3], R['basis']) for S in orb) / 8
                    zb, bb, _ = AR.z_from_gamma(R, Gb)
                    eb = AR.evaluate(R, zb, bb)
                    evs = np.linalg.eigvalsh((G + G.conj().T) / 2)
                    fm = evs.min()
                    worst['v2'] = max(worst['v2'], ev['res_v2']); worst['sym'] = max(worst['sym'], eb['res_all'])
                    worst['obj'] = max(worst['obj'], abs(ev['obj'] - I), abs(eb['obj'] - I))
                    worst['mineig'] = min(worst['mineig'], ev['mineig'], eb['mineig'])
                    worst['full_mineig'] = min(worst['full_mineig'], fm)
                    worst['rel_mineig'] = min(worst.get('rel_mineig', 0.0), fm / evs.max())
                    msg.append(f"L{L}:{ev['res_v2']:.0e}/{eb['res_all']:.0e}")
                ncase += 1
                print(f"dH=({dA},{dB}) {kA:10s}/{kB:10s} s{seed}: W~ valid (a {vr['a']:.0e} c {vr['c']:.0e} mineig "
                      f"{vr['mineig']:.0e}) I={I:.4f} | V2/sym-all residuals " + " ".join(msg) +
                      f" [{time.time()-t0:.1f}s]", flush=True)
    print(f"\nGENERIC LUEDERS-FORM: {ncase} strategies x levels {levels}: max V2 residual {worst['v2']:.2e}, max "
          f"residual of ALL rows on group average {worst['sym']:.2e}, max |obj - I| {worst['obj']:.2e}, "
          f"min eig blocks {worst['mineig']:.2e}, min eig full complex Gamma {worst['full_mineig']:.2e} "
          f"(relative to lambda_max: {worst['rel_mineig']:.2e}; n*eps = {1156 * 2.2e-16:.1e})")

    # ---------------- NEGATIVE CONTROLS ----------------
    print("\nNEGATIVE CONTROLS (each must FAIL visibly):")
    R = Rs[4]
    rng = np.random.default_rng(7)
    dimsT = [2, 4, 2, 4]
    pA = party([rand_proj(2, 1, rng), rand_proj(2, 1, rng)]); pB = party([rand_proj(2, 1, rng), rand_proj(2, 1, rng)])
    Wt = C.random_valid_W(dimsT, rng)
    # N1: invalid W~ (random PSD, correct trace, NOT in the valid subspace)
    X = rng.normal(size=(64, 64)) + 1j * rng.normal(size=(64, 64)); Wbad = X @ X.conj().T
    Wbad *= 16 / np.trace(Wbad).real
    ev = AR.evaluate(R, *AR.z_from_gamma(R, gamma_direct(Wbad, pA, pB, R['basis']))[:2])
    print(f"  N1 random PSD non-valid W~:                 max V2 residual {ev['res_v2']:.2e}")
    # N1b: valid W~ + eps * (Z on Alice's OUTPUT register only)  [support {A_O}: forbidden]
    Zr = np.kron(np.kron(np.eye(2), np.kron(np.eye(2), np.diag([1.0, -1.0]))), np.eye(8))
    ev0 = AR.evaluate(R, *AR.z_from_gamma(R, gamma_direct(Wt, pA, pB, R['basis']))[:2])
    for eps in (1e-3, 1e-6):
        ev = AR.evaluate(R, *AR.z_from_gamma(R, gamma_direct(Wt + eps * Zr, pA, pB, R['basis']))[:2])
        print(f"  N1b valid W~ + {eps:.0e} * Z_(A_O register):   max V2 residual {ev['res_v2']:.2e}  "
              f"(unperturbed {ev0['res_v2']:.1e})")
    # N1c: valid W~ + eps * (sigma on A_I (x) A_O only), support {A_I, A_O} (forbidden: A_O without B_I)
    S = np.kron(np.kron(np.array([[0, 1], [1, 0]]), np.kron(np.array([[0, 1], [1, 0]]), np.eye(2))), np.eye(8))
    ev = AR.evaluate(R, *AR.z_from_gamma(R, gamma_direct(Wt + 1e-4 * S, pA, pB, R['basis']))[:2])
    print(f"  N1c valid W~ + 1e-4 * X_AI X_AO (loop):      max V2 residual {ev['res_v2']:.2e}")
    # N2: wrong symmetry map (fx WITHOUT the register flip)
    orb = orbit(Wt, dimsT, pA, pB, wrong_fx=True)
    Gb = sum(gamma_direct(S[0], S[2], S[3], R['basis']) for S in orb) / 8
    eb = AR.evaluate(R, *AR.z_from_gamma(R, Gb)[:2])
    orb = orbit(Wt, dimsT, pA, pB)
    Gb2 = sum(gamma_direct(S[0], S[2], S[3], R['basis']) for S in orb) / 8
    eb2 = AR.evaluate(R, *AR.z_from_gamma(R, Gb2)[:2])
    print(f"  N2 group average with fx lacking register flip: fx rows {eb['res_fx']:.2e}, all {eb['res_all']:.2e}  "
          f"(correct orbit: all {eb2['res_all']:.1e});  unsymmetrised Gamma: fx rows "
          f"{AR.evaluate(R, *AR.z_from_gamma(R, gamma_direct(Wt, pA, pB, R['basis']))[:2])['res_fx']:.2e}")
    # N3: idempotent words used in place of the dihedral words
    ev = AR.evaluate(R, *AR.z_from_gamma(R, gamma_direct(Wt, pA, pB, R['basis'], word_mode="idem"))[:2])
    print(f"  N3 idempotent words in the dihedral row list: max V2 residual {ev['res_v2']:.2e}")
    # N4: Lemma 1 with J^dagger instead of J^T in the absorbed Kraus (complex J): objective must disagree
    rng = np.random.default_rng(3)
    dims = [2, 2, 2, 2]; W = C.random_valid_W(dims, rng)
    KA = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]; KB = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
    I0 = C.gyni_value(C.probs_direct(W, KA, KB, 4, 4))
    qA = C.lemma1(KA, 2, 2, rng); qB = C.lemma1(KB, 2, 2, rng)
    good = C.gamma_from_F(W, C.party_F(qA, R['basis']), C.party_F(qB, R['basis']), 4, 4)
    bad = dict(qA); bad['J'] = qA['J'].conj()          # J^T -> J^dagger  <=>  J -> conj(J) inside the code
    Gbad = C.gamma_from_F(W, C.party_F(bad, R['basis']), C.party_F(qB, R['basis']), 4, 4)
    e_good = AR.evaluate(R, *AR.z_from_gamma(R, good)[:2]); e_bad = AR.evaluate(R, *AR.z_from_gamma(R, Gbad)[:2])
    print(f"  N4 J^dagger instead of J^T: |obj - I| = {abs(e_bad['obj'] - I0):.2e} (correct J^T: "
          f"{abs(e_good['obj'] - I0):.1e}); V2 residual {e_bad['res_v2']:.1e} (a valid process for a different "
          f"strategy, so V2 still holds)")


if __name__ == "__main__":
    main()
