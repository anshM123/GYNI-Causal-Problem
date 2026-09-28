"""P-AUDIT: EXPLICIT check of Lemma 1 in small dimensions: form W~ = (Phi_A^+ (x) Phi_B^+)(W) as a matrix on
H_A (x) (H_A (x) X) (x) H_B (x) (H_B (x) Y) and test directly: PSD, valid-subspace conditions, trace, normalisation on
random product channels (not only product states), statistics with the Lueders instruments M~(rho) = P rho P (x) |x><x|;
the same for the register-twirled and the complex-conjugated W~; Gamma(explicit Gram) = Gamma(Phi-trick)."""
import os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit_core as C
import audit_rows as AR


def random_channel_choi(din, dout, rng, nk=3):
    V = C.haar_isometry(nk * dout, din, rng)
    return C.choi_from_kraus([V[i * dout:(i + 1) * dout, :] for i in range(nk)])


def twirl_registers(Wt, dimsT, nX=2):
    """(1/n^2) sum_{j,k} Z^j_X Z^k_Y W~ Z^-j_X Z^-k_Y ; X is the last factor of Alice's output, Y of Bob's.
    dimsT = [dH_A, dH_A*nX, dH_B, dH_B*nX]; implemented as dephasing of the register indices."""
    dHA, dOA, dHB, dOB = dimsT
    T = Wt.reshape(dHA, dOA // nX, nX, dHB, dOB // nX, nX, dHA, dOA // nX, nX, dHB, dOB // nX, nX)
    mask = np.zeros((nX, nX, nX, nX))
    for r in range(nX):
        for s in range(nX):
            mask[r, s, r, s] = 1.0
    T = np.einsum('abrcdsefught,rsut->abrcdsefught', T, mask)     # keep only r = r', s = s'
    return T.reshape(Wt.shape)


def main():
    # (d_I <= m*kappa*d_O is forced by trace preservation; extra_dprime > 0 pads H_A with C^{d'} as in PROOF.md)
    configs = [([2, 2, 2, 2], (1, 1), False, 0), ([2, 1, 2, 2], (2, 1), False, 0), ([3, 1, 2, 2], (2, 1), False, 0),
               ([2, 2, 2, 1], (1, 2), False, 0), ([2, 2, 2, 2], (1, 1), True, 0), ([2, 2, 3, 1], (1, 2), False, 0),
               ([2, 1, 2, 1], (1, 1), False, 1)]
    R3 = AR.load(3)
    worst = {}
    for ci, (dims, kap, real, xdp) in enumerate(configs):
        for seed in (11, 12, 13):
            rng = np.random.default_rng(seed + 100 * ci)
            W = C.random_valid_W(dims, rng, real=real)
            if ci == 0 and seed == 11:
                W = 0.5 * W + 0.5 * C.local_unitary(C.ocb_W(), dims, rng)          # include OCB
            KA = [C.random_instrument_kraus(dims[0], dims[1], kap[0], rng, real=real) for _ in range(2)]
            KB = [C.random_instrument_kraus(dims[2], dims[3], kap[1], rng, real=real) for _ in range(2)]
            pA = C.lemma1(KA, dims[0], dims[1], rng, extra_dprime=xdp)
            pB = C.lemma1(KB, dims[2], dims[3], rng, extra_dprime=xdp)
            dHA, dHB = pA['dH'], pB['dH']
            dimsT = [dHA, 2 * dHA, dHB, 2 * dHB]
            t0 = time.time()
            Wt = C.Wtilde_explicit(W, pA, pB)
            checks = {}
            for tag, X in (("raw", Wt), ("twirl", twirl_registers(Wt, dimsT)), ("conj", Wt.conj())):
                vr = C.validity_report(X, dimsT)
                checks[tag] = vr
            # statistics with Lueders instruments + register
            p = C.probs_direct(W, KA, KB, dims[0] * dims[1], dims[2] * dims[3])
            pt = np.zeros_like(p)
            for x in (0, 1):
                for y in (0, 1):
                    for a in (0, 1):
                        for b in (0, 1):
                            u = np.kron(C.lueders_choi_vec(pA, a, x), C.lueders_choi_vec(pB, b, y))
                            pt[a, b, x, y] = (u.conj() @ Wt @ u).real
            ptw = np.zeros_like(p)
            Wtw = twirl_registers(Wt, dimsT)
            for x in (0, 1):
                for y in (0, 1):
                    for a in (0, 1):
                        for b in (0, 1):
                            u = np.kron(C.lueders_choi_vec(pA, a, x), C.lueders_choi_vec(pB, b, y))
                            ptw[a, b, x, y] = (u.conj() @ Wtw @ u).real
            # normalisation on random product CHANNELS H -> H (x) X (general CPTP maps, not only product states)
            nerr = 0.0
            for _ in range(4):
                CA = random_channel_choi(dHA, 2 * dHA, rng); CB = random_channel_choi(dHB, 2 * dHB, rng)
                nerr = max(nerr, abs(np.trace(Wt @ np.kron(CA, CB)) - 1))
            # Gamma: explicit Gram vs Phi-trick (L=3 basis)
            basis = R3['basis']
            VA = C.word_vectors(basis, pA['P0']); VB = C.word_vectors(basis, pB['P0'])
            G1 = C.gamma_from_Wtilde(Wt, VA, VB)
            G2 = C.gamma_from_F(W, C.party_F(pA, basis), C.party_F(pB, basis), dims[0] * dims[1], dims[2] * dims[3])
            G3 = C.gamma_from_F(W, C.party_F(pA, basis, explicit=True), C.party_F(pB, basis, explicit=True),
                                dims[0] * dims[1], dims[2] * dims[3])
            gerr = max(np.abs(G1 - G2).max(), np.abs(G1 - G3).max())
            # the V2 rows evaluated on the explicit-W~ Gamma
            z, bl, _ = AR.z_from_gamma(R3, G1)
            ev = AR.evaluate(R3, z, bl)
            line = (f"dims {dims} kappa {kap} real {real} seed {seed}: W~ {Wt.shape[0]}x{Wt.shape[0]} | "
                    + " | ".join(f"{t}: a {v['a']:.0e} b {v['b']:.0e} c {v['c']:.0e} tr {v['trace']:.0e} "
                                 f"herm {v['herm']:.0e} mineig {v['mineig']:.1e}" for t, v in checks.items())
                    + f" | |p~-p| {np.abs(pt-p).max():.0e} twirled {np.abs(ptw-p).max():.0e} | channel-norm err "
                    f"{nerr:.0e} | Gamma explicit-vs-trick {gerr:.0e} | L3 V2 {ev['res_v2']:.0e} [{time.time()-t0:.1f}s]")
            print(line, flush=True)
            for t, v in checks.items():
                for k2, val in v.items():
                    key = t + "_" + k2
                    worst[key] = min(worst.get(key, 1e9), val) if k2 == 'mineig' else max(worst.get(key, 0), val)
            for key, val in (("p_err", np.abs(pt - p).max()), ("p_err_twirl", np.abs(ptw - p).max()),
                             ("chan_norm", nerr), ("gamma_err", gerr), ("v2_L3", ev['res_v2'])):
                worst[key] = max(worst.get(key, 0), val)
    print("\nWORST over all configs:", {k: float(f"{v:.2e}") for k, v in worst.items()})


if __name__ == "__main__":
    main()
