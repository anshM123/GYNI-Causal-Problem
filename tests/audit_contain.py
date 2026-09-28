"""P-AUDIT containment test: GENERAL strategies -> Lemma 1 (own implementation) -> Gamma (own implementation)
-> check every certified row of mc3.build(L, sym=True), PSD of every register block, objective = I_GYNI.
Also the GYNI-group average computed from 8 explicitly transformed Lueders strategies (checks the fx/fy/swap rows)."""
import os, sys, time, argparse, pickle, json
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
import numpy as np
import scipy.linalg as sla
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit_core as C
import audit_rows as AR

GYNI_DIR = os.path.normpath(os.path.join(HERE, "data"))   # shipped seesaw strategies


# ------------------------------------------------------------------ strategy families
def kraus_from_choi(Ch, dI, dO, tol=1e-13):
    w, V = np.linalg.eigh((Ch + Ch.conj().T) / 2)
    Ks = []
    for lam, v in zip(w, V.T):
        if lam > tol * max(1.0, w.max()):
            Ks.append(np.sqrt(lam) * v.reshape(dI, dO).T)       # vecop(K)[i*dO+o] = K[o,i]
    return Ks


def clean_instrument(Kx, dI, dO):
    """make sum_a sum_k K^+K = 1 exact to machine precision (polar part of the stacked isometry)"""
    out = []
    for x in range(len(Kx)):
        stack = np.vstack([K for a in range(2) for K in Kx[x][a]])
        U, s, Vh = np.linalg.svd(stack, full_matrices=False)
        iso = U @ Vh
        cnt = [len(Kx[x][a]) for a in range(2)]
        Ks, pos = [], 0
        for a in range(2):
            Ks.append([iso[(pos + k) * dO:(pos + k + 1) * dO, :] for k in range(cnt[a])])
            pos += cnt[a]
        out.append(Ks)
    return out


def clean_W(W, dims):
    W = (W + W.conj().T) / 2
    W = C.LV(W, dims)
    D = W.shape[0]
    W = W + (dims[1] * dims[3] - np.trace(W).real) / D * np.eye(D)
    ev = np.linalg.eigvalsh(W).min()
    if ev < 0:
        c = dims[1] * dims[3] / D
        t = -ev / (c - ev)
        W = (1 - t) * W + t * c * np.eye(D)
    return W


def ab_separable_W(dims, rng):
    """A < B:  W = rho_AI (x) D_{AO,BI} (x) 1_BO with D >= 0, Tr_BI D = 1_AO (random channel AO -> BI)"""
    dAI, dAO, dBI, dBO = dims
    G = rng.normal(size=(dAI, dAI)) + 1j * rng.normal(size=(dAI, dAI)); rho = G @ G.conj().T; rho /= np.trace(rho)
    K = C.haar_isometry(dBI * 3, dAO, rng)
    Ks = [K[i * dBI:(i + 1) * dBI, :] for i in range(3)]
    Dm = C.choi_from_kraus(Ks)        # on AO (x) BI
    return np.kron(np.kron(rho, Dm), np.eye(dBO))


def family(name, seed):
    rng = np.random.default_rng(seed)
    if name == "rand2":          # boundary valid W, complex, dims 2222, kappa 3 non-projective instruments
        dims = [2, 2, 2, 2]; W = C.random_valid_W(dims, rng)
        KA = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
        KB = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
    elif name == "rand_asym":    # unequal dims, unequal Kraus counts per outcome
        dims = [2, 3, 3, 2]; W = C.random_valid_W(dims, rng)
        KA = []
        for x in range(2):
            V = C.haar_isometry(4 * 3, 2, rng)                     # 4 Kraus ops: 3 for a=0, 1 for a=1
            Ks = [V[i * 3:(i + 1) * 3, :] for i in range(4)]
            KA.append([Ks[:3], Ks[3:]])
        KB = [C.random_instrument_kraus(3, 2, 3, rng) for _ in range(2)]
    elif name == "rand_bigin":   # d_I > d_O (needs d' > 1 possibly), kappa 3
        dims = [3, 2, 2, 3]; W = C.random_valid_W(dims, rng)
        KA = [C.random_instrument_kraus(3, 2, 3, rng) for _ in range(2)]
        KB = [C.random_instrument_kraus(2, 3, 3, rng) for _ in range(2)]
    elif name == "ocb":          # OCB process (causally nonseparable) + local unitaries, kappa 3 instruments
        dims = [2, 2, 2, 2]; W = C.local_unitary(C.ocb_W(), dims, rng)
        KA = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
        KB = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
    elif name == "ocb_mix":      # OCB mixed with a random boundary valid W
        dims = [2, 2, 2, 2]; W = 0.6 * C.local_unitary(C.ocb_W(), dims, rng) + 0.4 * C.random_valid_W(dims, rng)
        KA = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
        KB = [C.random_instrument_kraus(2, 2, 4, rng) for _ in range(2)]
    elif name == "real":         # real W and real instruments
        dims = [2, 2, 2, 2]; W = C.random_valid_W(dims, rng, real=True)
        KA = [C.random_instrument_kraus(2, 2, 3, rng, real=True) for _ in range(2)]
        KB = [C.random_instrument_kraus(2, 2, 3, rng, real=True) for _ in range(2)]
    elif name == "separable":    # causally separable A<B with random instruments
        dims = [2, 2, 2, 2]; W = ab_separable_W(dims, rng)
        KA = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
        KB = [C.random_instrument_kraus(2, 2, 3, rng) for _ in range(2)]
    elif name == "degenerate":   # deterministic outcome, x-independent instrument, measure-and-prepare, projective
        dims = [2, 2, 2, 2]; W = C.random_valid_W(dims, rng)
        U = C.haar_unitary(2, rng)
        det = [[U], [np.zeros((2, 2))]]                                     # outcome 0 always, unitary channel
        K = C.random_instrument_kraus(2, 2, 3, rng)
        KA = [det, K]
        e = np.eye(2); psi = C.haar_isometry(2, 2, rng)
        mp = [[np.outer(psi[:, 0], e[0])], [np.outer(psi[:, 1], e[1])]]    # measure Z, prepare psi_a
        KB = [mp, mp]                                                       # same instrument for y = 0,1
    elif name.startswith("seesaw"):
        d = int(name[-1])
        with open(os.path.join(GYNI_DIR, f"seesaw_d{d}.pkl"), "rb") as f:
            R = pickle.load(f)
        dims = [d, d, d, d]
        W = clean_W(np.array(R['W'], dtype=complex), dims)
        KA = clean_instrument([[kraus_from_choi(R['MA'][x][a], d, d) for a in range(2)] for x in range(2)], d, d)
        KB = clean_instrument([[kraus_from_choi(R['MB'][x][a], d, d) for a in range(2)] for x in range(2)], d, d)
        # adversarial: extra random local unitaries on all four systems (complexifies everything)
        if seed:
            Us = [C.haar_unitary(d, rng) for _ in range(4)]
            Ufull = np.kron(np.kron(Us[0], Us[1]), np.kron(Us[2], Us[3]))
            W = Ufull @ W @ Ufull.conj().T
            # compensate in the instruments so that p is unchanged: (U_I (x) U_O)|K>> = |U_O K U_I^T>>
            KA = [[[Us[1] @ K @ Us[0].T for K in KA[x][a]] for a in range(2)] for x in range(2)]
            KB = [[[Us[3] @ K @ Us[2].T for K in KB[x][a]] for a in range(2)] for x in range(2)]
    else:
        raise ValueError(name)
    return dims, W, KA, KB


# ------------------------------------------------------------------ p from Gamma (independent of mc3's objective)
def p_from_gamma(G, basis):
    n = len(basis)
    idx = {b: i for i, b in enumerate(basis)}

    def u(a, x):
        v = np.zeros(n)
        v[idx[((), x)]] += 0.5
        v[idx[((x,), x)]] += 0.5 if a == 0 else -0.5
        return v
    p = np.zeros((2, 2, 2, 2))
    for a in (0, 1):
        for b in (0, 1):
            for x in (0, 1):
                for y in (0, 1):
                    uv = np.kron(u(a, x), u(b, y))
                    p[a, b, x, y] = (uv @ G @ uv).real
    return p


def gamma_of(W, dims, pA, pB, basis, reverse=False):
    FA = C.party_F(pA, basis, reverse); FB = C.party_F(pB, basis, reverse)
    return C.gamma_from_F(W, FA, FB, dims[0] * dims[1], dims[2] * dims[3])


def run_case(name, seed, levels, Rs, sym=True, log=None):
    t0 = time.time()
    dims, W, KA, KB = family(name, seed)
    vr = C.validity_report(W, dims)
    p = C.probs_direct(W, KA, KB, dims[0] * dims[1], dims[2] * dims[3])
    gy = C.gyni_value(p)
    rngL = np.random.default_rng(1000 + seed)
    pA = C.lemma1(KA, dims[0], dims[1], rngL)
    pB = C.lemma1(KB, dims[2], dims[3], rngL)
    diag = max(max(t['iso_err'], t['unitary_err']) for t in pA['diag'] + pB['diag'])
    e1A, e2A = C.lemma1_identity_error(pA, KA); e1B, e2B = C.lemma1_identity_error(pB, KB)
    kap = (pA['kappa'], pB['kappa'])
    head = (f"{name}#{seed} dims {dims} kappa {kap} dH ({pA['dH']},{pB['dH']}) GYNI {gy:.6f} | W valid: "
            f"a {vr['a']:.1e} b {vr['b']:.1e} c {vr['c']:.1e} tr {vr['trace']:.1e} mineig {vr['mineig']:.1e} | "
            f"Lemma1: iso/unitary {diag:.1e}, M=T.L.J {max(e1A, e1B):.1e}, Phi(M~)=M {max(e2A, e2B):.1e}")
    print(head, flush=True)
    res = dict(name=name, seed=seed, dims=dims, gyni=gy, validity=vr, lemma1=(diag, max(e1A, e1B), max(e2A, e2B)),
               levels={})
    orbit = C.strategy_orbit(W, dims, pA, pB) if sym else None
    for L in levels:
        R = Rs[L]
        basis = R['basis']
        G = gamma_of(W, dims, pA, pB, basis)
        full_min = np.linalg.eigvalsh((G + G.conj().T) / 2).min()
        z, blocks, asym = AR.z_from_gamma(R, G)
        ev = AR.evaluate(R, z, blocks)
        pg = p_from_gamma(G, basis)
        out = dict(v2=ev['res_v2'], mineig_blocks=ev['mineig'], mineig_full=full_min, herm=asym,
                   obj_err=abs(ev['obj'] - gy), p_err=np.abs(pg - p).max())
        line = (f"   L={L}: V2 max|res| {ev['res_v2']:.1e}  PSD min eig blocks {ev['mineig']:.1e} full {full_min:.1e}  "
                f"|obj-I| {out['obj_err']:.1e}  |p_Gamma-p| {out['p_err']:.1e}  herm {asym:.1e}")
        if sym:
            Gs = [gamma_of(S[0], S[1], S[2], S[3], basis) for S in orbit]
            gys = [C.gyni_value(p_from_gamma(Gg, basis)) for Gg in Gs]
            Gbar = sum(Gs) / len(Gs)
            zb, bb, _ = AR.z_from_gamma(R, Gbar)
            eb = AR.evaluate(R, zb, bb)
            out.update(sym_all=eb['res_all'], sym_v2=eb['res_v2'], sym_fx=eb['res_fx'], sym_fy=eb['res_fy'],
                       sym_swap=eb['res_swap'], sym_mineig=eb['mineig'], sym_obj_err=abs(eb['obj'] - gy),
                       orbit_gyni_spread=max(gys) - min(gys))
            line += (f"\n        sym-avg: ALL rows {eb['res_all']:.1e} (V2 {eb['res_v2']:.1e} fx {eb['res_fx']:.1e} "
                     f"fy {eb['res_fy']:.1e} swap {eb['res_swap']:.1e})  min eig {eb['mineig']:.1e}  "
                     f"|obj-I| {out['sym_obj_err']:.1e}  orbit I spread {out['orbit_gyni_spread']:.1e}")
        print(line, flush=True)
        res['levels'][L] = out
    res['time'] = time.time() - t0
    return res


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--levels", type=int, nargs="+", default=[2, 3, 4, 8])
    ap.add_argument("--cases", nargs="+", default=None)
    ap.add_argument("--seeds", type=int, nargs="+", default=[1, 2])
    ap.add_argument("--nosym", action="store_true")
    ap.add_argument("--out", default="contain_results.pkl")
    a = ap.parse_args()
    Rs = {L: AR.load(L) for L in a.levels}
    cases = a.cases or ["rand2", "rand_asym", "rand_bigin", "ocb", "ocb_mix", "real", "separable", "degenerate",
                        "seesaw2", "seesaw3"]
    allres = []
    for name in cases:
        for s in a.seeds:
            allres.append(run_case(name, s, a.levels, Rs, sym=not a.nosym))
    with open(os.path.join(HERE, a.out), "wb") as f:
        pickle.dump(allres, f)
    # summary
    keys = ["v2", "sym_all", "obj_err", "sym_obj_err", "p_err"]
    print("\nSUMMARY over", len(allres), "strategies x levels", a.levels)
    for k in keys:
        vals = [r['levels'][L][k] for r in allres for L in a.levels if k in r['levels'][L]]
        if vals:
            print(f"  max {k:12s} = {max(vals):.2e}")
    for k in ["mineig_blocks", "mineig_full", "sym_mineig"]:
        vals = [r['levels'][L][k] for r in allres for L in a.levels if k in r['levels'][L]]
        if vals:
            print(f"  min {k:12s} = {min(vals):.2e}")
    print("  max Lemma-1 identity errors:", max(max(r['lemma1']) for r in allres))
