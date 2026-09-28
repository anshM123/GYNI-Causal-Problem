"""P-AUDIT: link the level-8 certificate to the containment points (floating point; the EXACT PD check is verify3).
From lam = lam_int / D and MY cached row matrix: u = A^T lam - o, Y_k (Y_ii = u_v, Y_ij = u_v / 2), beta = lam.b.
For each genuine strategy's z:  o.z = beta + lam.(A z - b) - sum_k <Y_k, G_k(z)>,  so  beta - I = sum_k <Y_k,G_k> >= 0.
Also: relative size of the most negative Gamma eigenvalue seen in the containment runs (rounding check)."""
import os, sys, pickle, zlib
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit_core as C
import audit_rows as AR
import audit_jstrat as JS
import audit_contain as CT
import audit_lueders_direct as LD

R = AR.load(8)
with open(os.path.join(AR.PUB, "cert3_L8.pkl"), "rb") as f:
    Ct = pickle.load(f)
assert Ct['L'] == 8 and len(Ct['lam_int']) == R['A'].shape[0]
lam = np.array([float(x) for x in Ct['lam_int']]) / float(Ct['D'])
beta = lam @ R['b']
u = R['A'].T @ lam - R['obj']
Ys = []
for (rA, rB, nsz, off) in R['blocks']:
    Y = np.zeros((nsz, nsz))
    iu, ju = np.triu_indices(nsz)
    vals = u[off + ju * (ju + 1) // 2 + iu]
    Y[iu, ju] = np.where(iu == ju, vals, vals / 2)
    Y = Y + np.triu(Y, 1).T
    Ys.append(Y)
print(f"certificate cert3_L8.pkl: beta = lam.b = {beta:.12f} (claimed {float(Ct['beta']):.12f}); float min eig of the "
      f"four Y_k: {[f'{np.linalg.eigvalsh(Y).min():.3e}' for Y in Ys]}")


def link(name, G, I):
    z, blocks, _ = AR.z_from_gamma(R, G)
    viol = lam @ (R['A'] @ z - R['b'])
    pair = sum(np.sum(Y * B) for Y, B in zip(Ys, blocks))
    oz = R['obj'] @ z
    print(f"  {name:28s} I = {I:.12f}  o.z = {oz:.12f}  sum<Y,G> = {pair:.3e}  beta - o.z = {beta - oz:.3e}  "
          f"lam.(Az-b) = {viol:.1e}  identity err {abs(oz - (beta + viol - pair)):.1e}")


for J in (3, 4):
    S = JS.load_strategy(os.path.join(AR.PUB, f"GYNI_J{J}_strategy_cert.npz"))
    link(f"J={J} record strategy", JS.gamma_product(S, R['basis'], (S['P0'], False), (S['P0'], False)), S['claimed'])
for name, seed in (("seesaw3", 0), ("seesaw2", 0), ("ocb", 1), ("rand2", 1)):
    dims, W, KA, KB = CT.family(name, seed)
    rng = np.random.default_rng(5)
    pA = C.lemma1(KA, dims[0], dims[1], rng); pB = C.lemma1(KB, dims[2], dims[3], rng)
    I = C.gyni_value(C.probs_direct(W, KA, KB, dims[0] * dims[1], dims[2] * dims[3]))
    orb = C.strategy_orbit(W, dims, pA, pB)
    Gb = sum(CT.gamma_of(S[0], S[1], S[2], S[3], R['basis']) for S in orb) / 8
    link(f"{name}#{seed} (group avg)", Gb, I)

# rounding check for the most negative eigenvalue seen (dH=(1,2) generic/commuting etc.): relative to ||Gamma||
worst = (0, None)
kinds = ["generic", "equal", "commuting", "trivial", "orthogonal"]
for (dA, dB) in [(1, 2), (2, 2), (4, 4)]:
    for kA in kinds:
        for seed in (1, 2):
            rng = np.random.default_rng(zlib.crc32(f"{dA},{dB},{kA},{seed}".encode()))
            dimsT = [dA, 2 * dA, dB, 2 * dB]
            kB = kinds[(kinds.index(kA) + 2) % 5]
            Wt = C.random_valid_W(dimsT, rng, boundary=1.0)
            pA = LD.party(LD.projector_pair(kA, dA, rng)); pB = LD.party(LD.projector_pair(kB, dB, rng))
            G = LD.gamma_direct(Wt, pA, pB, R['basis'])
            ev = np.linalg.eigvalsh((G + G.conj().T) / 2)
            rel = ev.min() / ev.max()
            if rel < worst[0]:
                worst = (rel, (dA, dB, kA, seed, ev.min(), ev.max()))
print(f"most negative relative eigenvalue lambda_min/lambda_max of full Gamma (L=8): {worst[0]:.2e}  case {worst[1]}  "
      f"(n = {len(R['basis'])**2}; n * eps = {len(R['basis'])**2 * 2.2e-16:.1e})")
