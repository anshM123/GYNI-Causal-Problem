"""P-AUDIT: containment of the published near-optimal lower-bound strategies (J=3: 0.622146712690, J=4:
0.622165901354) in the CERTIFIED relaxation at levels L = 2..8.  W is read from the self-contained .npz certificate
(format documented in verify_strategy.py) in its product form W = c0*1 + sum_{a,b} C[a,b] R_a (x) R_b, so Gamma is
computed as c0 G(x)G + sum C[a,b] Rhat_a (x) Rhat_b with Rhat_e = V^T R_e V (V = word vectors). Own code only."""
import os, sys, time, argparse, pickle
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
import numpy as np
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit_core as C
import audit_rows as AR

SRC = AR.PUB


def load_strategy(path):
    Z = np.load(path)
    J = int(Z['J']); R = Z['R'].astype(np.float64); mim = Z['mim']; pairs = Z['pairs']; y = Z['y']
    D = int(Z['D']); k = int(Z['k'])
    npo = R.shape[0]
    Cm = np.zeros((npo, npo))
    scale = (1.0 - 2.0 ** (-k)) / D
    for t, (a, b) in enumerate(pairs):
        ph = (-1) ** ((int(mim[a]) + int(mim[b])) // 2)
        c = scale * int(y[t]) * ph
        if a == b:
            Cm[a, a] += c
        else:
            Cm[a, b] += c
            Cm[b, a] += c
    cs = [(int(a) / int(b), int(c) / int(d)) for a, b, c, d in zip(Z['c_num'], Z['c_den'], Z['s_num'], Z['s_den'])]
    dI = 2 * J
    P0 = []
    for x in (0, 1):
        P = np.zeros((dI, dI))
        for j, (c, s) in enumerate(cs):
            ph_ = (c, s if x == 1 else -s)
            for qa in range(2):
                for qb in range(2):
                    P[qa * J + j, qb * J + j] = ph_[qa] * ph_[qb]
        P0.append(P)
    claimed = Fraction(int(str(Z['claimed_value_num'])), int(str(Z['claimed_value_den'])))
    return dict(J=J, R=R, Cm=Cm, c0=1.0 / (4 * J * J), P0=P0, dI=dI, claimed=float(claimed))


def vectors(basis, P0, flip_reg=False):
    cols = [np.kron(C.vecop(C.word_op(w, P0)), np.eye(2)[(1 - r) if flip_reg else r]) for (w, r) in basis]
    return np.array(cols).T.real


def gamma_product(S, basis, partyA, partyB):
    """partyX = (P0 list, flip_reg).  Gamma index k*n + l."""
    VA = vectors(basis, *partyA); VB = vectors(basis, *partyB)
    n = VA.shape[1]
    RA = np.einsum('ik,eij,jm->ekm', VA, S['R'], VA, optimize=True)
    RB = np.einsum('ik,eij,jm->ekm', VB, S['R'], VB, optimize=True)
    T = np.einsum('ab,akm->bkm', S['Cm'], RA, optimize=True)
    G4 = np.einsum('bkm,bln->klmn', T, RB, optimize=True)
    G4 += S['c0'] * np.einsum('km,ln->klmn', VA.T @ VA, VB.T @ VB)
    return G4.reshape(n * n, n * n)


def orbit_parties(P0):
    """GYNI group on the (Alice = Bob, swap-invariant W) strategy: fx = Alice letter swap + register flip, Bob
    outcome flip; fy symmetric; swap = identity on this strategy (W symmetric under party exchange, Alice = Bob)."""
    sw = [P0[1], P0[0]]
    fl = [np.eye(P0[0].shape[0]) - P0[0], np.eye(P0[0].shape[0]) - P0[1]]
    out = []
    for f1 in (0, 1):
        for f2 in (0, 1):
            # Alice: letters swapped iff fx; outcome flipped iff fy.  Bob: letters swapped iff fy; outcome flipped iff fx
            def mk(letter, outcome):
                Q = [P0[0], P0[1]]
                if letter:
                    Q = [Q[1], Q[0]]
                if outcome:
                    Q = [np.eye(Q[0].shape[0]) - Q[0], np.eye(Q[0].shape[0]) - Q[1]]
                return Q
            out.append(((mk(f1, f2), bool(f1)), (mk(f2, f1), bool(f2))))
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--J", type=int, nargs="+", default=[3, 4])
    ap.add_argument("--levels", type=int, nargs="+", default=[2, 3, 4, 5, 6, 7, 8])
    a = ap.parse_args()
    Rs = {L: AR.load(L) for L in a.levels}
    for J in a.J:
        t0 = time.time()
        S = load_strategy(os.path.join(SRC, f"GYNI_J{J}_strategy_cert.npz"))
        print(f"J={J}: claimed exact value {S['claimed']:.12f}; projector check "
              f"{max(np.abs(P @ P - P).max() for P in S['P0']):.1e}", flush=True)
        for L in a.levels:
            R = Rs[L]
            basis = R['basis']
            G = gamma_product(S, basis, (S['P0'], False), (S['P0'], False))
            z, blocks, asym = AR.z_from_gamma(R, G)
            ev = AR.evaluate(R, z, blocks)
            fullmin = np.linalg.eigvalsh((G + G.T) / 2).min()
            Gs = [gamma_product(S, basis, pa, pb) for (pa, pb) in orbit_parties(S['P0'])]
            Gbar = sum(Gs) / len(Gs)
            zb, bb, _ = AR.z_from_gamma(R, Gbar)
            eb = AR.evaluate(R, zb, bb)
            dev = np.abs(Gbar - G).max()
            print(f"  L={L}: raw: ALL rows {ev['res_all']:.1e} (V2 {ev['res_v2']:.1e} fx {ev['res_fx']:.1e} fy "
                  f"{ev['res_fy']:.1e} swap {ev['res_swap']:.1e}) min eig blocks {ev['mineig']:.2e} full {fullmin:.2e} "
                  f"obj {ev['obj']:.12f} (|obj-claim| {abs(ev['obj']-S['claimed']):.1e}) | group avg: ALL rows "
                  f"{eb['res_all']:.1e} min eig {eb['mineig']:.2e} |avg-raw| {dev:.1e}  [{time.time()-t0:.0f}s]",
                  flush=True)
