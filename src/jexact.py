"""Exact verification of a J-block Lueders strategy (rigorous lower bound on I_GYNI).
Angles theta_j with rational tan(theta_j/4)  ->  rational (cos, sin)(theta_j/2)  (bisector basis).
W = c0*1 + sum_t (y_t / D) E_t  (E_t: exact integer invariant valid basis; D = 2^40)
W' = (1 - 2^-k) W + 2^-k c0 1.  Validity + normalisation hold exactly by construction (allowed Pauli-type patterns,
identity coefficient c0 = 1/(4J^2)).  PSD: W' is exactly invariant under register twirl, label twirl and the GYNI
group, so W' >= 0  <=>  every sector block (cA <= cB) of register block (0,0) is PSD; each such block of
(4J^2 D 2^k) W' is an integer matrix, certified positive definite by Sylvester's criterion (Bareiss).
The value sum_xy 1/4 <u_xy|W'|u_xy> is computed exactly from all four register blocks."""
import os, sys, time, pickle, argparse
os.environ.setdefault("OMP_NUM_THREADS", "3"); os.environ.setdefault("MKL_NUM_THREADS", "3")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb
start_watchdog(3.5, period=0.1)
from fractions import Fraction as Fr
import numpy as np
from jmodel import JModel
from certify2 import bareiss_leading_minors

HERE = os.path.dirname(os.path.abspath(__file__))


def rat_half_angle(t, maxden=2000):
    u = Fr(np.tan(t / 4)).limit_denominator(maxden)
    c = (1 - u * u) / (1 + u * u); s = 2 * u / (1 + u * u)
    return c, s, float(4 * np.arctan(float(u)))


def exact_u(m, cs, a, x):
    """restricted (charge-0, register x) Fraction vector |P_{a|x}>> in basis (q_in, q_out, l)."""
    J = m.J
    v = [Fr(0)] * (4 * J)
    for l, (c, s) in enumerate(cs):
        sg = 1 if x == 1 else -1
        ph = (c, sg * s)
        P0 = [[ph[0] * ph[0], ph[0] * ph[1]], [ph[1] * ph[0], ph[1] * ph[1]]]
        P = P0 if a == 0 else [[1 - P0[0][0], -P0[0][1]], [-P0[1][0], 1 - P0[1][1]]]
        for qi in range(2):
            for qo in range(2):
                v[(qi * 2 + qo) * J + l] = P[qo][qi]
    return v


def party_quadform(m, cs, e_idx, r, a, x):
    """exact  u^T (party element e restricted to register r, charge-0 sector) u  with u = |P_{a|x}>> (Fractions)."""
    u = exact_u(m, cs, a, x)
    Bm = np.rint(m.rest[(e_idx, r, 0)]).astype(np.int64)
    tot = Fr(0)
    nz = [(i, u[i]) for i in range(len(u)) if u[i] != 0]
    for (i, ui) in nz:
        row = Bm[i]
        for (j, uj) in nz:
            if row[j]:
                tot += ui * uj * int(row[j])
    return tot


def exact_value(m, cs, yi, D, K):
    """sum_xy 1/4 <u_xy|W'|u_xy> exactly, using u_xy = uA (x) uB and E_t = ph (a(x)b + b(x)a):
    <uA uB| a(x)b |uA uB> = (uA^T a uA)(uB^T b uB)  (restricted to the (register, charge-0) blocks)."""
    J = m.J
    c0 = Fr(1, 4 * J * J)
    s_ = Fr(1, K)
    need = sorted({i for (ia, ib, ph) in m.elems for i in (ia, ib)})
    total = Fr(0)
    for x in (0, 1):
        for yy in (0, 1):
            ua = exact_u(m, cs, yy, x); ub = exact_u(m, cs, x, yy)
            nA = sum(v * v for v in ua); nB = sum(v * v for v in ub)
            qa = {e: party_quadform(m, cs, e, x, yy, x) for e in need}      # Alice: register x, outcome a=y
            qb = {e: party_quadform(m, cs, e, yy, x, yy) for e in need}     # Bob: register y, outcome b=x
            acc = c0 * nA * nB
            for t, q in enumerate(yi):
                if q == 0:
                    continue
                ia, ib, ph = m.elems[t]
                tt = qa[ia] * qb[ib]
                if ia != ib:
                    tt += qa[ib] * qb[ia]
                acc += (1 - s_) * Fr(q, D) * ph * tt
            total += acc / 4
    return total


def main(J, thetas, D=2 ** 40, save=None, tol=1e-9):
    t0 = time.time()
    m = JModel(J)
    cs, ths = [], []
    for t in thetas:
        c, s, tt = rat_half_angle(t)
        cs.append((c, s)); ths.append(tt)
    print(f"rational angles {np.round(ths, 8)} (rad) = {np.round(np.degrees(ths), 5)} deg", flush=True)
    val, sol, const = m.value_sparse(tuple(ths), tol=tol, return_sol=True, maxit=150)
    y = sol['y']
    print(f"float SDP value {val:.10f} (gap {sol['gap']:.1e}, pinf {sol['pinf']:.1e}, it {sol['it']}) ({time.time()-t0:.1f}s)", flush=True)
    yi = [int(round(v * D)) for v in y]
    c0 = Fr(1, 4 * J * J)
    nsec = len(m.sectors)
    pairs = [(cA, cB) for cA in range(nsec) for cB in range(cA, nsec)]
    # float check of min eigenvalue of the rounded W (register (0,0) blocks) to choose the mixing weight
    lam = 1.0
    for (cA, cB) in pairs:
        n = m.rest[(0, 0, cA)].shape[0] * m.rest[(0, 0, cB)].shape[0]
        Wb = float(c0) * np.eye(n)
        for t, q in enumerate(yi):
            if q:
                Wb = Wb + (q / D) * m.block(t, 0, 0, cA, cB)
        lam = min(lam, np.linalg.eigvalsh(Wb).min())
    need = max(0.0, -lam) / float(c0) * 2.0 + 1e-15
    k = max(1, int(np.floor(-np.log2(need)))) if need > 0 else 40
    k = min(k, 60)
    K = 2 ** k
    print(f"float min eig of rounded W: {lam:.3e} -> mixing 2^-{k}", flush=True)
    # exact integer blocks:  N = 4J^2 * D * K * W' = D*K*1 + 4J^2*(K-1)*sum_t y_t E_t
    ok_all = True
    for (cA, cB) in pairs:
        n = m.rest[(0, 0, cA)].shape[0] * m.rest[(0, 0, cB)].shape[0]
        Mi = np.zeros((n, n), dtype=object)
        for i in range(n):
            Mi[i, i] = D * K
        for t, q in enumerate(yi):
            if q == 0:
                continue
            B = m.block(t, 0, 0, cA, cB)
            Bi = np.rint(B).astype(np.int64)
            assert np.abs(B - Bi).max() < 1e-9
            nz = np.nonzero(Bi)
            for r_, c_ in zip(*nz):
                Mi[r_, c_] += 4 * J * J * (K - 1) * q * int(Bi[r_, c_])
        Ml = [[int(Mi[i, j]) for j in range(n)] for i in range(n)]
        assert all(Ml[i][j] == Ml[j][i] for i in range(n) for j in range(n))
        minors = bareiss_leading_minors(Ml)
        pd = len(minors) == n and all(mm > 0 for mm in minors)
        ok_all &= pd
        if not pd:
            print(f"   block {(cA, cB)} NOT PD", flush=True)
    print(f"EXACT PD check ({len(pairs)} integer sector blocks): {ok_all}  ({time.time()-t0:.1f}s)", flush=True)
    total = exact_value(m, cs, yi, D, K)
    print(f"EXACT GYNI value of the verified J={J} strategy: {float(total):.12f}   total {time.time()-t0:.1f}s, "
          f"peak {peak_gb():.2f} GB", flush=True)
    if save:
        with open(os.path.join(HERE, save), "wb") as f:
            pickle.dump(dict(J=J, cs=cs, thetas=ths, yi=yi, D=D, k=k, value=total, pd=ok_all), f)
    return total, ok_all


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--J", type=int, default=3)
    ap.add_argument("thetas", type=float, nargs="+")
    ap.add_argument("--save", default=None)
    a = ap.parse_args()
    main(a.J, a.thetas, save=a.save)
