"""Fast exact verification of a two-Jordan-block strategy (rigorous lower bound).
Rational angles via rational tan(t/2); SDP for W at those angles; coefficients rounded to a COMMON denominator
D = 2^40; W' = (1-s) W + s*c0*1 with dyadic s; every sector block of 16*D*2^k*W' is an INTEGER matrix whose positive
definiteness is certified by Sylvester's criterion (fraction-free Bareiss). The GYNI value of (W', exact Lueders
instruments) is then computed exactly in rational arithmetic."""
import os, sys, time, pickle, argparse
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import numpy as np
from lueders_J2 import J2Model
from certify2 import bareiss_leading_minors
from j2_exact_strategy import rat_angle, exact_projs, lueders_vec_exact

HERE = os.path.dirname(os.path.abspath(__file__))


def main(t1, t2, D=2 ** 40, kmix=None, save="j2_exact2.pkl"):
    t0 = time.time()
    (c1, s1, a1) = rat_angle(t1, 1000); (c2, s2, a2) = rat_angle(t2, 1000)
    print(f"rational angles: {a1:.8f}, {a2:.8f}  (cos,sin) = ({c1},{s1}), ({c2},{s2})", flush=True)
    model = J2Model()
    val, res = model.value((a1, a2), (a1, a2), return_W=True)
    z = res['z']
    print(f"float SDP value {val:.10f} [{res['status']}]", flush=True)
    zi = [int(round(x * D)) for x in z]          # coefficients = zi / D
    # float min eigenvalue of the rounded W to choose the dyadic mixing weight
    lam = 1.0
    for b, ind in enumerate(model.sectors):
        n = len(ind)
        Wb = np.eye(n) / 16.0
        for q, Bi in zip(zi, model.blocks[b]):
            if q and Bi.nnz:
                Wb = Wb + (q / D) * Bi.toarray()
        lam = min(lam, np.linalg.eigvalsh(Wb).min())
    if kmix is None:
        need = max(0.0, -lam) * 16 * 2.0 + 1e-12      # s*c0 > -lam  with factor 2 safety
        kmix = max(1, int(np.floor(-np.log2(need))))
    s = Fr(1, 2 ** kmix)
    print(f"float min eig {lam:.3e}; mixing s = 2^-{kmix} = {float(s):.3e}", flush=True)
    # integer blocks: M = 16 * D * 2^k * W' = 16*D*(2^k - 1)*W + D*1   (W' = (1-s)W + s/16 * 1)
    K = 2 ** kmix
    ok_all = True
    minpiv = None
    for b, ind in enumerate(model.sectors):
        n = len(ind)
        Mb = [[0] * n for _ in range(n)]
        for i in range(n):
            Mb[i][i] = (K - 1) * D + D           # from W's identity part: 16*D*(K-1)*(1/16) ; plus s-part D
        for q, Bi in zip(zi, model.blocks[b]):
            if q == 0 or Bi.nnz == 0:
                continue
            Bc = Bi.tocoo()
            for r_, cc_, d in zip(Bc.row, Bc.col, Bc.data):
                di = int(round(d)); assert abs(d - di) < 1e-12
                Mb[r_][cc_] += 16 * (K - 1) * q * di
        # symmetric?
        assert all(Mb[i][j] == Mb[j][i] for i in range(n) for j in range(n))
        minors = bareiss_leading_minors(Mb)
        pd = len(minors) == n and all(m > 0 for m in minors)
        ok_all &= pd
    print(f"EXACT PD check of W' ({len(model.sectors)} integer blocks, Sylvester/Bareiss): {ok_all}  ({time.time()-t0:.1f}s)", flush=True)
    # exact value
    P = exact_projs([(c1, s1), (c2, s2)])
    va = {(a, x): lueders_vec_exact(P[(a, x)], x) for a in (0, 1) for x in (0, 1)}
    Ms = [M.tocoo() for M in model.mats]
    total = Fr(0)
    for x in (0, 1):
        for y in (0, 1):
            ua, ub = va[(y, x)], va[(x, y)]
            nz = {}
            for i in range(32):
                if ua[i] == 0:
                    continue
                for j in range(32):
                    if ub[j] != 0:
                        nz[i * 32 + j] = ua[i] * ub[j]
            uu = sum(v * v for v in nz.values())
            acc = Fr(1, 16) * uu
            for q, M in zip(zi, Ms):
                if q == 0:
                    continue
                t_ = Fr(0)
                for r_, cc_, d in zip(M.row, M.col, M.data):
                    a_ = nz.get(int(r_))
                    if a_ is None:
                        continue
                    b_ = nz.get(int(cc_))
                    if b_ is None:
                        continue
                    t_ += a_ * b_ * int(round(d))
                if t_ != 0:
                    acc += (1 - s) * Fr(q, D) * t_
            total += acc / 4
    print(f"EXACT GYNI value of the verified strategy: {float(total):.12f}  total {time.time()-t0:.1f}s", flush=True)
    with open(os.path.join(HERE, save), "wb") as f:
        pickle.dump(dict(angles=(a1, a2), cs=((c1, s1), (c2, s2)), zi=zi, D=D, kmix=kmix, value=total, pd=ok_all), f)
    return total, ok_all


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("t1", type=float); ap.add_argument("t2", type=float)
    a = ap.parse_args()
    main(a.t1, a.t2)
