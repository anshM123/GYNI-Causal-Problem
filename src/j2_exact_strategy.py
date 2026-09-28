"""Turn the best two-Jordan-block solution into an EXACTLY verified strategy (rigorous lower bound).
1. rational angles: (cos t, sin t) = ((1-u^2)/(1+u^2), 2u/(1+u^2)) with rational u  -> exact rational projectors
2. solve the W-SDP (Clarabel) for these instruments; W = c0*1 + sum_i c_i B_i with B_i the invariant valid basis
3. rationalise the coefficients c_i (valid-subspace membership and normalisation are then exact by construction)
4. mix with the maximally mixed process: W' = (1-s) W + s c0 1, s rational, and verify W' >= 0 EXACTLY
   (block-diagonal: each sector block checked by exact LDL / Sylvester with fractions)
5. compute the GYNI value of (W', instruments) exactly in rational arithmetic."""
import os, sys, time, pickle, argparse
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import numpy as np
import scipy.sparse as sp
from lueders_J2 import J2Model
from sdp_sparse import SDP

HERE = os.path.dirname(os.path.abspath(__file__))


def rat_angle(t, maxden=1000):
    u = Fr(np.tan(t / 2)).limit_denominator(maxden)
    c = (1 - u * u) / (1 + u * u); s = 2 * u / (1 + u * u)
    return c, s, float(2 * np.arctan(float(u)))


def exact_projs(cs):
    """cs = [(c0,s0),(c1,s1)] per Jordan block j; returns dict (a,x) -> 4x4 Fraction matrix on q (x) l."""
    def kron(A, B):
        return [[A[i // 2][j // 2] * B[i % 2][j % 2] for j in range(4)] for i in range(4)]
    Z0 = [[Fr(1), Fr(0)], [Fr(0), Fr(0)]]
    I2 = [[Fr(1), Fr(0)], [Fr(0), Fr(1)]]
    A0 = kron(Z0, I2)
    A1 = [[Fr(0)] * 4 for _ in range(4)]
    for j, (c, s) in enumerate(cs):
        Pj = [[c * c, c * s], [c * s, s * s]]
        L = [[Fr(1 - j), Fr(0)], [Fr(0), Fr(j)]]
        K = kron(Pj, L)
        for a in range(4):
            for b in range(4):
                A1[a][b] += K[a][b]
    I4 = [[Fr(int(a == b)) for b in range(4)] for a in range(4)]
    sub = lambda X, Y: [[X[a][b] - Y[a][b] for b in range(4)] for a in range(4)]
    return {(0, 0): A0, (1, 0): sub(I4, A0), (0, 1): A1, (1, 1): sub(I4, A1)}


def lueders_vec_exact(P, x):
    """|P>> (x) |x> as a length-32 Fraction vector, order (q_in,l_in,q_out,l_out,reg)."""
    v = [Fr(0)] * 32
    for i in range(4):
        for o in range(4):
            v[(i * 4 + o) * 2 + x] = P[o][i]
    return v


def ldl_pd(Mf):
    n = len(Mf)
    A = [row[:] for row in Mf]
    for j in range(n):
        piv = A[j][j]
        if piv <= 0:
            return False, piv
        for i in range(j + 1, n):
            if A[i][j] != 0:
                f = A[i][j] / piv
                for k in range(j, n):
                    if A[j][k] != 0:
                        A[i][k] -= f * A[j][k]
    return True, None


def main(t1, t2, maxden=1000, cden=10 ** 9):
    t0 = time.time()
    (c1, s1, a1) = rat_angle(t1, maxden); (c2, s2, a2) = rat_angle(t2, maxden)
    print(f"rational angles: t1 {t1:.6f} -> {a1:.6f}, t2 {t2:.6f} -> {a2:.6f}", flush=True)
    model = J2Model()
    val, res = model.value((a1, a2), (a1, a2), return_W=True)
    z = res['z']
    print(f"float SDP value at rational angles: {val:.10f} [{res['status']}]", flush=True)
    # rationalise coefficients
    cq = [Fr(float(x)).limit_denominator(cden) for x in z]
    c0 = Fr(64, 1024)
    # exact block matrices: W_block = c0*I + sum cq_i B_i  (B_i blocks have integer entries)
    min_pivots = []
    blocks_exact = []
    for b, ind in enumerate(model.sectors):
        n = len(ind)
        Wb = [[Fr(0)] * n for _ in range(n)]
        for i in range(n):
            Wb[i][i] = c0
        for ci, Bi in zip(cq, model.blocks[b]):
            if ci == 0 or Bi.nnz == 0:
                continue
            Bc = Bi.tocoo()
            for r_, cc_, d in zip(Bc.row, Bc.col, Bc.data):
                dv = Fr(int(round(d))) if abs(d - round(d)) < 1e-12 else Fr(d).limit_denominator(64)
                Wb[r_][cc_] += ci * dv
        blocks_exact.append(Wb)
    # smallest eigenvalue (float) per block to choose mixing s
    lam = min(np.linalg.eigvalsh(np.array([[float(x) for x in row] for row in Wb])).min() for Wb in blocks_exact)
    s = Fr(0)
    if lam < 1e-9:
        s = Fr(max(0.0, -lam) + 1e-9).limit_denominator(10 ** 12) / (c0 + Fr(max(0.0, -lam) + 1e-9).limit_denominator(10 ** 12))
        s = Fr(float(s) * 1.5).limit_denominator(10 ** 12)
    print(f"float min eig of rationalised W: {lam:.3e}; mixing s = {float(s):.3e}", flush=True)
    ok_all = True
    for Wb in blocks_exact:
        n = len(Wb)
        Wm = [[(1 - s) * Wb[i][j] + (s * c0 if i == j else Fr(0)) for j in range(n)] for i in range(n)]
        ok, piv = ldl_pd(Wm)
        ok_all &= ok
    print(f"EXACT PSD check of W' (all {len(blocks_exact)} blocks): {ok_all}  ({time.time()-t0:.1f}s)", flush=True)
    # exact value: Tr[W' Omega] with Omega = 1/4 sum_xy |u><u|, u = va(y,x) (x) vb(x,y)
    P = exact_projs([(c1, s1), (c2, s2)])
    va = {(a, x): lueders_vec_exact(P[(a, x)], x) for a in (0, 1) for x in (0, 1)}
    # W' as a sparse exact object: W' = (1-s)(c0 I + sum cq_i M_i) + s c0 I ; value = sum_xy 1/4 u^T W' u
    total = Fr(0)
    Ms = [M.tocoo() for M in model.mats]
    for x in (0, 1):
        for y in (0, 1):
            ua, ub = va[(y, x)], va[(x, y)]
            u = [ua[i // 32] * ub[i % 32] for i in range(1024)]
            nz = {i: u[i] for i in range(1024) if u[i] != 0}
            uu = sum(v * v for v in nz.values())
            acc = c0 * uu      # identity part (both (1-s)c0 and s c0 add up to c0)
            for ci, M in zip(cq, Ms):
                if ci == 0:
                    continue
                t_ = Fr(0)
                for r_, cc_, d in zip(M.row, M.col, M.data):
                    if r_ in nz and cc_ in nz:
                        t_ += nz[r_] * nz[cc_] * Fr(int(round(d)))
                acc += (1 - s) * ci * t_
            total += acc / 4
    print(f"EXACT GYNI value of the verified strategy: {float(total):.12f}  (rational with {len(str(total.denominator))}-digit denominator)"
          f"  total {time.time()-t0:.1f}s", flush=True)
    with open(os.path.join(HERE, "j2_exact_strategy.pkl"), "wb") as f:
        pickle.dump(dict(u_angles=(a1, a2), c=cq, s=s, value=total, psd_ok=ok_all), f)
    return total, ok_all


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("t1", type=float); ap.add_argument("t2", type=float)
    a = ap.parse_args()
    main(a.t1, a.t2)
