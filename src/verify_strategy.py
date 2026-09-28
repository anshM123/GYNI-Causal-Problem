"""STAND-ALONE, SOLVER-FREE, EXACT verification (v2: explicit int64 overflow guard (0)) of an explicit GYNI strategy (lower bound on I_GYNI).
Depends only on numpy and Python's fractions; reads a self-contained .npz certificate (export_strategy_cert.py).

Strategy format.  Each party: A_I = C^2 (Jordan qubit q) (x) C^J (label l)  [dim 2J],
                                A_O = C^2 (q) (x) C^J (l) (x) C^2 (setting register)  [dim 4J];
basis ordering of A_I (x) A_O: (q_in, l_in, q_out, l_out, reg).
Process:  W = c0*1 + (1 - 2^-k) * sum_t (y_t / D) * i^(m_a+m_b) * (R_a (x) R_b + R_b (x) R_a)      (a != b)
          (single term R_a (x) R_a if a == b), with integer matrices R, c0 = 1/(4J^2).
Instruments (Alice = Bob): P_{0|x} = sum_j |phi_j^x><phi_j^x| (x) |j><j|,  phi_j^x = (c_j, (-1)^(x+1) s_j),
          P_{1|x} = 1 - P_{0|x};  Lueders instrument with the setting written into the register:
          Choi M_{a|x} = |v_{a,x}><v_{a,x}|,  v_{a,x}[(i),(o),(r)] = P_{a|x}[o,i] * delta_{r,x}.

Checks (all exact):
 (1) Hermiticity type of every R (R symmetric if m even, antisymmetric if m odd); every pair has m_a+m_b even,
     so W is real symmetric.
 (2) PROCESS VALIDITY: every R is 'pattern-pure' (exactly one of its four Hilbert-Schmidt components
     [1(x)1, X(x)1, 1(x)Y, rest] is non-zero; computed with exact integer partial traces) and every product pattern
     (A_I, A_O, B_I, B_O) of a (x) b and b (x) a is allowed:  A_O => (B_I and not B_O),  B_O => (A_I and not A_O).
     Hence W lies in the valid-process subspace; non-identity terms are traceless, so Tr W = c0 * dim = d_AO*d_BO.
 (3) BLOCK STRUCTURE: every R maps each class {register value, label-charge sector} of its party into itself, so W
     is block diagonal over (class_A, class_B).
 (4) POSITIVITY: EVERY block of the integer matrix 4J^2 * D * 2^k * W is positive definite (Sylvester's criterion,
     fraction-free Bareiss elimination, exact integers).  (No symmetry argument is used.)
 (5) INSTRUMENT VALIDITY: c_j^2 + s_j^2 = 1, P_{a|x} symmetric idempotent, P_0+P_1 = 1, and
     Tr_{A_O}(M_{0|x} + M_{1|x}) = 1_{A_I} exactly; M_{a|x} = |v><v| >= 0.
 (6) VALUE: I_GYNI = 1/4 sum_{x,y} Tr[W (M_{y|x} (x) M_{x|y})] computed exactly.
"""
import sys, time, argparse
from fractions import Fraction as Fr
import numpy as np


def bareiss_pd(M):
    """M: list of lists of Python ints (symmetric). True iff all leading principal minors > 0."""
    n = len(M)
    A = [row[:] for row in M]
    prev = 1
    for k in range(n):
        piv = A[k][k]
        if piv <= 0:
            return False
        rk = A[k]
        for i in range(k + 1, n):
            ri = A[i]
            aik = ri[k]
            for j in range(k + 1, n):
                ri[j] = (ri[j] * piv - aik * rk[j]) // prev
            ri[k] = 0
        prev = piv
    return True


def allowed(pat):
    AI, AO, BI, BO = pat
    if AO and not (BI and not BO):
        return False
    if BO and not (AI and not AO):
        return False
    return True


def main(path, quick=False):
    t0 = time.time()
    Z = np.load(path)
    J = int(Z['J']); R = Z['R'].astype(np.int64); mim = Z['mim']; pairs = Z['pairs']; y = Z['y']
    D = int(Z['D']); k = int(Z['k']); K = 2 ** k
    # (0) overflow guard: all int64 intermediates below are bounded rigorously (Python-int arithmetic) before use.
    maxR = max(abs(int(v)) for v in R.flat)
    sumy = sum(abs(int(v)) for v in y)
    bound_S = sumy * 2 * maxR * maxR                     # |S_ij| <= sum_t |y_t| * (|kron| + |kron|)
    bound_tr = (2 * J) * (4 * J) * maxR * 3 + (2 * J) * (4 * J) * maxR   # partial traces / 'rest' matrix entries
    assert bound_S < 2 ** 62 and bound_tr < 2 ** 62, ('int64 overflow possible', bound_S, bound_tr)
    print(f"(0) int64 overflow guard: max|R|={maxR}, sum|y| < 2^{sumy.bit_length()}, |S| <= 2^{bound_S.bit_length()} < 2^62: OK")
    cs = [(Fr(int(a), int(b)), Fr(int(c), int(d))) for a, b, c, d in zip(Z['c_num'], Z['c_den'], Z['s_num'], Z['s_den'])]
    dI, dO = 2 * J, 4 * J
    n = dI * dO
    npo = R.shape[0]
    print(f"[certificate] J={J}: party dims A_I={dI}, A_O={dO}; {npo} party operators, {len(pairs)} terms, D=2^{D.bit_length()-1}, k={k}")
    ok = True

    # (1) Hermiticity type + real product
    for e in range(npo):
        if mim[e] % 2 == 0:
            ok_e = np.array_equal(R[e], R[e].T)
        else:
            ok_e = np.array_equal(R[e], -R[e].T)
        if not ok_e:
            print("  FAIL (1): Hermiticity type of party operator", e); ok = False
    for (a, b) in pairs:
        if (mim[a] + mim[b]) % 2:
            print("  FAIL (1): non-real pair", a, b); ok = False
    print(f"(1) Hermiticity/realness: {ok}"); ok_all = ok; ok = True

    # (2) pattern purity and allowed patterns (exact integer partial traces)
    pat = []
    for e in range(npo):
        X = R[e].reshape(dI, dO, dI, dO)
        T = int(np.trace(R[e]))
        RI = np.einsum('iojo->ij', X)          # Tr_{A_O}
        RO = np.einsum('ioip->op', X)          # Tr_{A_I}
        c00 = T != 0
        c10 = not np.array_equal(dI * RI, T * np.eye(dI, dtype=np.int64))
        c01 = not np.array_equal(dO * RO, T * np.eye(dO, dtype=np.int64))
        rest = dI * dO * R[e] - dI * np.kron(RI, np.eye(dO, dtype=np.int64)) - dO * np.kron(np.eye(dI, dtype=np.int64), RO) \
            + T * np.eye(n, dtype=np.int64)
        c11 = np.any(rest != 0)
        comps = [c00, c10, c01, c11]
        if sum(comps) != 1:
            print(f"  FAIL (2): party operator {e} not pattern-pure {comps}"); ok = False
        pat.append((bool(c10 or c11), bool(c01 or c11)))
    for (a, b) in pairs:
        for (u, v) in ((a, b), (b, a)):
            p = (pat[u][0], pat[u][1], pat[v][0], pat[v][1])
            if not any(p) or not allowed(p):
                print(f"  FAIL (2): forbidden pattern {p} for pair {(a, b)}"); ok = False
    c0 = Fr(1, 4 * J * J)
    ok_tr = (c0 * n * n == dO * dO)
    print(f"(2) validity (pattern-pure terms, allowed patterns): {ok}; Tr W = c0*dim = {c0 * n * n} = d_AO d_BO: {ok_tr}")
    ok &= ok_tr; ok_all &= ok; ok = True

    # (3) block structure
    idx = np.arange(n)
    q_in = idx // (J * 2 * J * 2); rem = idx % (J * 2 * J * 2)
    l_in = rem // (2 * J * 2); rem = rem % (2 * J * 2)
    q_out = rem // (J * 2); rem = rem % (J * 2)
    l_out = rem // 2; reg = rem % 2
    cls = {}
    for i in range(n):
        key = (int(reg[i]), 0) if l_in[i] == l_out[i] else (int(reg[i]), (int(l_in[i]), int(l_out[i])))
        cls.setdefault(key, []).append(i)
    classes = [np.array(v) for key, v in sorted(cls.items(), key=lambda kv: str(kv[0]))]
    cl_of = np.empty(n, dtype=np.int64)
    for c, ind in enumerate(classes):
        cl_of[ind] = c
    for e in range(npo):
        r_, c_ = np.nonzero(R[e])
        if np.any(cl_of[r_] != cl_of[c_]):
            print(f"  FAIL (3): party operator {e} not block diagonal"); ok = False
    print(f"(3) block structure: {ok}  ({len(classes)} classes per party, {len(classes)**2} blocks of W)"); ok_all &= ok; ok = True

    # (4) positivity of every block (exact)
    ph = np.array([(-1) ** ((int(mim[a]) + int(mim[b])) // 2) for (a, b) in pairs], dtype=np.int64)
    nblk = 0
    tb = time.time()
    blocks = [(ca, cb) for ca in range(len(classes)) for cb in range(len(classes))]
    if quick:
        blocks = [(ca, cb) for (ca, cb) in blocks if ca <= cb]
    for (ca, cb) in blocks:
        ia, ib = classes[ca], classes[cb]
        S = np.zeros((len(ia) * len(ib),) * 2, dtype=np.int64)
        for t, (a, b) in enumerate(pairs):
            if y[t] == 0:
                continue
            Ra, Rb = R[a], R[b]
            term = np.kron(Ra[np.ix_(ia, ia)], Rb[np.ix_(ib, ib)])
            if a != b:
                term = term + np.kron(Rb[np.ix_(ia, ia)], Ra[np.ix_(ib, ib)])
            if term.any():
                S += int(y[t]) * int(ph[t]) * term
        m_ = S.shape[0]
        big = 4 * J * J * (K - 1)
        Ml = [[big * int(S[i, j]) for j in range(m_)] for i in range(m_)]
        for i in range(m_):
            Ml[i][i] += D * K
        if not bareiss_pd(Ml):
            print(f"  FAIL (4): block {(ca, cb)} not positive definite"); ok = False
        nblk += 1
    print(f"(4) positivity: {nblk} integer blocks checked exactly -> all PD: {ok}  ({time.time()-tb:.0f}s)"); ok_all &= ok; ok = True

    # (5) instruments
    P = {}
    for x in (0, 1):
        P0 = [[Fr(0)] * dI for _ in range(dI)]
        for j, (c, s) in enumerate(cs):
            if c * c + s * s != 1:
                print("  FAIL (5): c^2+s^2 != 1"); ok = False
            ph_ = (c, s if x == 1 else -s)
            for qa in range(2):
                for qb in range(2):
                    P0[qa * J + j][qb * J + j] = ph_[qa] * ph_[qb]
        P1 = [[(1 if i == j else 0) - P0[i][j] for j in range(dI)] for i in range(dI)]
        P[(0, x)], P[(1, x)] = P0, P1
    mm = lambda A, B: [[sum(A[i][l] * B[l][j] for l in range(dI)) for j in range(dI)] for i in range(dI)]
    for key, Pm in P.items():
        if mm(Pm, Pm) != Pm or any(Pm[i][j] != Pm[j][i] for i in range(dI) for j in range(dI)):
            print("  FAIL (5): not a symmetric projector", key); ok = False
    V = {}
    for (a, x), Pm in P.items():
        v = {}
        for i in range(dI):
            for o in range(dI):
                if Pm[o][i] != 0:
                    v[(i * (2 * J) + o) * 2 + x] = Pm[o][i]
        V[(a, x)] = v
    for x in (0, 1):
        TrO = [[Fr(0)] * dI for _ in range(dI)]
        for a in (0, 1):
            v = V[(a, x)]
            for p1, w1 in v.items():
                i1, o1 = divmod(p1, dO)
                for p2, w2 in v.items():
                    i2, o2 = divmod(p2, dO)
                    if o1 == o2:
                        TrO[i1][i2] += w1 * w2
        if TrO != [[Fr(int(i == j)) for j in range(dI)] for i in range(dI)]:
            print("  FAIL (5): Tr_AO sum_a M_{a|x} != 1 for x =", x); ok = False
    print(f"(5) instruments (projectors, Lueders, trace condition exact): {ok}"); ok_all &= ok; ok = True

    # (6) exact value
    Rcoo = [np.nonzero(R[e]) for e in range(npo)]

    def quad(e, v):
        r_, c_ = Rcoo[e]
        tot = Fr(0)
        for i, j in zip(r_, c_):
            wi = v.get(int(i))
            if wi is None:
                continue
            wj = v.get(int(j))
            if wj is None:
                continue
            tot += wi * wj * int(R[e][i, j])
        return tot
    s_ = Fr(1, K)
    total = Fr(0)
    for x in (0, 1):
        for yy in (0, 1):
            vA, vB = V[(yy, x)], V[(x, yy)]          # Alice outputs a = y (setting x); Bob outputs b = x (setting y)
            nA = sum(w * w for w in vA.values()); nB = sum(w * w for w in vB.values())
            qa = {}; qb = {}
            acc = c0 * nA * nB
            for t, (a, b) in enumerate(pairs):
                for e in (a, b):
                    if e not in qa:
                        qa[e] = quad(e, vA); qb[e] = quad(e, vB)
                tt = qa[a] * qb[b]
                if a != b:
                    tt += qa[b] * qb[a]
                if tt:
                    acc += (1 - s_) * Fr(int(y[t]), D) * int(ph[t]) * tt
            total += acc / 4
    claimed = Fr(int(str(Z['claimed_value_num'])), int(str(Z['claimed_value_den'])))
    print(f"(6) exact GYNI value = {float(total):.12f}  (= stored claim: {total == claimed})")
    ok_all &= (total == claimed)
    print(f"RESULT: all checks passed = {ok_all};  I_GYNI >= {float(total):.12f}   [{time.time()-t0:.0f}s]")
    return ok_all, total


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("npz")
    ap.add_argument("--quick", action="store_true", help="check only blocks with class_A <= class_B (uses swap symmetry)")
    a = ap.parse_args()
    main(a.npz, a.quick)
