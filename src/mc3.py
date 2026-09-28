"""Moment hierarchy in the OBSERVABLE (dihedral) word basis.

O_x := P_{0|x} - P_{1|x} = 2 A_x - 1 (unitary involutions). Words = reduced words in the infinite dihedral group
Z2*Z2 (no two equal adjacent letters; O_x O_x = 1). The span of words of length <= L equals the span of the
idempotent words of length <= L, so every level has the same value as in mc2 (basis change only).
Word vectors |w,r> = (1 (x) w)|Phi> (x) |r>; Gamma = Gram matrix of the (Lueders normal form) process.
Trace functional of the pair (bra (w,r), ket (w',r')) is delta_{rr'} w^{-1} w' (a group element); the FREE group
algebra C[Z2*Z2] is isomorphic to the free algebra of two idempotents, so identities hold in every realisation.
"""
import os, sys, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sp
from mc2 import Party, BlockMoment, all_words


def red(w):
    out = []
    for c in w:
        if out and out[-1] == c:
            out.pop()          # O_x O_x = 1
        else:
            out.append(c)
    return tuple(out)


def wmul(w1, w2):
    return red(tuple(w1) + tuple(w2))


def inv(w):
    return tuple(reversed(w))


def pmul(p, q):
    out = {}
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = wmul(w1, w2)
            out[w] = out.get(w, 0.0) + c1 * c2
    return {w: c for w, c in out.items() if c != 0}


def Pw(a, x):
    """P_{a|x} = (1 + (-1)^a O_x)/2"""
    return {(): 0.5, (x,): 0.5 if a == 0 else -0.5}


class OParty(Party):
    def vec(self, poly, r):
        out = {}
        for w, c in poly.items():
            key = (red(w), r)
            if key not in self.index:
                raise KeyError(f"word {key} not in basis")
            i = self.index[key]
            out[i] = out.get(i, 0.0) + c
        return {i: c for i, c in out.items() if c != 0}

    def tword(self, k, kp):
        (w, r), (wp, rp) = self.basis[k], self.basis[kp]
        if r != rp:
            return None
        return wmul(inv(w), wp)


def v2_rows(M):
    """Word-level validity rows (TA x TP and TP x TA, normalisation) in the dihedral basis."""
    A, B = M.A, M.B

    def classes(P):
        groups = {}
        for k in range(P.n):
            for kp in range(P.n):
                t = P.tword(k, kp)
                if t is None:
                    continue
                groups.setdefault(t, []).append((k, kp))
        TA = []
        for t, lst in groups.items():
            for p in lst[1:]:
                TA.append(((lst[0], 1.0), (p, -1.0)))
        rep = groups[()][0]
        return TA, rep

    TA_A, repA = classes(A)
    TA_B, repB = classes(B)
    TP_B = TA_B + [((repB, 1.0),)]
    cons = {}

    def add(c, d, rhs):
        row = {}
        for (pa, ca) in c:
            for (pb, cb) in d:
                (k, kp), (l, lp) = pa, pb
                v = M.entry(k, l, kp, lp)
                if v is None:
                    continue
                row[v] = row.get(v, 0.0) + ca * cb
        row = {v: c for v, c in row.items() if c != 0}
        if not row:
            if rhs != 0:
                raise ValueError("inconsistent")
            return
        items = sorted(row.items())
        s = items[0][1]
        key = tuple((v, c / s) for v, c in items) + (rhs / s,)
        cons[key] = (row, rhs)

    for c in TA_A:
        for d in TP_B:
            add(c, d, 0.0)
    for d in TA_B:
        add(((repA, 1.0),), d, 0.0)
    add(((repA, 1.0),), ((repB, 1.0),), 1.0)
    return list(cons.values())


def objective(M, coef):
    A, B = M.A, M.B
    obj = {}
    for a in (0, 1):
        for b in (0, 1):
            for x in range(A.nset):
                for y in range(B.nset):
                    w = coef[a][b][x][y]
                    if w == 0:
                        continue
                    u = A.vec(Pw(a, x), x)
                    v = B.vec(Pw(b, y), y)
                    M.bilinear(u, v, u, v, scale=w, out=obj)
    return obj


def prob_expr(M, a, b, x, y):
    u = M.A.vec(Pw(a, x), x)
    v = M.B.vec(Pw(b, y), y)
    return M.bilinear(u, v, u, v)


# ---------------- GYNI symmetry (signed permutations) ----------------

def party_signed_perm(P, letter_map, sign_flip, reg_perm):
    """Transformed basis vector j = sign * basis vector perm[j].  letter_map: dict letter->letter;
    sign_flip: if True, O -> -O (each letter contributes -1)."""
    perm = np.zeros(P.n, dtype=np.int64)
    sign = np.zeros(P.n)
    for j, (w, r) in enumerate(P.basis):
        w2 = tuple(letter_map[c] for c in w)
        s = (-1.0) ** len(w) if sign_flip else 1.0
        perm[j] = P.index[(red(w2), reg_perm[r])]
        sign[j] = s
    return perm, sign


def group_maps(M):
    """Returns dict name -> (permA, signA, permB, signB, swap) for fx, fy, swap."""
    A, B = M.A, M.B
    sw = {0: 1, 1: 0}; idl = {0: 0, 1: 1}
    fx = party_signed_perm(A, sw, False, [1, 0]) + party_signed_perm(B, idl, True, [0, 1]) + (False,)
    fy = party_signed_perm(A, idl, True, [0, 1]) + party_signed_perm(B, sw, False, [1, 0]) + (False,)
    return dict(fx=fx, fy=fy)


def map_rows(M, g):
    """rows z_target - sign * z_source = 0 expressing invariance under a signed-permutation group element
    (Gamma' [(k,l),(k',l')] = sA(k) sB(l) sA(k') sB(l') Gamma[(pA(k),pB(l)),(pA(k'),pB(l'))])."""
    pA, sA, pB, sB, _ = g
    rows = []
    A, B = M.A, M.B
    for (rA, rB, nsz, off) in M.blocks:
        ks = A.reg_members[rA]; ls = B.reg_members[rB]
        nl = len(ls)
        for jj in range(nsz):
            for ii in range(jj + 1):
                k, l = ks[ii // nl], ls[ii % nl]
                kp, lp = ks[jj // nl], ls[jj % nl]
                v0 = off + jj * (jj + 1) // 2 + ii
                src = M.entry(pA[k], pB[l], pA[kp], pB[lp])
                s = sA[k] * sB[l] * sA[kp] * sB[lp]
                if src == v0:
                    if s == 1.0:
                        continue
                    rows.append(({v0: 2.0}, 0.0))       # z = -z -> z = 0
                else:
                    rows.append(({v0: 1.0, src: -s}, 0.0))
    return rows


def swap_rows(M):
    A, B = M.A, M.B
    assert A.basis == B.basis
    rows = []
    for (rA, rB, nsz, off) in M.blocks:
        ks = A.reg_members[rA]; ls = B.reg_members[rB]
        nl = len(ls)
        for jj in range(nsz):
            for ii in range(jj + 1):
                k, l = ks[ii // nl], ls[ii % nl]
                kp, lp = ks[jj // nl], ls[jj % nl]
                v0 = off + jj * (jj + 1) // 2 + ii
                src = M.entry(l, k, lp, kp)
                if src != v0:
                    rows.append(({v0: 1.0, src: -1.0}, 0.0))
    return rows


def block_signed_perm_from00(M, block):
    """For symmetric points: Gamma_block[i,j] = s_i s_j Gamma_00[pi(i), pi(j)].  Returns (pi, s) over block indices."""
    A, B = M.A, M.B
    gm = group_maps(M)
    rA, rB = block
    # compose: block (rA,rB) = fx^{rA} fy^{rB} (block 00) ; for an index (k,l) of block (rA,rB) the source index is
    # obtained by applying the maps' (perm, sign) successively.
    ks = A.reg_members[rA]; ls = B.reg_members[rB]
    ks0 = A.reg_members[0]; ls0 = B.reg_members[0]
    pos0 = {(k, l): i for i, (k, l) in enumerate((k, l) for k in ks0 for l in ls0)}
    pi = []; s = []
    for k in ks:
        for l in ls:
            kk, ll, sg = k, l, 1.0
            if rA == 1:
                pA, sA, pB, sB, _ = gm['fx']
                sg *= sA[kk] * sB[ll]; kk, ll = pA[kk], pB[ll]
            if rB == 1:
                pA, sA, pB, sB, _ = gm['fy']
                sg *= sA[kk] * sB[ll]; kk, ll = pA[kk], pB[ll]
            pi.append(pos0[(kk, ll)]); s.append(sg)
    return np.array(pi), np.array(s)


def build(L, game="gyni", sym=True, verbose=True):
    t0 = time.time()
    ws = all_words(2, L)
    A = OParty(2, [ws, ws]); B = OParty(2, [ws, ws])
    M = BlockMoment(A, B)
    rows = v2_rows(M)
    nv2 = len(rows)
    if sym:
        gm = group_maps(M)
        rows += map_rows(M, gm['fx']) + map_rows(M, gm['fy']) + swap_rows(M)
    import mc2
    coef = {"gyni": mc2.gyni_coef(), "lgyni": mc2.lgyni_coef()}[game]
    obj = objective(M, coef)
    if verbose:
        print(f"[mc3 build L={L}] words {len(ws)}, blocks {[b[2] for b in M.blocks]}, vars {M.nvar}, "
              f"V2 rows {nv2}, total rows {len(rows)}  ({time.time()-t0:.1f}s)", flush=True)
    return M, rows, obj


def swap_split(M):
    """Orthonormal Q_plus, Q_minus for block (0,0) under (k,l) <-> (l,k)."""
    A, B = M.A, M.B
    ks = A.reg_members[0]; ls = B.reg_members[0]
    idx = [(k, l) for k in ks for l in ls]
    pos = {p: i for i, p in enumerate(idx)}
    n = len(idx)
    plus, minus = [], []
    seen = set()
    for i, (k, l) in enumerate(idx):
        j = pos[(l, k)]
        if i in seen:
            continue
        seen.add(i); seen.add(j)
        if i == j:
            e = np.zeros(n); e[i] = 1; plus.append(e)
        else:
            e = np.zeros(n); e[i] = e[j] = 1 / np.sqrt(2); plus.append(e)
            f = np.zeros(n); f[i] = 1 / np.sqrt(2); f[j] = -1 / np.sqrt(2); minus.append(f)
    return np.array(plus).T, np.array(minus).T


def psd_block00_split(M):
    """PSD cone data for block (0,0) in the swap-split basis: list of (n, terms, F0)."""
    rA, rB, nsz, off = M.blocks[0]
    assert (rA, rB) == (0, 0)
    Qp, Qm = swap_split(M)
    res = []
    for Q in (Qp, Qm):
        m = Q.shape[1]
        terms = []
        for j in range(nsz):
            for i in range(j + 1):
                v = off + j * (j + 1) // 2 + i
                if i == j:
                    F = np.outer(Q[i], Q[i])
                else:
                    F = np.outer(Q[i], Q[j]) + np.outer(Q[j], Q[i])
                if np.abs(F).max() > 1e-14:
                    F[np.abs(F) < 1e-15] = 0.0
                    terms.append((v, sp.csr_matrix(F)))
        res.append((m, terms, sp.csr_matrix((m, m))))
    return res, (Qp, Qm)
