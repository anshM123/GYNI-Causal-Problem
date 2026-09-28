"""GYNI symmetry group acting on the moment matrix (as linear equalities z_g = z).
Generators (all are symmetries of the set of strategies in Lueders form AND of the GYNI objective):
  s_swap : Alice <-> Bob                    (p(a,b|x,y) -> p(b,a|y,x))
  s_fx   : x -> 1-x on Alice (letters A_0<->A_1, register r -> 1-r) together with b -> 1-b (B_y -> 1 - B_y)
  s_fy   : y -> 1-y on Bob, together with a -> 1-a.
Letter substitutions are automorphisms of the free idempotent algebra, so V2 is mapped to itself."""
import numpy as np
import mc2


def party_transform(P, letter_map, reg_perm):
    """T (n x n): column j = expansion of transformed basis vector j.
    letter_map: dict letter -> polynomial (dict word->coef) ; reg_perm: list new register for old register."""
    n = P.n
    T = np.zeros((n, n))
    for j, (w, r) in enumerate(P.basis):
        poly = {(): 1.0}
        for c in w:
            poly = mc2.pmul(poly, letter_map[c])
        vec = P.vec(poly, reg_perm[r])
        for i, x in vec.items():
            T[i, j] += x
    return T


def gamma_map_rows(M, TA, TB, swap=False):
    """rows expressing z' - z = 0 where Gamma' = (TA (x) TB) Gamma (TA (x) TB)^T (optionally with party swap).
    Works blockwise. Returns list of (dict, 0.0)."""
    A, B = M.A, M.B
    rows = []
    # build full index lists
    for (rA, rB, nsz, off) in M.blocks:
        ks = A.reg_members[rA]; ls = B.reg_members[rB]
        # target entry (i,j) in block (rA,rB): Gamma'[(k,l),(k',l')] = sum TA[k,a]TB[l,b]TA[k',a']TB[l',b'] Gamma[(a,b),(a',b')]
        # (without swap).  With swap: Gamma'[(k,l),(k',l')] = Gamma[(l,k),(l',k')] (requires identical bases).
        for jj in range(nsz):
            for ii in range(jj + 1):
                k, l = ks[ii // len(ls)], ls[ii % len(ls)]
                kp, lp = ks[jj // len(ls)], ls[jj % len(ls)]
                row = {}
                if swap:
                    v = M.entry(l, k, lp, kp)
                    if v is not None:
                        row[v] = row.get(v, 0.0) + 1.0
                else:
                    # new basis vector k = sum_a T[a,k] |a>_old  =>  Gamma' = T^T Gamma T
                    colA = lambda kk: [(a, TA[a, kk]) for a in np.nonzero(TA[:, kk])[0]]
                    colB = lambda ll: [(b, TB[b, ll]) for b in np.nonzero(TB[:, ll])[0]]
                    for a_, ta in colA(k):
                        for b_, tb in colB(l):
                            for ap_, tap in colA(kp):
                                for bp_, tbp in colB(lp):
                                    v = M.entry(a_, b_, ap_, bp_)
                                    if v is None:
                                        continue
                                    row[v] = row.get(v, 0.0) + ta * tb * tap * tbp
                v0 = off + jj * (jj + 1) // 2 + ii
                row[v0] = row.get(v0, 0.0) - 1.0
                row = {v: c for v, c in row.items() if abs(c) > 1e-14}
                if row:
                    rows.append((row, 0.0))
    return rows


def gyni_symmetry_rows(M):
    A, B = M.A, M.B
    assert A.nset == 2 and B.nset == 2
    ident = {0: {(0,): 1.0}, 1: {(1,): 1.0}}
    swapl = {0: {(1,): 1.0}, 1: {(0,): 1.0}}
    compl = {0: {(): 1.0, (0,): -1.0}, 1: {(): 1.0, (1,): -1.0}}
    rows = []
    # s_fx: Alice letters swap + register flip; Bob complement letters, registers unchanged
    TA = party_transform(A, swapl, [1, 0]); TB = party_transform(B, compl, [0, 1])
    rows += gamma_map_rows(M, TA, TB)
    # s_fy
    TA = party_transform(A, compl, [0, 1]); TB = party_transform(B, swapl, [1, 0])
    rows += gamma_map_rows(M, TA, TB)
    # swap
    if A.basis == B.basis:
        rows += gamma_map_rows(M, None, None, swap=True)
    return rows
