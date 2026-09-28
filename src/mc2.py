"""General moment + canonical-image relaxation ("MC") for bipartite causal games with binary outcomes.

Parties: Alice has nA settings, Bob nB settings, outcomes in {0,1}.
WLOG strategy form (see REPORT.md, Lemma 1): projective measurements A_x = P_{0|x} on H_A, Lueders instrument,
setting copied to an output register X of dim nA.  Word vectors |w,r> = (1 (x) w)|Phi> (x) |r>.
Gamma = Gram matrix of W on word vectors; WLOG real and block diagonal in (r_A, r_B)
(twirl of the output registers).  Blocks: Gamma_{rA,rB} over (Alice words of register rA) x (Bob words of rB).

Constraints
 V1  every Gamma block PSD
 V2  Tr[W (L_A (x) L_B)] = 0 for L_A trace-annihilating, L_B trace-proportional (and A<->B); = 1 for TP x TP.
     Trace functional of the pair (bra (w,r), ket (w',r)) is w^dag w' in the free algebra of nA (resp. nB)
     idempotents (words: no two equal adjacent letters).
 V3  for every trigger pair (xi,eta): the Liu-Chiribella canonical process W'_{xi,eta} (qubit input,
     qubit O1 + register output per party) is a linear image of Gamma; it must be PSD (blockwise in the
     registers) and satisfy the process-validity linear conditions (forbidden Pauli components vanish,
     Tr = d_AO d_BO).
"""
import os, sys, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sp
from pm_core import allowed, pauli_string

# ---------------- word algebra ----------------

def red(w):
    out = []
    for c in w:
        if out and out[-1] == c:
            continue
        out.append(c)
    return tuple(out)


def wmul(w1, w2):
    return red(tuple(w1) + tuple(w2))


def adj(w):
    return tuple(reversed(w))


def pmul(p, q):
    out = {}
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = wmul(w1, w2)
            out[w] = out.get(w, 0.0) + c1 * c2
    return {w: c for w, c in out.items() if c != 0}


def Pw(a, x):
    return {(x,): 1.0} if a == 0 else {(): 1.0, (x,): -1.0}


def all_words(n, maxlen):
    out = [()]
    cur = [()]
    for L in range(1, maxlen + 1):
        nxt = []
        for w in cur:
            for c in range(n):
                if not w or w[-1] != c:
                    nxt.append(w + (c,))
        out += nxt
        cur = nxt
    return out


def canonical_words(n, r):
    """words needed by the LC canonical images for register r"""
    ws = [(), (r,)]
    for xi in range(n):
        if xi != r:
            ws += [(xi,), (r, xi)]
    return ws


class Party:
    def __init__(self, nset, words_by_reg):
        self.nset = nset
        self.words_by_reg = [list(dict.fromkeys(tuple(w) for w in ws)) for ws in words_by_reg]
        self.basis = [(w, r) for r in range(nset) for w in self.words_by_reg[r]]
        self.index = {b: i for i, b in enumerate(self.basis)}
        self.n = len(self.basis)
        self.reg = np.array([r for (w, r) in self.basis])
        self.reg_members = [[i for i, (w, r) in enumerate(self.basis) if r == rr] for rr in range(nset)]
        self.pos_in_reg = {}
        for rr in range(nset):
            for j, i in enumerate(self.reg_members[rr]):
                self.pos_in_reg[i] = j

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
        return wmul(adj(w), wp)


class BlockMoment:
    """Gamma = direct sum over (rA,rB) of real symmetric blocks; variables = upper triangles."""

    def __init__(self, A, B):
        self.A, self.B = A, B
        self.blocks = []  # (rA, rB, size, var_offset)
        self.var_base = {}
        off = 0
        for rA in range(A.nset):
            for rB in range(B.nset):
                nsz = len(A.reg_members[rA]) * len(B.reg_members[rB])
                self.blocks.append((rA, rB, nsz, off))
                self.var_base[(rA, rB)] = (off, nsz)
                off += nsz * (nsz + 1) // 2
        self.nvar = off

    def local_index(self, k, l):
        A, B = self.A, self.B
        return A.pos_in_reg[k] * len(B.reg_members[B.reg[l]]) + B.pos_in_reg[l]

    def entry(self, k, l, kp, lp):
        A, B = self.A, self.B
        if A.reg[k] != A.reg[kp] or B.reg[l] != B.reg[lp]:
            return None
        off, nsz = self.var_base[(int(A.reg[k]), int(B.reg[l]))]
        i, j = self.local_index(k, l), self.local_index(kp, lp)
        if i > j:
            i, j = j, i
        # upper-triangle column-major-free indexing: row i, col j (i<=j): index = j*(j+1)/2 + i
        return off + j * (j + 1) // 2 + i

    def bilinear(self, uA, uB, vA, vB, scale=1.0, out=None):
        out = {} if out is None else out
        for k, ck in uA.items():
            for l, cl in uB.items():
                for kp, ckp in vA.items():
                    for lp, clp in vB.items():
                        v = self.entry(k, l, kp, lp)
                        if v is None:
                            continue
                        out[v] = out.get(v, 0.0) + scale * ck * cl * ckp * clp
        return out

    def block_psd_terms(self):
        """list of (n, terms, F0) for each Gamma block"""
        res = []
        for (rA, rB, nsz, off) in self.blocks:
            terms = []
            for j in range(nsz):
                for i in range(j + 1):
                    v = off + j * (j + 1) // 2 + i
                    if i == j:
                        E = sp.csr_matrix(([1.0], ([i], [i])), shape=(nsz, nsz))
                    else:
                        E = sp.csr_matrix(([1.0, 1.0], ([i, j], [j, i])), shape=(nsz, nsz))
                    terms.append((v, E))
            res.append((nsz, terms, sp.csr_matrix((nsz, nsz))))
        return res

    def gamma_blocks_from_z(self, z):
        out = {}
        for (rA, rB, nsz, off) in self.blocks:
            G = np.zeros((nsz, nsz))
            for j in range(nsz):
                for i in range(j + 1):
                    G[i, j] = G[j, i] = z[off + j * (j + 1) // 2 + i]
            out[(rA, rB)] = G
        return out


# ---------------- V2 ----------------

def v2_constraints(M):
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
                TA.append([(lst[0], 1.0), (p, -1.0)])
        rep = groups[()][0]
        return TA, TA + [[(rep, 1.0)]], rep

    TA_A, TP_A, repA = classes(A)
    TA_B, TP_B, repB = classes(B)
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
        row = {v: c for v, c in row.items() if abs(c) > 1e-15}
        if not row:
            if abs(rhs) > 0:
                raise ValueError("inconsistent")
            return
        items = sorted(row.items())
        s = items[0][1]
        key = tuple((v, round(c / s, 12)) for v, c in items) + (round(rhs / s, 12),)
        cons[key] = (row, rhs)

    for c in TA_A:
        for d in TP_B:
            add(c, d, 0.0)
    for d in TA_B:
        add([(repA, 1.0)], d, 0.0)
    add([(repA, 1.0)], [(repB, 1.0)], 1.0)
    return list(cons.values())


# ---------------- V3: canonical images ----------------

def eff(P, xi, i, o, r, ip, op):
    """effective Choi of canonical |c><c'| (c=(i,o,r), c'=(ip,op,r)) for trigger xi: list of (ket, bra, coef)"""
    if r == xi:
        if o != op:
            return []
        return [(P.vec(Pw(i, xi), xi), P.vec(Pw(ip, xi), xi), 1.0)]
    if (o ^ i) != (op ^ ip):
        return []
    return [(P.vec(pmul(Pw(a2, r), Pw(i, xi)), r), P.vec(pmul(Pw(a2, r), Pw(ip, xi)), r), 1.0)
            for a2 in (0, 1)]


def canonical_image(M, xi, eta):
    """dict (rA,rB) -> 16x16 nested list of dicts var->coef for <c'|W'|c>, c=(iA,oA,iB,oB) (iA MSB)."""
    A, B = M.A, M.B
    blocks = {}
    for rA in range(A.nset):
        for rB in range(B.nset):
            E = [[None] * 16 for _ in range(16)]
            for c in range(16):
                iA, oA, iB, oB = (c >> 3) & 1, (c >> 2) & 1, (c >> 1) & 1, c & 1
                for cp in range(16):
                    ipA, opA, ipB, opB = (cp >> 3) & 1, (cp >> 2) & 1, (cp >> 1) & 1, cp & 1
                    d = {}
                    for (kA, bA, cA) in eff(A, xi, iA, oA, rA, ipA, opA):
                        for (kB, bB, cB) in eff(B, eta, iB, oB, rB, ipB, opB):
                            M.bilinear(bA, bB, kA, kB, scale=cA * cB, out=d)
                    E[cp][c] = {v: x for v, x in d.items() if abs(x) > 1e-15}
            blocks[(rA, rB)] = E
    return blocks


def nqubits(n):
    q = 0
    while (1 << q) < n:
        q += 1
    assert (1 << q) == n, "register dimension must be a power of 2"
    return q


def image_validity_constraints(M, blocks):
    """Forbidden-Pauli-component equalities + trace normalisation for a register-diagonal real canonical
    process given by its blocks (dict (rA,rB)->16x16 of dicts). Qubit order: [AI, O1A, regA..., BI, O1B, regB...]."""
    A, B = M.A, M.B
    qa, qb = nqubits(A.nset), nqubits(B.nset)
    # groups: AI=[0], AO=[1..1+qa], BI=[2+qa], BO=[3+qa .. 3+qa+qb]
    nq = 4 + qa + qb
    grp = [0] + [1] * (1 + qa) + [2] + [3] * (1 + qb)
    regA_q = list(range(2, 2 + qa)); regB_q = list(range(4 + qa, 4 + qa + qb))
    rest_q = [0, 1, 2 + qa, 3 + qa]
    dAO, dBO = 2 * A.nset, 2 * B.nset
    rows = []
    # precompute block expressions as sparse over vars: for each (rA,rB): list over (cp,c)
    for s in itertools.product(range(4), repeat=nq):
        if any(s[q] in (1, 2) for q in regA_q + regB_q):
            continue
        if sum(1 for t in s if t == 2) % 2 == 1:
            continue
        pat = [False] * 4
        for q, t in enumerate(s):
            if t != 0:
                pat[grp[q]] = True
        is_id = not any(pat)
        if not is_id and allowed(pat):
            continue
        Mrest = pauli_string([s[q] for q in rest_q]).real  # 16x16 real
        row = {}
        for rA in range(A.nset):
            for rB in range(B.nset):
                sign = 1.0
                for idx, q in enumerate(regA_q):
                    bit = (rA >> (qa - 1 - idx)) & 1
                    if s[q] == 3 and bit:
                        sign = -sign
                for idx, q in enumerate(regB_q):
                    bit = (rB >> (qb - 1 - idx)) & 1
                    if s[q] == 3 and bit:
                        sign = -sign
                E = blocks[(rA, rB)]
                # Tr[B sigma] = sum_{cp,c} B[cp,c] sigma[c,cp]
                for cp in range(16):
                    for c in range(16):
                        sv = Mrest[c, cp]
                        if sv == 0:
                            continue
                        for v, x in E[cp][c].items():
                            row[v] = row.get(v, 0.0) + sign * sv * x
        row = {v: x for v, x in row.items() if abs(x) > 1e-13}
        rhs = float(dAO * dBO) if is_id else 0.0
        if row or rhs != 0:
            rows.append((row, rhs))
    return rows


def image_psd_terms(blocks):
    """PSD constraint data for each image block: (16, terms, F0)."""
    res = []
    for key, E in blocks.items():
        acc = {}
        for cp in range(16):
            for c in range(16):
                for v, x in E[cp][c].items():
                    acc.setdefault(v, []).append((cp, c, x))
        terms = []
        for v, lst in acc.items():
            r_ = [t[0] for t in lst]; c_ = [t[1] for t in lst]; d_ = [t[2] for t in lst]
            F = sp.csr_matrix((d_, (r_, c_)), shape=(16, 16))
            F = (F + F.T) * 0.5  # symmetric (image blocks are symmetric for real symmetric Gamma)
            terms.append((v, F))
        res.append((16, terms, sp.csr_matrix((16, 16))))
    return res


def objective(M, coef):
    """coef[a][b][x][y] (x in [nA], y in [nB])"""
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


# ---------------- assembly ----------------

def build_system(A, B, use_canon=True, use_v2=True, extra_images=None, verbose=True, use_gamma_psd=True):
    """Returns dict with M, eq rows (list of (dict, rhs)), psd list [(n, terms, F0)]."""
    t0 = time.time()
    M = BlockMoment(A, B)
    eqs = []
    if use_v2:
        eqs += v2_constraints(M)
    psd = M.block_psd_terms() if use_gamma_psd else []
    nimg = 0
    if use_canon:
        for xi in range(A.nset):
            for eta in range(B.nset):
                blocks = canonical_image(M, xi, eta)
                eqs += image_validity_constraints(M, blocks)
                psd += image_psd_terms(blocks)
                nimg += 1
    if extra_images:
        for blocks, validity_rows in extra_images(M):
            eqs += validity_rows
            psd += image_psd_terms(blocks)
    if verbose:
        print(f"[build] Gamma blocks {[b[2] for b in M.blocks]}, vars {M.nvar}, eq rows {len(eqs)}, "
              f"psd cones {len(psd)}, images {nimg}, {time.time()-t0:.1f}s", flush=True)
    return dict(M=M, eqs=eqs, psd=psd)


def independent_rows(rows, nvar, tol=1e-10):
    import scipy.linalg as sla
    m = len(rows)
    A = np.zeros((nvar, m))
    for i, (d, rhs) in enumerate(rows):
        for v, c in d.items():
            A[v, i] += c
    R, piv = sla.qr(A, mode='r', pivoting=True, overwrite_a=True, check_finite=False)
    diag = np.abs(np.diag(R))
    rank = int(np.sum(diag > tol * diag[0]))
    keep = sorted(piv[:rank])
    return [rows[i] for i in keep]


def make_sdp(system, obj, reduce=True, extra_eqs=None, extra_ineqs=None):
    from sdp_sparse import SDP
    M = system['M']
    sdp = SDP()
    sdp.add_vars(M.nvar)
    rows = list(system['eqs']) + list(extra_eqs or [])
    if reduce:
        rows = independent_rows(rows, M.nvar)
    for row, rhs in rows:
        sdp.add_eq(row, rhs)
    for (n, terms, F0) in system['psd']:
        sdp.add_psd(n, terms, F0)
    for (coef, const) in (extra_ineqs or []):
        sdp.add_ineq(coef, const)
    sdp.set_objective_min({k: -v for k, v in obj.items()})
    return sdp


def gyni_coef(nA=2, nB=2):
    c = np.zeros((2, 2, nA, nB))
    for x in (0, 1):
        for y in (0, 1):
            c[y, x, x, y] = 0.25
    return c


def lgyni_coef():
    c = np.zeros((2, 2, 2, 2))
    for a in (0, 1):
        for b in (0, 1):
            for x in (0, 1):
                for y in (0, 1):
                    if ((x == 0) or (a == y)) and ((y == 0) or (b == x)):
                        c[a, b, x, y] = 0.25
    return c


def ocb_coef():
    """OCB game: Alice x in {0,1}; Bob setting yy = 2*b' + y (b' selects who guesses).
    success: b'=0 -> b == x ; b'=1 -> a == y.  p = (1/2)[p(b=x|b'=0)+p(a=y|b'=1)], x,y uniform.
    causal bound 3/4, quantum (2+sqrt2)/4."""
    c = np.zeros((2, 2, 2, 4))
    for x in (0, 1):
        for y in (0, 1):
            for bp in (0, 1):
                yy = 2 * bp + y
                for a in (0, 1):
                    for b in (0, 1):
                        ok = (b == x) if bp == 0 else (a == y)
                        if ok:
                            c[a, b, x, yy] += 1.0 / 8.0
    return c
