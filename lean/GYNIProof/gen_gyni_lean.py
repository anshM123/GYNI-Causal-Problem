"""Generator for GYNIProof: reads iqoqi/programs/gyni/GYNI_J4_strategy_cert.npz and emits the Lean data files.

Steps (all checks exact, integers / fractions):
 1. Party operators R, pairs, coefficients as in verify_strategy.py.  Finds the 15 'A_I-only' operators
    R_s = X_s (x) 1_{A_O} (Tr X_s = 0); every pair contains one of them.  Hence
        2^71 W = 2^65 1 + (2^30 - 1) (T_A + T_B),
        T_A((a,b),(a',b')) = [o_a = o_a'] H(i_a,i_a')(b,b'),   T_B((a,b),(a',b')) = [o_b = o_b'] H(i_b,i_b')(a,a'),
    H(i,i') = sum_s X_s(i,i') G_s, G_s = sum over the pairs of s of (2 or 1) y_t ph_t R_other.
 2. Checks: H(i,i') = 0 unless label(i) = label(i'); sum_i H(i,i) = 0; H class preserving;
    H(i,i')(b,b') = H(i',i)(b',b); and T_A + T_B = 2 * S_cert on every one of the 676 blocks (S_cert = the integer
    matrix of verify_strategy.py), i.e. the Lean W equals the certificate's W.
 3. Block certificates (blocks cA <= cB): c A = L L^T + E with E diagonally dominant (L = rounded Cholesky
    factor of A - tau 1), verified exactly; packed-row identities verified exactly.
 4. Instrument parameters and the exact GYNI value (recomputed with the Lean formulas, compared with the claim).
Output: GYNIProof/Data.lean, GYNIProof/Cert*.lean, GYNIProof/Blocks.lean (assembly of the block theorems).
"""
import os, sys, time, math
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
NPZ = os.environ.get("GYNI_NPZ", os.path.join(HERE, "..", "..", "iqoqi", "programs", "gyni", "GYNI_J4_strategy_cert.npz"))
sys.set_int_max_str_digits(0)

Z = np.load(NPZ)
J = int(Z['J']); R = Z['R'].astype(np.int64); mim = Z['mim']; pairs = Z['pairs']; y = Z['y']
D = int(Z['D']); k = int(Z['k'])
assert J == 4 and D == 2 ** 40 and k == 30
dI, dO, n = 8, 16, 128
ph = [(-1) ** ((int(mim[a]) + int(mim[b])) // 2) for (a, b) in pairs]
for (a, b) in pairs:
    assert (int(mim[a]) + int(mim[b])) % 2 == 0

# ---------------------------------------------------------------- 1. H-form
def aionly(Re):
    X = Re.reshape(dI, dO, dI, dO)[:, 0, :, 0]
    return np.array_equal(np.kron(X, np.eye(dO, dtype=np.int64)), Re) and int(np.trace(X)) == 0, X
S = []; Xs = {}
for e in range(R.shape[0]):
    ok, X = aionly(R[e])
    if ok:
        S.append(e); Xs[e] = X
Sset = set(S)
assert len(S) == 15
G = {s: np.zeros((n, n), dtype=object) for s in S}
for t, (a, b) in enumerate(pairs):
    a = int(a); b = int(b); c = int(y[t]) * ph[t]
    if a == b:
        assert a in Sset
        G[a] = G[a] + c * R[a].astype(object)
    elif a in Sset:
        G[a] = G[a] + 2 * c * R[b].astype(object)
    else:
        assert b in Sset
        G[b] = G[b] + 2 * c * R[a].astype(object)
H = {}
for i in range(8):
    for ip in range(8):
        M = np.zeros((n, n), dtype=object)
        for s in S:
            if Xs[s][i, ip] != 0:
                M = M + int(Xs[s][i, ip]) * G[s]
        H[(i, ip)] = M

def lab(i): return i % 4
def secL(l, lp): return 0 if l == lp else 1 + l * 3 + (lp if lp < l else lp - 1)
# party index b = (i, (o, r)) <-> flat i*16 + o*2 + r
def unflat(f): return (f // 16, (f % 16) // 2, f % 2)
def flat(i, o, r): return i * 16 + o * 2 + r
def clsN(f):
    i, o, r = unflat(f); return r * 13 + secL(lab(i), lab(o))
def posN(f):
    i, o, r = unflat(f)
    return i * 2 + o // 4 if lab(i) == lab(o) else (i // 4) * 2 + o // 4
def szN(c): return 16 if c % 13 == 0 else 4
def embN(c, p):
    r = c // 13; sg = c % 13
    if sg == 0:
        i = p // 2 % 8
        return flat(i, (p % 2) * 4 + i % 4, r % 2)
    l = (sg - 1) // 3 % 4; t = (sg - 1) % 3; lp = t if t < l else t + 1
    return flat((p // 2 % 2) * 4 + l, (p % 2) * 4 + lp % 4, r % 2)
# class structure checks (mirrored by `decide` in Lean)
seen = set()
for c in range(26):
    for p in range(szN(c)):
        f = embN(c, p); assert clsN(f) == c and posN(f) == p; seen.add(f)
assert len(seen) == 128
for f in range(128):
    assert embN(clsN(f), posN(f)) == f

# ---------------------------------------------------------------- 2. checks on H
for (i, ip), M in H.items():
    if lab(i) != lab(ip):
        assert not np.any(M != 0)
tot = sum(H[(i, i)] for i in range(8))
assert not np.any(tot != 0), "sum_i H(i,i) != 0"
for (i, ip), M in H.items():
    nz = np.argwhere(M != 0)
    for (b, bp) in nz:
        assert clsN(b) == clsN(bp)
    assert np.array_equal(M, H[(ip, i)].T), "H symmetry"
Hmax = max(abs(int(v)) for M in H.values() for v in M.flat)
print("H checks passed; max |H| =", Hmax)

def HintF(i, ip, b, bp):
    if lab(i) == lab(ip) and clsN(b) == clsN(bp):
        return int(H[(i, ip)][b, bp])
    return 0
def WintF(u, v):
    (a, b), (ap, bp) = u, v
    val = (2 ** 65 if u == v else 0)
    ta = HintF(a // 16, ap // 16, b, bp) if (a % 16) == (ap % 16) else 0
    tb = HintF(b // 16, bp // 16, a, ap) if (b % 16) == (bp % 16) else 0
    return val + (2 ** 30 - 1) * (ta + tb)

def blockA(cA, cB):
    sA, sB = szN(cA), szN(cB)
    m = sA * sB
    idx = [(embN(cA, i // sB), embN(cB, i % sB)) for i in range(m)]
    return [[WintF(idx[i], idx[j]) for j in range(m)] for i in range(m)]

# compare with the certificate's integer blocks (verify_strategy.py: 2^76 W = 2^70 1 + 64 (2^30-1) S_cert)
def cert_block_S(cA, cB):
    sA, sB = szN(cA), szN(cB)
    ia = [embN(cA, p) for p in range(sA)]; ib = [embN(cB, p) for p in range(sB)]
    Sm = np.zeros((sA * sB, sA * sB), dtype=object)
    for t, (a, b) in enumerate(pairs):
        Ra, Rb = R[a], R[b]
        term = np.kron(Ra[np.ix_(ia, ia)], Rb[np.ix_(ib, ib)])
        if a != b:
            term = term + np.kron(Rb[np.ix_(ia, ia)], Ra[np.ix_(ib, ib)])
        if term.any():
            Sm = Sm + int(y[t]) * ph[t] * term.astype(object)
    return Sm

if "--skip-compare" not in sys.argv:
    t0 = time.time()
    for cA in range(26):
        for cB in range(26):
            A = blockA(cA, cB)
            Sm = cert_block_S(cA, cB)
            m = len(A)
            for i in range(m):
                for j in range(m):
                    # 2^71 W = 2^65 d + (2^30-1)(TA+TB)  and  2^71 W = 2^65 d + 2 (2^30-1) S_cert
                    assert A[i][j] == (2 ** 65 if i == j else 0) + 2 * (2 ** 30 - 1) * int(Sm[i, j]), (cA, cB, i, j)
    print(f"H-form W equals the certificate W on all 676 blocks ({time.time()-t0:.0f}s)")

# ---------------------------------------------------------------- 3. block certificates
HBOUND = 30000000000
assert Hmax <= HBOUND
ALPHA = 2 ** 65 + 2 * (2 ** 30 - 1) * HBOUND


def packL(X, l):
    s = 0
    for a in reversed(l):
        s = a + X * s
    return s


def certify(A):
    m = len(A)
    Af = np.array([[float(v) for v in row] for row in A])
    ev = np.linalg.eigvalsh(Af)
    assert ev[0] > 0
    tau = 0.5 * ev[0]
    Lf = np.linalg.cholesky(Af - tau * np.eye(m))
    Ao = np.array(A, dtype=object)
    for F in ([0, 8, 16] if m < 256 else []) + [20, 24, 28, 32, 40]:
        L = [[(int(round(Lf[i, j] * 2.0 ** F)) if j <= i else 0) for j in range(m)] for i in range(m)]
        c = 2 ** (2 * F)
        Lo = np.array(L, dtype=object)
        E = (c * Ao - Lo.dot(Lo.T)).tolist()
        if all(sum(abs(v) for v in E[i]) <= 2 * E[i][i] for i in range(m)):
            return F, c, L, E
    raise RuntimeError("no certificate")


def lit(v, hexa=False):
    if hexa:
        return ("zp 0x%x" % v) if v >= 0 else ("zn 0x%x" % (-v))
    return ("zp %d" % v) if v >= 0 else ("zn %d" % (-v))


def lrow(r, hexa=False):
    return "[" + ", ".join(lit(v, hexa) for v in r) + "]"


def lrows(rows):
    return "\n  " + " ::\n  ".join(lrow(r) for r in rows) + " :: []"


BLOCKS = [(cA, cB) for cA in range(26) for cB in range(26) if cA <= cB]
CHUNK = 16
certs = {}
t0 = time.time()
for (cA, cB) in BLOCKS:
    A = blockA(cA, cB)
    m = len(A)
    F, c, L, E = certify(A)
    lam = max(abs(v) for r in L for v in r)
    eps = max(abs(v) for r in E for v in r)
    X = 2 ** (2 * (c * ALPHA + m * lam ** 2 + eps)).bit_length()
    assert 2 * (c * ALPHA + m * lam ** 2 + eps) < X
    # exact checks mirroring the Lean kernel checks
    PL = [packL(X, [L[j][kk] for j in range(m)]) for kk in range(m)]
    for i in range(m):
        lhs = packL(X, [c * A[i][j] for j in range(m)])
        rhs = sum(L[i][kk] * PL[kk] for kk in range(m)) + packL(X, E[i])
        assert lhs == rhs
        assert sum(abs(v) for v in E[i]) <= 2 * E[i][i]
        for j in range(m):
            assert abs(A[i][j]) <= ALPHA and A[i][j] == A[j][i]
    certs[(cA, cB)] = dict(m=m, F=F, c=c, L=L, E=E, lam=lam, eps=eps, X=X, PL=PL)
print(f"certificates for {len(BLOCKS)} blocks ({time.time()-t0:.0f}s); max F =",
      max(v['F'] for v in certs.values()), "; max bits of X =", max(v['X'].bit_length() for v in certs.values()))

# ---------------------------------------------------------------- 4. emission
OUT = os.environ.get("GYNI_OUT", HERE)
os.makedirs(os.path.join(OUT, "Big"), exist_ok=True)
GEN = "Generated by `GYNIProof/gen_gyni_lean.py` from `iqoqi/programs/gyni/GYNI_J4_strategy_cert.npz`."
OPTS = "set_option Elab.async false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n"


def core_header(imports, doc):
    return ("".join(f"import GYNIProof.{m}\n" for m in imports) + f"\n/-! {GEN}\n{doc}\n"
            "Checked by the Lean kernel (`decide +kernel`), one declaration at a time; no Mathlib import. -/\n\n"
            "namespace GYNIProof\n\n" + OPTS)


def emit_small(f, cA, cB):
    d = certs[(cA, cB)]
    nm = f"{cA}_{cB}"
    nexpr = f"(szN {cA} * szN {cB})"
    f.write(f"def cL_{nm} : List (List Int) :={lrows(d['L'])}\n\n")
    f.write(f"def cE_{nm} : List (List Int) :={lrows(d['E'])}\n\n")
    f.write(f"def cPL_{nm} : List Int := packCols {d['X']} {nexpr} cL_{nm}\n\n")
    f.write(f"theorem chk_{nm} : (paramsOK {nexpr} {d['c']} {d['X']} {d['lam']} {d['eps']} alphaW &&\n"
            f"    shapeOK {nexpr} {d['lam']} {d['eps']} cL_{nm} cE_{nm} cPL_{nm} &&\n"
            f"    rowsOK {nexpr} (blockA {cA} {cB}) {d['c']} {d['X']} cPL_{nm} 0 cL_{nm} cE_{nm}) = true := by\n"
            f"  decide +kernel\n\n")


def emit_group(name, blist):
    with open(os.path.join(OUT, name + ".lean"), "w", encoding="utf-8") as f:
        f.write(core_header(["Core"], f"Block certificates `c A = L Lᵀ + E` (`E` diagonally dominant) of the blocks\n"
                            f"{', '.join(f'({a}, {b})' for a, b in blist)} of `2^71 W`."))
        for (cA, cB) in blist:
            emit_small(f, cA, cB)
        f.write("end GYNIProof\n")
    return name


def data_header(doc):
    return f"import GYNIProof.IntLit\n\n/-! {GEN}\n{doc} -/\n\nnamespace GYNIProof\n\nset_option maxRecDepth 100000\n\n"


def emit_big_files(cA, cB):
    d = certs[(cA, cB)]
    nm = f"{cA}_{cB}"
    m = d['m']
    nexpr = f"(szN {cA} * szN {cB})"
    nch = (m + CHUNK - 1) // CHUNK
    X = d['X']
    XK = X ** CHUNK
    data_mods = []
    for q in range(nch):
        mod = f"D_{nm}_{q}"
        rowsL = d['L'][q*CHUNK:(q+1)*CHUNK]
        pc = [packL(X, [rowsL[j][kk] for j in range(len(rowsL))]) for kk in range(m)]
        with open(os.path.join(OUT, "Big", mod + ".lean"), "w", encoding="utf-8") as f:
            f.write(data_header(f"Rows {q*CHUNK}..{(q+1)*CHUNK-1} of the certificate matrices `L`, `E` of the block `({cA}, {cB})`,\n"
                                f"and the packed columns `∑_j L_(16q+j),k X^j` of these rows."))
            f.write(f"def bL_{nm}_{q} : List (List Int) :={lrows(rowsL)}\n\n")
            f.write(f"def bE_{nm}_{q} : List (List Int) :={lrows(d['E'][q*CHUNK:(q+1)*CHUNK])}\n\n")
            f.write(f"def bPLc_{nm}_{q} : List Int :=\n  " + " ::\n  ".join(lit(v, True) for v in pc) + " :: []\n\nend GYNIProof\n")
        data_mods.append("Big." + mod)
    # consistency (exact): the chunk packs combine to the full packed columns
    for kk in range(m):
        acc = 0
        for q in range(nch - 1, -1, -1):
            rowsL = d['L'][q*CHUNK:(q+1)*CHUNK]
            acc = packL(X, [rowsL[j][kk] for j in range(len(rowsL))]) + XK * acc
        assert acc == d['PL'][kk]
    with open(os.path.join(OUT, "Big", f"P_{nm}.lean"), "w", encoding="utf-8") as f:
        f.write(data_header(f"Packed columns `PL_k = ∑_j L_jk X^j` of the certificate of the block `({cA}, {cB})`."))
        f.write(f"def bPL_{nm} : List Int :=\n  " + " ::\n  ".join(lit(v, True) for v in d['PL']) + " :: []\n\nend GYNIProof\n")
    pmod = f"Big.P_{nm}"
    blist = "[" + ", ".join(f"bL_{nm}_{q}" for q in range(nch)) + "]"
    elist = "[" + ", ".join(f"bE_{nm}_{q}" for q in range(nch)) + "]"
    clist = "[" + ", ".join(f"bPLc_{nm}_{q}" for q in range(nch)) + "]"
    shape = f"CertBigShape_{nm}"
    with open(os.path.join(OUT, shape + ".lean"), "w", encoding="utf-8") as f:
        f.write(core_header(["Core"] + data_mods + [pmod],
                            f"Block `({cA}, {cB})` (256 × 256): parameters, shapes and entry bounds, chunk lengths."))
        f.write(f"def cL_{nm} : List (List Int) := List.flatten {blist}\n\n")
        f.write(f"def cE_{nm} : List (List Int) := List.flatten {elist}\n\n")
        f.write(f"theorem params_{nm} : paramsOK {nexpr} {d['c']} {X} {d['lam']} {d['eps']} alphaW = true := by\n  decide +kernel\n\n")
        for q in range(nch):
            f.write(f"theorem bLok_{nm}_{q} : rowsBoundOK {nexpr} {d['lam']} bL_{nm}_{q} = true := by\n  decide +kernel\n\n")
            f.write(f"theorem bEok_{nm}_{q} : rowsBoundOK {nexpr} {d['eps']} bE_{nm}_{q} = true := by\n  decide +kernel\n\n")
        f.write(f"theorem shape_{nm} : shapeOK {nexpr} {d['lam']} {d['eps']} cL_{nm} cE_{nm} bPL_{nm} = true := by\n"
                f"  refine shapeOK_of_chunks (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_ ?_\n"
                f"  · simp only [cL_{nm}, List.flatten_cons, List.flatten_nil, List.append_nil, rowsBoundOK_append, "
                + ", ".join(f"bLok_{nm}_{q}" for q in range(nch)) + ", Bool.and_self]\n"
                f"  · simp only [cE_{nm}, List.flatten_cons, List.flatten_nil, List.append_nil, rowsBoundOK_append, "
                + ", ".join(f"bEok_{nm}_{q}" for q in range(nch)) + ", Bool.and_self]\n\n")
        f.write(f"theorem chunks_{nm} : ∀ l ∈ {blist}, l.length = {CHUNK} ∧ ∀ r ∈ l, r.length = {nexpr} := by\n  decide +kernel\n\nend GYNIProof\n")
    colfiles = []
    for q in range(nch):
        cf = f"CertBigCols_{nm}_{q}"
        with open(os.path.join(OUT, cf + ".lean"), "w", encoding="utf-8") as f:
            f.write(core_header(["Core", data_mods[q]],
                                f"Block `({cA}, {cB})` (256 × 256): packed columns of rows {q*CHUNK}..{(q+1)*CHUNK-1}."))
            f.write(f"theorem colc_{nm}_{q} : packCols {X} {nexpr} bL_{nm}_{q} = bPLc_{nm}_{q} := by\n  decide +kernel\n\nend GYNIProof\n")
        colfiles.append(cf)
    combf = f"CertBigComb_{nm}"
    with open(os.path.join(OUT, combf + ".lean"), "w", encoding="utf-8") as f:
        f.write(core_header(["Core"] + data_mods + [pmod],
                            f"Block `({cA}, {cB})` (256 × 256): the chunk-packed columns combine to the packed columns."))
        f.write(f"theorem comb_{nm} : packCols {XK} {nexpr} {clist} = bPL_{nm} := by\n  decide +kernel\n\nend GYNIProof\n")
    rowfiles = []
    for q in range(nch):
        rf = f"CertBigRows_{nm}_{q}"
        with open(os.path.join(OUT, rf + ".lean"), "w", encoding="utf-8") as f:
            f.write(core_header(["Core", data_mods[q], pmod],
                                f"Block `({cA}, {cB})` (256 × 256): rows {q*CHUNK}..{(q+1)*CHUNK-1} of the packed-row identities."))
            f.write(f"theorem rows_{nm}_{q} : rowsOK {nexpr} (blockA {cA} {cB}) {d['c']} {X} bPL_{nm} {q*CHUNK}\n"
                    f"    bL_{nm}_{q} bE_{nm}_{q} = true := by\n  decide +kernel\n\nend GYNIProof\n")
        rowfiles.append(rf)
    asm = f"CertBig_{nm}"
    with open(os.path.join(OUT, asm + ".lean"), "w", encoding="utf-8") as f:
        f.write("import GYNIProof.Model\n" + f"import GYNIProof.{shape}\n" + "".join(f"import GYNIProof.{cf}\n" for cf in colfiles)
                + f"import GYNIProof.{combf}\n" + "".join(f"import GYNIProof.{rf}\n" for rf in rowfiles))
        f.write(f"\n/-! {GEN}\nBlock `({cA}, {cB})` (256 × 256) of `2^71 W` is positive semidefinite: assembly of the\n"
                f"kernel checks of `{shape}` and `CertBigRows_{nm}_*` with `packCols_flatten` and\n"
                f"`posSemidef_of_cert`. -/\n\nnamespace GYNIProof\n\n")
        f.write(f"theorem cols_{nm} : packCols {X} {nexpr} cL_{nm} = bPL_{nm} := by\n"
                f"  unfold cL_{nm}\n"
                f"  rw [packCols_flatten _ _ {CHUNK} _ chunks_{nm}]\n"
                f"  simp only [List.map_cons, List.map_nil, " + ", ".join(f"colc_{nm}_{q}" for q in range(nch)) + "]\n"
                f"  rw [show ({X} : ℤ) ^ {CHUNK} = {XK} by norm_num]\n"
                f"  exact comb_{nm}\n\n")
        f.write(f"theorem rows_{nm} : rowsOK {nexpr} (blockA {cA} {cB}) {d['c']} {X} bPL_{nm} 0 cL_{nm} cE_{nm} = true := by\n"
                f"  unfold cL_{nm} cE_{nm}\n"
                f"  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]\n")
        for q in range(nch - 1):
            f.write(f"  refine rowsOK_append' _ _ _ _ _ {q*CHUNK} {(q+1)*CHUNK} _ _ _ _ (by decide +kernel) (by decide +kernel)\n"
                    f"    rows_{nm}_{q} ?_\n")
        f.write(f"  exact rows_{nm}_{nch-1}\n\n")
        f.write(f"theorem cert_{nm} : BlockPSD {cA} {cB} :=\n"
                f"  posSemidef_of_cert _ (blockA {cA} {cB}) (blockA_symm {cA} {cB}) _ _ _ _ alphaW (blockA_bound {cA} {cB})\n"
                f"    _ _ _ params_{nm} shape_{nm} cols_{nm} rows_{nm}\n\nend GYNIProof\n")
    return data_mods + [pmod, shape] + colfiles + [combf] + rowfiles + [asm]


# Data.lean
with open(os.path.join(OUT, "Data.lean"), "w", encoding="utf-8") as f:
    f.write(f"""import GYNIProof.IntLit

/-! {GEN}
The integer matrices `H(i,i')` restricted to the classes (`Hdat[c][pair][x][y]`, see `Core.lean`)
and the rational instrument parameters `c_l = cNum[l] / csDen[l]`, `s_l = sNum[l] / csDen[l]`. -/

namespace GYNIProof

set_option maxRecDepth 1000000 in
/-- `Hdat[c][4 l + 2 q + q'][x][y] = H(4q+l, 4q'+l)(embN c x, embN c y)`. -/
def Hdat : List (List (List (List Int))) :=
""")
    cls_items = []
    for c in range(26):
        pr_items = []
        for l in range(4):
            for q in range(2):
                for qp in range(2):
                    i, ip = q * 4 + l, qp * 4 + l
                    s = szN(c)
                    rows = [[int(H[(i, ip)][embN(c, x), embN(c, yy)]) for yy in range(s)] for x in range(s)]
                    pr_items.append("[" + ", ".join(lrow(r) for r in rows) + "]")
        cls_items.append("  [" + ",\n   ".join(pr_items) + "]")
    f.write(" ::\n".join(cls_items) + " :: []\n\n")
    cs = [(int(a), int(b), int(c_), int(d_)) for a, b, c_, d_ in zip(Z['c_num'], Z['c_den'], Z['s_num'], Z['s_den'])]
    assert all(b == d_ for a, b, c_, d_ in cs)
    f.write("/-- Numerators of `c_l`. -/\ndef cNum : List Nat := [" + ", ".join(str(a) for a, b, c_, d_ in cs) + "]\n")
    f.write("/-- Numerators of `s_l`. -/\ndef sNum : List Nat := [" + ", ".join(str(c_) for a, b, c_, d_ in cs) + "]\n")
    f.write("/-- Common denominators of `c_l`, `s_l`. -/\ndef csDen : List Nat := [" + ", ".join(str(b) for a, b, c_, d_ in cs) + "]\n\n")
    f.write("end GYNIProof\n")

big = [b for b in BLOCKS if certs[b]['m'] == 256]
mid = [b for b in BLOCKS if certs[b]['m'] == 64]
small = [b for b in BLOCKS if certs[b]['m'] == 16]
BIGMODS = {}
for (cA, cB) in big:
    BIGMODS[(cA, cB)] = emit_big_files(cA, cB)
SMALLFILES = [emit_group(f"CertSmall{g}", small[g * 38:(g + 1) * 38]) for g in range(8)]
MIDFILES = [emit_group(f"CertMid{g}", mid[g * 3:(g + 1) * 3]) for g in range(16)]
BIGSET = set(big)
with open(os.path.join(OUT, "BlockCerts.lean"), "w", encoding="utf-8") as f:
    f.write("import GYNIProof.Model\n" + "".join(f"import GYNIProof.{fn}\n" for fn in SMALLFILES + MIDFILES))
    f.write(f"""
/-! {GEN}
Every block `(cA, cB)`, `cA ≤ cB < 26`, of `2^71 W` is positive semidefinite: the kernel checks
`chk_cA_cB` of `CertSmall*`/`CertMid*` (348 blocks) turned into `BlockPSD cA cB` by
`posSemidef_of_chk`. The three `256 × 256` blocks `(0, 0)`, `(0, 13)`, `(13, 13)` (both parties in a
label-diagonal class) enter through the hypothesis `BigBlocksPSD`, discharged in `CertBig_*.lean`
(`Main.lean`). -/

namespace GYNIProof

/-- Positive semidefiniteness of the three `256 × 256` integer blocks `blockA 0 0`,
`blockA 0 13`, `blockA 13 13` of `2^71 W`. -/
def BigBlocksPSD : Prop := BlockPSD 0 0 ∧ BlockPSD 0 13 ∧ BlockPSD 13 13

""")
    for (cA, cB) in small + mid:
        nm = f"{cA}_{cB}"
        f.write(f"theorem cert_{nm} : BlockPSD {cA} {cB} :=\n"
                f"  posSemidef_of_chk _ (blockA {cA} {cB}) (blockA_symm {cA} {cB}) _ _ _ _ alphaW (blockA_bound {cA} {cB})\n"
                f"    cL_{nm} cE_{nm} cPL_{nm} rfl chk_{nm}\n\n")
    bigref = {(0, 0): "hbig.1", (0, 13): "hbig.2.1", (13, 13): "hbig.2.2"}
    for cA in range(26):
        refs = [(bigref[(cA, cB)] if (cA, cB) in BIGSET else f"cert_{cA}_{cB}") for cB in range(cA, 26)]
        f.write(f"theorem blockPSD_row_{cA} (hbig : BigBlocksPSD) :\n    ∀ cB : ℕ, {cA} ≤ cB → cB < 26 → BlockPSD {cA} cB := by\n"
                f"  intro cB h1 h2\n  interval_cases cB\n  exacts [" + ", ".join(refs) + "]\n\n")
    f.write("theorem blockPSD_le (hbig : BigBlocksPSD) :\n    ∀ cA cB : ℕ, cA ≤ cB → cB < 26 → BlockPSD cA cB := by\n"
            "  intro cA cB h1 h2\n  have h3 : cA < 26 := by omega\n  interval_cases cA\n  exacts [" +
            ", ".join(f"blockPSD_row_{cA} hbig cB h1 h2" for cA in range(26)) + "]\n\nend GYNIProof\n")
print("small files:", SMALLFILES)
print("mid files:", MIDFILES)
print("big modules:", {k: len(v) for k, v in BIGMODS.items()})
print("F values:", sorted(set(v['F'] for v in certs.values())))
for b in big:
    d = certs[b]
    print("big block", b, "F", d['F'], "X bits", d['X'].bit_length(), "lam bits", d['lam'].bit_length(), "eps bits", d['eps'].bit_length())
with open(os.path.join(OUT, "Big", "MODULES.txt"), "w", encoding="utf-8") as f:
    for (cA, cB) in big:
        f.write(" ".join(BIGMODS[(cA, cB)]) + "\n")

# ---------------------------------------------------------------- 5. instruments and the exact value
cs5 = [(Fr(int(a), int(b)), Fr(int(c_), int(d_))) for a, b, c_, d_ in zip(Z['c_num'], Z['c_den'], Z['s_num'], Z['s_den'])]
for (cc, ss) in cs5:
    assert cc * cc + ss * ss == 1


def phi(x, l, q):
    cc, ss = cs5[l]
    return cc if q == 0 else (-ss if x == 0 else ss)


def P0(x, o, i):
    return phi(x, o % 4, o // 4) * phi(x, i % 4, i // 4) if o % 4 == i % 4 else Fr(0)


def Pm(a, x, o, i):
    return P0(x, o, i) if a == 0 else Fr(int(o == i)) - P0(x, o, i)


def vvec(a, x, f):
    i, o, r = unflat(f)
    return Pm(a, x, o, i) if r == x else Fr(0)


for a in range(2):
    for x in range(2):
        for f in range(128):
            if clsN(f) != 13 * x:
                assert vvec(a, x, f) == 0
LAM = 1
for a in range(2):
    for x in range(2):
        for p in range(16):
            LAM = LAM * vvec(a, x, embN(13 * x, p)).denominator // math.gcd(LAM, vvec(a, x, embN(13 * x, p)).denominator)
vtab = {(a, x): [int(vvec(a, x, embN(13 * x, p)) * LAM) for p in range(16)] for a in range(2) for x in range(2)}
for (a, x), row in vtab.items():
    for p in range(16):
        assert Fr(row[p], LAM) == vvec(a, x, embN(13 * x, p))
kappa = Fr(2 ** 30 - 1, 2 ** 71)


def trq(x, a):
    return sum(vvec(a, x, f) ** 2 for f in range(128))


def ptq(x, a, ip, i):
    return sum(vvec(a, x, flat(ip, o, r)) * vvec(a, x, flat(i, o, r)) for o in range(8) for r in range(2))


def hInt(i, ip, s, a):
    vt = vtab[(a, s)]
    return sum(HintF(i, ip, embN(13 * s, p), embN(13 * s, pp)) * vt[pp] * vt[p] for p in range(16) for pp in range(16))


V = Fr(0)
for x in range(2):
    for yy in range(2):
        t = Fr(1, 64) * trq(x, yy) * trq(yy, x)
        t += sum(ptq(x, yy, ip, i) * kappa * Fr(hInt(i, ip, yy, x), LAM * LAM) for i in range(8) for ip in range(8))
        t += sum(kappa * Fr(hInt(j, jp, x, yy), LAM * LAM) * ptq(yy, x, jp, j) for j in range(8) for jp in range(8))
        V += t / 4
claimed = Fr(int(str(Z['claimed_value_num'])), int(str(Z['claimed_value_den'])))
print("exact value (Lean formulas):", float(V), " equals stored claim:", V == claimed)
assert V == claimed
assert V >= Fr(6221659013539, 10 ** 13) and V < Fr(622165901354, 10 ** 12)  # NB: 0.622165901354 is a rounded-up decimal
with open(os.path.join(OUT, "ValueData.lean"), "w", encoding="utf-8") as f:
    f.write("""import GYNIProof.IntLit

/-! Generated by `GYNIProof/gen_gyni_lean.py`: the instrument vectors on their class, scaled to
integers (`vtab a x p = LAM * v_{a,x}(embN (13 x) p)`), and the exact GYNI value of the strategy
(the value stored in `GYNI_J4_strategy_cert.npz`). -/

namespace GYNIProof

/-- Common denominator of the instrument vectors. -/
def LAM : Nat := %d

/-- `vtab a x p = LAM * v_{a,x}(embN (13 x) p)`. -/
def vtabData : List (List Int) :=
""" % LAM)
    rows = [vtab[(a, x)] for a in range(2) for x in range(2)]
    f.write("  " + " ::\n  ".join(lrow(r) for r in rows) + " :: []\n\n")
    f.write("/-- The exact GYNI value (numerator). -/\ndef valNum : Nat := %d\n" % V.numerator)
    f.write("/-- The exact GYNI value (denominator). -/\ndef valDen : Nat := %d\n\nend GYNIProof\n" % V.denominator)
print("LAM =", LAM, "bits", LAM.bit_length())

# ---------------------------------------------------------------- 6. value tables (small kernel checks)
def qlit(q):
    q = Fr(q)
    return "(%s, %d)" % (lit(q.numerator), q.denominator)


Ttab = {(x, a): trq(x, a) for x in range(2) for a in range(2)}
Ktab = {(x, a, ip, i): ptq(x, a, ip, i) for x in range(2) for a in range(2) for ip in range(8) for i in range(8)}
Htab = {(s, a, i, ip): (hInt(i, ip, s, a) if i % 4 == ip % 4 else 0) for s in range(2) for a in range(2) for i in range(8) for ip in range(8)}
trTab = {}
for x in range(2):
    for yy in range(2):
        t = Fr(1, 64) * Ttab[(x, yy)] * Ttab[(yy, x)]
        t += sum(Ktab[(x, yy, ip, i)] * kappa * Fr(Htab[(yy, x, i, ip)], LAM * LAM) for i in range(8) for ip in range(8))
        t += sum(kappa * Fr(Htab[(x, yy, j, jp)], LAM * LAM) * Ktab[(yy, x, jp, j)] for j in range(8) for jp in range(8))
        trTab[(x, yy)] = t
assert sum(trTab.values()) / 4 == V
with open(os.path.join(OUT, "ValueTabs.lean"), "w", encoding="utf-8") as f:
    f.write("""import GYNIProof.IntLit

/-! Generated by `GYNIProof/gen_gyni_lean.py`: exact tables of the pieces of the GYNI value
(traces `Tr M_{a|x}`, partial traces `Tr_O M_{a|x}`, integer quadratic forms `hInt`, and the four
terms `Tr[W (M_{y|x} ⊗ M_{x|y})]`), rationals as pairs `(numerator, denominator)`, each checked
separately by the kernel in `Value.lean`. -/

namespace GYNIProof

set_option maxRecDepth 100000

""")
    f.write("/-- `Tr M_{a|x}`, index `2 x + a`. -/\ndef TtabData : List (Int × Nat) := [" + ", ".join(qlit(Ttab[(x, a)]) for x in range(2) for a in range(2)) + "]\n\n")
    f.write("/-- `(Tr_O M_{a|x}) i' i`, index `128 x + 64 a + 8 i' + i`. -/\ndef KtabData : List (Int × Nat) :=\n  " +
            " ::\n  ".join(qlit(Ktab[(x, a, ip, i)]) for x in range(2) for a in range(2) for ip in range(8) for i in range(8)) + " :: []\n\n")
    f.write("/-- `hInt i i' s a`, index `128 s + 64 a + 8 i + i'`. -/\ndef HtabData : List Int :=\n  " +
            " ::\n  ".join(lit(Htab[(s, a, i, ip)]) for s in range(2) for a in range(2) for i in range(8) for ip in range(8)) + " :: []\n\n")
    f.write("/-- `Tr[W (M_{y|x} ⊗ M_{x|y})]`, index `2 x + y`. -/\ndef trTabData : List (Int × Nat) := [" + ", ".join(qlit(trTab[(x, yy)]) for x in range(2) for yy in range(2)) + "]\n\nend GYNIProof\n")
print("value tables written")
