"""Export the symmetry-free GYNI dual certificate (averaged_cert.py) as Lean data for GYNIUpper.

Data (all integers, scaled by den = 16 D |GG|):
  Phi_{rs}[i][j], i = a n + b, j = a' n + b'   (Phi = o + Y', see averaged_cert.py)
  A_{rs} = Phi_{rs} - o_{rs} = Y'_{rs}         (must be positive semidefinite)
Packed rows (UBCheck.lean): row i of Phi_{rs} is  R_i = sum_j (Phi[i][j] + OA) 2^(BA j).
PSD certificate per block: c A = L L^T + E with L lower triangular (L = round(2^F chol(A - tau I))),
c = 2^(2F), E diagonally dominant; L row i packed as  RL_i = sum_{k<=i} (L[i][k] + OL) 2^(BL k);
packed columns PL_k = sum_j L[j][k] 2^(B j).
Every check of UBCheck.lean is re-run here in exact integer arithmetic (a mirror of the Lean code)
before anything is written.

usage: python export_lean.py <averaged.pkl> <outdir> <Lname> [F]
"""
import os, sys, pickle, time
sys.dont_write_bytecode = True  # never write caches into the source repository
import numpy as np
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from averaged_cert import word_at, cls, red


# ---------------------------------------------------------------- mirrors of UBCheck.lean

def dig(B, R, j):
    return (R >> (B * j)) % (1 << B)


def objE(n, i0, i1, od, r, s, i, j):
    def uS(i1x, sgn, a):
        return 1 if a == i0 else (sgn if a == i1x else 0)
    sA = 1 if s == 0 else -1
    sB = 1 if r == 0 else -1
    return od * (uS(i1[r], sA, i // n) * uS(i1[r], sA, j // n) * uS(i1[s], sB, i % n) * uS(i1[s], sB, j % n))


def packZ(X, l):
    acc = 0
    for a in reversed(l):
        acc = a + X * acc
    return acc


def rowChk(N, B, BA, BL, offA, offL, c, eps, h, ones, obj, PL, R, RL, i):
    X = 1 << B
    rowA = [dig(BA, R, j) - offA - obj(i, j) for j in range(N)]
    rowL = [dig(BL, RL, k) - offL for k in range(i + 1)]
    W = c * packZ(X, rowA) - sum(a * b for a, b in zip(rowL, PL)) + h * ones
    if W < 0:
        return False
    w = W
    sabs = 0
    ei = 0
    for j in range(N):
        e = (w % (1 << B)) - h
        if not (-eps <= e <= eps):
            return False
        sabs += abs(e)
        if j == i:
            ei = e
        w >>= B
    return w == 0 and sabs <= 2 * ei


def colPack(BL, offL, B, k, RLs):
    return sum(((dig(BL, RL, k) - offL) if k <= j else 0) * (1 << (B * j)) for j, RL in enumerate(RLs))


# ---------------------------------------------------------------- certificate construction

def exact_gram(Lint):
    """L L^T exactly (L: list of lists of Python ints, |L| < 2^62) via int64 blocks of 26 bits"""
    N = len(Lint)
    SH = 26
    M = (1 << SH) - 1
    arr = np.array(Lint, dtype=object)
    sgn = np.sign(arr).astype(np.int64)
    ab = np.abs(arr)
    parts = []
    rem = ab.copy()
    for t in range(3):
        parts.append(np.array((rem & M), dtype=np.int64) * sgn)
        rem = rem >> SH
    assert all(v == 0 for v in rem.flat)
    G = [[0] * N for _ in range(N)]
    Gobj = np.zeros((N, N), dtype=object)
    for p in range(3):
        for q in range(3):
            prod = parts[p] @ parts[q].T          # entries < 289 * 2^52 < 2^61
            Gobj = Gobj + prod.astype(object) * (1 << (SH * (p + q)))
    return [[int(Gobj[i, j]) for j in range(N)] for i in range(N)]


def cholesky_cert(A, F):
    """A: list of lists of ints (symmetric PD). Returns (Lint, E, c)."""
    N = len(A)
    Af = np.array([[float(x) for x in row] for row in A])
    ev = np.linalg.eigvalsh(Af)
    lmin, lmax = ev[0], ev[-1]
    tau = lmin / 2
    Lf = np.linalg.cholesky(Af - tau * np.eye(N))
    scale = float(2 ** F)
    Lint = [[int(round(Lf[i, k] * scale)) if k <= i else 0 for k in range(N)] for i in range(N)]
    c = 1 << (2 * F)
    G = exact_gram(Lint)
    E = [[c * A[i][j] - G[i][j] for j in range(N)] for i in range(N)]
    return Lint, E, c, lmin, lmax


def verify_E(E):
    N = len(E)
    ok = True
    worst = None
    for i in range(N):
        s = sum(abs(x) for x in E[i])
        if not s <= 2 * E[i][i]:
            ok = False
        r = (2 * E[i][i] - s) / max(1, E[i][i])
        worst = r if worst is None else min(worst, r)
        for j in range(N):
            if E[i][j] != E[j][i]:
                ok = False
    return ok, worst


# ---------------------------------------------------------------- Lean emission helpers

def lean_nat_list(name, xs, per_line=1, ty="List Nat"):
    body = ",\n  ".join(str(x) for x in xs)
    return f"/-- Generated data. -/\nnoncomputable def {name} : {ty} := [\n  {body}]\n"


def lean_int(x):
    return f"Int.ofNat {x}" if x >= 0 else f"Int.negSucc {-x - 1}"


def lean_int_list(name, xs):
    body = ",\n  ".join(lean_int(x) for x in xs)
    return f"/-- Generated data. -/\nnoncomputable def {name} : List Int := [\n  {body}]\n"


def fin2_word(w):
    return "[" + ", ".join(str(c) for c in w) + "]"


def main(avg_path, outdir, Lname, F=24):
    t0 = time.time()
    with open(avg_path, "rb") as f:
        R = pickle.load(f)
    L = R['L']; den = R['den']
    n = 2 * L + 1; N = n * n
    Phi = R['Phi']; Yavg = R['Yavg']; o = R['o']
    words = [word_at(m) for m in range(-L, L + 1)]
    assert words == [tuple(w) for w in R['words']]
    i0 = L; i1 = (L - 1, L + 1)
    assert words[i0] == () and words[i1[0]] == (0,) and words[i1[1]] == (1,)
    assert den % 64 == 0
    od = den // 64
    # objective check
    for (r, s), blk in o.items():
        for i in range(N):
            for j in range(N):
                assert blk[i][j] == objE(n, i0, i1, od, r, s, i, j)
    # data digits
    mx = max(abs(x) for k in Phi for row in Phi[k] for x in row)
    BA = mx.bit_length() + 1
    OA = 1 << (BA - 1)
    assert mx < OA
    print(f"[{Lname}] L={L} n={n} N={N} den=2^{den.bit_length()-1}, max|Phi| 2^{mx.bit_length()}, BA={BA}", flush=True)
    blocks = [(0, 0), (0, 1), (1, 0), (1, 1)]
    rows = {k: [sum((Phi[k][i][j] + OA) << (BA * j) for j in range(N)) for i in range(N)] for k in blocks}
    # classes and table
    classes = sorted({cls(words[a], words[a2]) for a in range(n) for a2 in range(n)}, key=lambda w: (len(w), w))
    NC = len(classes); te = classes.index(())
    tab = [[0] * n for _ in range(NC)]
    for t, cw in enumerate(classes):
        for a in range(n):
            hits = [a2 for a2 in range(n) if cls(words[a], words[a2]) == cw]
            assert len(hits) <= 1
            tab[t][a] = hits[0] + 1 if hits else 0
    # PSD certificates
    certs = {}
    for k in blocks:
        t1 = time.time()
        A = Yavg[k]
        Lint, E, c, lmin, lmax = cholesky_cert(A, F)
        ok, worst = verify_E(E)
        eps = max(abs(x) for row in E for x in row)
        print(f"  block {k}: eig [{lmin:.3e}, {lmax:.3e}] (x den), dominance ok {ok} (min slack ratio {worst:.3f}), "
              f"max|L| 2^{max(abs(x) for row in Lint for x in row).bit_length()}, eps 2^{eps.bit_length()} "
              f"({time.time()-t1:.1f}s)", flush=True)
        assert ok, "E not diagonally dominant: increase F"
        certs[k] = (Lint, E, c, eps)
    c = certs[(0, 0)][2]
    Lmax = max(abs(x) for k in blocks for row in certs[k][0] for x in row)
    BL = Lmax.bit_length() + 1
    OL = 1 << (BL - 1)
    eps = max(certs[k][3] for k in blocks)
    alpha = OA + od
    lam = OL
    B = (2 * (c * alpha + N * lam * lam + eps)).bit_length() + 1
    assert 2 * (c * alpha + N * lam * lam + eps) < (1 << B)
    H = 1 << (B - 1)
    X = 1 << B
    ones = packZ(X, [1] * N)
    assert eps < H
    print(f"  params: F={F} c=2^{2*F} BL={BL} B={B} eps=2^{eps.bit_length()}", flush=True)
    lrows = {k: [sum((certs[k][0][i][kk] + OL) << (BL * kk) for kk in range(i + 1)) for i in range(N)] for k in blocks}
    PL = {k: [sum(certs[k][0][j][kk] * (1 << (B * j)) for j in range(N)) for kk in range(N)] for k in blocks}
    # ---- mirror checks
    t1 = time.time()
    for k in blocks:
        for kk in range(N):
            assert PL[k][kk] == colPack(BL, OL, B, kk, lrows[k])
        for i in range(N):
            assert rowChk(N, B, BA, BL, OA, OL, c, eps, H, ones,
                          lambda ii, jj, kk_=k: objE(n, i0, i1, od, kk_[0], kk_[1], ii, jj),
                          PL[k], rows[k][i], lrows[k][i], i), (k, i)
            for j in range(i):
                assert dig(BA, rows[k][i], j) == dig(BA, rows[k][j], i)
    # class sums (mirror of caOK / cbOK)
    def blk(r, s):
        return rows[(r, s)]
    for s in (0, 1):
        for b in range(n):
            Rs = [blk(0, s)[a * n + b] for a in range(n)] + [blk(1, s)[a * n + b] for a in range(n)]
            for b2 in range(n):
                for t in range(NC):
                    if t == te:
                        continue
                    g = tab[t] + tab[t]
                    tot = sum(dig(BA, Rm, (gm - 1) * n + b2) for Rm, gm in zip(Rs, g) if gm)
                    cnt = sum(1 for gm in g if gm)
                    assert tot == OA * cnt, ("CA", s, b, b2, t)
    for r in (0, 1):
        for a in range(n):
            Rs = [blk(r, 0)[a * n + b] for b in range(n)] + [blk(r, 1)[a * n + b] for b in range(n)]
            for a2 in range(n):
                for t in range(NC):
                    if t == te:
                        continue
                    g = tab[t] + tab[t]
                    tot = sum(dig(BA, Rm, a2 * n + (gm - 1)) for Rm, gm in zip(Rs, g) if gm)
                    cnt = sum(1 for gm in g if gm)
                    assert tot == OA * cnt, ("CB", r, a, a2, t)
    trace = sum(dig(BA, rows[k][i], i) for k in blocks for i in range(N))
    beta_num = trace - 4 * N * OA
    from fractions import Fraction
    beta = Fraction(beta_num, den)
    assert beta == R['beta'], (beta, R['beta'])
    print(f"  mirror checks passed ({time.time()-t1:.1f}s); beta = {beta_num}/{den} = {beta} = {float(beta):.15f}", flush=True)
    return dict(L=L, n=n, N=N, den=den, od=od, BA=BA, OA=OA, BL=BL, OL=OL, B=B, H=H, c=c, F=F, eps=eps,
                ones=ones, rows=rows, lrows=lrows, PL=PL, classes=classes, NC=NC, te=te, tab=tab,
                beta_num=beta_num, beta=beta, i0=i0, i1=i1)




# ---------------------------------------------------------------- writing the Lean files

HEADER = "/-! Generated by `GYNIUpper/tools/export_lean.py` from `{src}`. {what} -/\n\n"


def fix_order(text):
    """move the leading module docstring after the import lines"""
    if not text.startswith("/-!"):
        return text
    end = text.index("-/") + 2
    doc = text[:end].strip() + "\n"
    rest = text[end:].lstrip("\n")
    lines = rest.split("\n")
    k = 0
    while k < len(lines) and lines[k].startswith("import "):
        k += 1
    imports = "\n".join(lines[:k])
    body = "\n".join(lines[k:]).lstrip("\n")
    return imports + "\n\n" + doc + "\n" + body


def write(path, text):
    text = fix_order(text)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return os.path.getsize(path)


def chunk_ranges(total, size):
    out = []
    lo = 0
    while lo < total:
        cnt = min(size, total - lo)
        out.append((lo, cnt))
        lo += cnt
    return out


def nested_add(lemma, names):
    """lemma (lemma (n0 n1) n2) ... as a Lean term"""
    t = names[0]
    for nm in names[1:]:
        t = f"({lemma} {t} {nm})"
    return t


def emit_split(C, outdir, Lname, src, ns, mod, OPT, rows_per_chunk, chunks):
    """Split layout: ChkTab, ChkCA_s_q, ChkCB_r_q, ChkSym_rs, ChkCol_rs, ChkRows_rs_q, Main."""
    n, N, NC = C['n'], C['N'], C['NC']
    blocks = [(0, 0), (0, 1), (1, 0), (1, 1)]
    files = []
    cab = chunks.get('ca', n)            # words b per class-sum file
    rpf = chunks.get('rows_per_file', N)  # rows per rows file
    rpc = rows_per_chunk or N             # rows per theorem
    t = HEADER.format(src=src, what="Kernel checks: class table, parameters, lengths, trace.")
    t += f"import {mod}.Blocks\n\nnamespace {ns}\n\n" + OPT
    t += "theorem tab_ok : tabOK (wordAt lev) nW cw tab = true := by decide +kernel\n\n"
    t += "theorem cover_ok : coverOK (wordAt lev) nW cw = true := by decide +kernel\n\n"
    t += "theorem cw_len : cw.length = nC := by decide +kernel\n\n"
    t += "theorem cw_te : cw.getD tE [] = [] := by decide +kernel\n\n"
    t += "theorem te_lt : tE < nC := by decide +kernel\n\n"
    t += "theorem tab_shape : tabShapeOK nW nC tE tab = true := by decide +kernel\n\n"
    t += "theorem ones_ok : onesX = packZ (pw bX 1) (List.replicate nN 1) := by decide +kernel\n\n"
    t += ("theorem params_ok : 0 < cS ∧ 0 ≤ eB ∧ 2 * hX = pw bX 1 ∧ 2 * oA = 2 ^ bA ∧ 2 * oL = 2 ^ bL ∧\n"
          "    0 < od ∧ 64 * od = den ∧\n"
          "    2 * (cS * ((oA : Int) + od) + (nN : Int) * ((oL : Int) * (oL : Int)) + eB) < pw bX 1 := by\n"
          "  decide +kernel\n\n")
    t += ("theorem words_ok : wordAt lev lev = [] ∧ wordAt lev (i1 0) = [0] ∧ wordAt lev (i1 1) = [1] ∧\n"
          "    lev < nW ∧ i1 0 < nW ∧ i1 1 < nW ∧ nN = nW * nW := by decide +kernel\n\n")
    for (r, s) in blocks:
        t += f"theorem len{r}{s} : (blk {r} {s}).length = nN := by decide +kernel\n\n"
    t += ("theorem trace_ok : (traceSum bA (blk 0 0) 0 + traceSum bA (blk 0 1) 0 + traceSum bA (blk 1 0) 0\n"
          "    + traceSum bA (blk 1 1) 0 : Int) = betaNum + 4 * nN * oA := by decide +kernel\n\n")
    t += f"end {ns}\n"
    files.append(("ChkTab", write(os.path.join(outdir, "ChkTab.lean"), t)))
    ca_names = {}
    for kind, fn in (("CA", "caSB"), ("CB", "cbRA")):
        for x in (0, 1):
            names = []
            t = HEADER.format(src=src, what=f"Kernel checks: class sums ({kind}), register {x} (one theorem per word chunk).")
            t += f"import {mod}.Blocks\n\nnamespace {ns}\n\n" + OPT
            for q, (lo, cnt) in enumerate(chunk_ranges(n, cab)):
                nm = f"{kind.lower()}_{x}_{q}"
                t += (f"theorem {nm} : allFrom (fun w => {fn} bA oA nW nC tE tab blk {x} w) {lo} {cnt} = true := by\n"
                      f"  decide +kernel\n\n")
                names.append(nm)
            t += f"end {ns}\n"
            files.append((f"Chk{kind}_{x}", write(os.path.join(outdir, f"Chk{kind}_{x}.lean"), t)))
            ca_names[(kind, x)] = names
    col_names = {}
    for (r, s) in blocks:
        k = f"{r}{s}"
        t = HEADER.format(src=src, what=f"Kernel check: symmetry of block `({r}, {s})`.")
        t += f"import {mod}.Blocks\n\nnamespace {ns}\n\n" + OPT
        t += f"theorem sym{k} : symOK bA (blk {r} {s}) [] 0 = true := by decide +kernel\n\n"
        t += f"end {ns}\n"
        files.append((f"ChkSym{k}", write(os.path.join(outdir, f"ChkSym{k}.lean"), t)))
        t = HEADER.format(src=src, what=f"Kernel check: packed columns of the factor of block `({r}, {s})`.")
        t += f"import {mod}.Params\nimport {mod}.Fac{k}\nimport {mod}.Col{k}\n\nnamespace {ns}\n\n" + OPT
        t += f"theorem fac_len{k} : fac{k}.length = nN := by decide +kernel\n\n"
        t += f"theorem col_len{k} : col{k}.length = nN := by decide +kernel\n\n"
        cnames = []
        for (lo, cnt) in chunk_ranges(N, chunks.get('cols_per_thm', N)):
            nm = f"col_ok{k}_{lo}"
            t += f"theorem {nm} : colOK bL oL bX fac{k} col{k} {lo} {cnt} = true := by decide +kernel\n\n"
            cnames.append(nm)
        col_names[k] = cnames
        t += f"end {ns}\n"
        files.append((f"ChkCol{k}", write(os.path.join(outdir, f"ChkCol{k}.lean"), t)))
    row_names = {}
    for (r, s) in blocks:
        k = f"{r}{s}"
        names = []
        for fq, (flo, fcnt) in enumerate(chunk_ranges(N, rpf)):
            t = HEADER.format(src=src, what=f"Kernel checks: rows {flo}..{flo+fcnt-1} of `c A = L Lᵀ + E`, block `({r}, {s})`.")
            t += f"import {mod}.Params\nimport {mod}.Phi{k}\nimport {mod}.Fac{k}\nimport {mod}.Col{k}\n\nnamespace {ns}\n\n" + OPT
            for (lo, cnt) in chunk_ranges(fcnt, rpc):
                lo += flo
                nm = f"rows{k}_{lo}"
                t += (f"theorem {nm} : rowsChk nN bX bA bL oA oL cS eB hX onesX (objE nW lev i1 od {r} {s})\n"
                      f"    col{k} phi{k} fac{k} {lo} {cnt} = true := by decide +kernel\n\n")
                names.append((nm, lo, cnt))
            t += f"end {ns}\n"
            files.append((f"ChkRows{k}_{fq}", write(os.path.join(outdir, f"ChkRows{k}_{fq}.lean"), t)))
        row_names[k] = names
    # Main
    from fractions import Fraction
    beta = Fraction(C['beta_num'], C['den'])
    p, q = beta.numerator, beta.denominator
    kq = q.bit_length() - 1
    assert q == 1 << kq
    dec = -((-p * 10 ** 12) // q)       # rounded up, 12 digits
    decs = f"0.{dec:012d}"
    imports = [f"import GYNIUpper.UBLevelMain", "import GYNIUpper.UBBridge", f"import {mod}.ChkTab"]
    for (kind, x) in ca_names:
        imports.append(f"import {mod}.Chk{kind}_{x}")
    for (r, s) in blocks:
        k = f"{r}{s}"
        imports.append(f"import {mod}.ChkSym{k}")
        imports.append(f"import {mod}.ChkCol{k}")
        for fq in range(len(chunk_ranges(N, rpf))):
            imports.append(f"import {mod}.ChkRows{k}_{fq}")
    t = "\n".join(imports) + "\n\n"
    t += (f"/-!\n# The level-{C['L']} bound\n\n"
          f"Generated by `GYNIUpper/tools/export_lean.py` from `{src}`. The certificate gives\n\n"
          f"  `I_GYNI ≤ {p} / 2^{kq} = {float(beta):.15f}…`\n\n"
          f"for every Lüders-form strategy (`gyni_le_lueders`) and, with Lemma 1\n"
          f"(`GYNIUpper.lueders_normal_form`), for every strategy (`gyni_upper_bound`).\n-/\n\n")
    t += f"namespace {ns}\n\nopen GYNIProof GYNIUpperBound\n\nset_option maxRecDepth 100000\n\n"
    t += ("-- the elaborator must never evaluate the checks (only the kernel does, in the check files)\n"
          "attribute [local irreducible] rowsChk colOK\n\n")
    t += ("/-- The factor rows of block `(r, s)`. -/\nnoncomputable def facF (r s : ℕ) : List ℕ :=\n"
          "  if r = 0 then (if s = 0 then fac00 else fac01) else (if s = 0 then fac10 else fac11)\n\n"
          "/-- The packed factor columns of block `(r, s)`. -/\nnoncomputable def colF (r s : ℕ) : List ℤ :=\n"
          "  if r = 0 then (if s = 0 then col00 else col01) else (if s = 0 then col10 else col11)\n\n"
          "theorem blocks4 {p : ℕ → ℕ → Prop} (h00 : p 0 0) (h01 : p 0 1) (h10 : p 1 0) (h11 : p 1 1) :\n"
          "    ∀ r < 2, ∀ s < 2, p r s := by\n"
          "  intro r hr s hs\n"
          "  interval_cases r <;> interval_cases s <;> assumption\n\n")
    for kind, fn, whole in (("CA", "caSB", "caOK"), ("CB", "cbRA", "cbOK")):
        t += f"theorem {whole.lower()}_all : {whole} bA oA nW nC tE tab blk = true := by\n"
        t += f"  have hn : nW = {n} := rfl\n"
        t += "  refine allLT_of_forall fun x hx => allLT_of_forall fun w hw => ?_\n"
        t += "  interval_cases x\n"
        for x in (0, 1):
            names = ca_names[(kind, x)]
            t += f"  · exact allFrom_true {nested_add('allFrom_add', names)} w (Nat.zero_le w) (by omega)\n"
        t += "\n"
    def chain(lemma, stmt, items):
        """sequential `have` steps with explicit literal counts (no unification against unknown
        sums, so the elaborator never unfolds the check functions)"""
        body = ""
        prev, tot = items[0][0], items[0][2]
        for q, (nm, lo, cnt) in enumerate(items[1:], start=1):
            assert lo == tot
            body += (f"  have h{q} : {stmt(tot + cnt)} :=\n"
                     f"    {lemma} (lo := 0) (a := {tot}) (b := {cnt}) {prev} {nm}\n")
            prev, tot = f"h{q}", tot + cnt
        body += f"  exact {prev}\n"
        return body
    for (r, s) in blocks:
        k = f"{r}{s}"
        names = row_names[k]
        rstmt = (lambda m, k=k, r=r, s=s: f"rowsChk nN bX bA bL oA oL cS eB hX onesX (objE nW lev i1 od {r} {s})"
                 f" col{k} phi{k} fac{k} 0 {m} = true")
        t += (f"theorem rows{k} : rowsChk nN bX bA bL oA oL cS eB hX onesX (objE nW lev i1 od {r} {s})\n"
              f"    col{k} phi{k} fac{k} 0 nN = true := by\n")
        t += chain("rowsChk_add", rstmt, names) + "\n"
        cst = (lambda m, k=k: f"colOK bL oL bX fac{k} col{k} 0 {m} = true")
        citems = []
        lo = 0
        for (clo, ccnt), nm in zip(chunk_ranges(N, chunks.get('cols_per_thm', N)), col_names[k]):
            citems.append((nm, clo, ccnt))
        t += f"theorem col_ok{k} : colOK bL oL bX fac{k} col{k} 0 nN = true := by\n"
        t += chain("colOK_add", cst, citems) + "\n"
    t += (f"/-- The level-{C['L']} bound for Lüders-form strategies. -/\n"
          "theorem gyni_le_lueders {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB]\n"
          "    [DecidableEq HB]\n"
          "    {W : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))\n"
          "      ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ}\n"
          "    (hW : IsProcess W) {P : Fin 2 → Fin 2 → Matrix HA HA ℂ} {Q : Fin 2 → Fin 2 → Matrix HB HB ℂ}\n"
          "    (hP : IsProjMeas P) (hQ : IsProjMeas Q) :\n"
          f"    gyniValue W (lChoi P) (lChoi Q) ≤ {p} / 2 ^ {kq} := by\n"
          "  obtain ⟨hw0, hw1, hw2, hL, hi10, hi11, hN⟩ := words_ok\n"
          "  have h := gyni_le_level (L := lev) (n := nW) (N := nN) (blk := blk) (fac := facF) (col := colF)\n"
          "    hN tab_ok cover_ok cw_len cw_te te_lt tab_shape caok_all cbok_all\n"
          "    (blocks4 len00 len01 len10 len11) (blocks4 sym00 sym01 sym10 sym11) trace_ok params_ok\n"
          "    ones_ok ⟨hw0, hw1, hw2, hL, hi10, hi11⟩\n"
          "    (blocks4 fac_len00 fac_len01 fac_len10 fac_len11)\n"
          "    (blocks4 col_len00 col_len01 col_len10 col_len11)\n"
          "    (blocks4 col_ok00 col_ok01 col_ok10 col_ok11)\n"
          "    (blocks4 rows00 rows01 rows10 rows11) hW hP hQ\n"
          f"  have hval : ((betaNum : ℤ) : ℝ) / (den : ℕ) = {p} / 2 ^ {kq} := by\n"
          "    norm_num [betaNum, den]\n"
          "  rwa [hval] at h\n\n")
    t += (f"/-- **The level-{C['L']} upper bound on GYNI** for every strategy (finite-dimensional process `W`\n"
          "and instruments `M`, `N`). -/\n"
          "theorem gyni_upper_bound {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI]\n"
          "    [Fintype BO] [DecidableEq AI] [DecidableEq BI]\n"
          "    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)\n"
          "    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)\n"
          "    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :\n"
          f"    gyniValue W M N ≤ {p} / 2 ^ {kq} := by\n"
          "  obtain ⟨nA, nB, P, Q, W', hP, hQ, hW', hval⟩ := exists_lueders_form W hW M hM N hN\n"
          "  rw [← hval]\n"
          "  exact gyni_le_lueders hW' hP hQ\n\n")
    t += (f"/-- Decimal form (rounded up) of the level-{C['L']} bound. -/\n"
          "theorem gyni_upper_bound_decimal {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI]\n"
          "    [Fintype BO] [DecidableEq AI] [DecidableEq BI]\n"
          "    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)\n"
          "    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)\n"
          "    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :\n"
          f"    gyniValue W M N ≤ {decs} := by\n"
          "  refine (gyni_upper_bound W hW M hM N hN).trans ?_\n"
          "  norm_num\n\n")
    t += f"end {ns}\n"
    files.append(("Main", write(os.path.join(outdir, "Main.lean"), t)))
    return files


def emit(C, outdir, Lname, src, rows_per_chunk=None, layout="single", chunks=None):
    chunks = chunks or {}
    """Write <outdir>/{Params,Phi_rs,Fac_rs,Col_rs,Checks...}.lean (namespace GYNIUpperBound.<Lname>)."""
    ns = f"GYNIUpperBound.{Lname}"
    mod = f"GYNIUpper.{Lname}"
    n, N, NC = C['n'], C['N'], C['NC']
    blocks = [(0, 0), (0, 1), (1, 0), (1, 1)]
    files = []
    # Params
    t = HEADER.format(src=src, what="Parameters, class words and class table.")
    t += f"import GYNIUpper.UBCheck\n\nnamespace {ns}\n\n"
    t += f"/-- Level. -/\ndef lev : Nat := {C['L']}\n/-- Number of words `2 lev + 1`. -/\ndef nW : Nat := {n}\n"
    t += f"/-- Block size `nW ^ 2`. -/\ndef nN : Nat := {N}\n/-- Number of classes. -/\ndef nC : Nat := {NC}\n"
    t += f"/-- Slot of the empty class. -/\ndef tE : Nat := {C['te']}\n"
    t += f"/-- Digit bits of the data rows. -/\ndef bA : Nat := {C['BA']}\n/-- Offset of the data digits. -/\ndef oA : Nat := {C['OA']}\n"
    t += f"/-- Digit bits of the factor rows. -/\ndef bL : Nat := {C['BL']}\n/-- Offset of the factor digits. -/\ndef oL : Nat := {C['OL']}\n"
    t += f"/-- Bits of the packing base `X = 2 ^ bX`. -/\ndef bX : Nat := {C['B']}\n"
    t += f"/-- Scale `c = 2 ^ (2 F)`. -/\ndef cS : Int := {C['c']}\n/-- Bound on the remainder entries. -/\ndef eB : Int := {C['eps']}\n"
    t += f"/-- Half base `2 ^ (bX - 1)`. -/\ndef hX : Int := {C['H']}\n"
    t += f"/-- `∑_(j < nN) X ^ j`. -/\ndef onesX : Int := {C['ones']}\n"
    t += f"/-- Denominator of the data. -/\ndef den : Nat := {C['den']}\n/-- `den / 64`. -/\ndef od : Int := {C['od']}\n"
    t += f"/-- Numerator of the bound: `β = betaNum / den`. -/\ndef betaNum : Int := {C['beta_num']}\n"
    t += f"/-- Index of the word `[x]`. -/\ndef i1 (x : Nat) : Nat := if x = 0 then {C['i1'][0]} else {C['i1'][1]}\n"
    t += "/-- The class words (slots). -/\ndef cw : List (List (Fin 2)) := [" + ", ".join(fin2_word(w) for w in C['classes']) + "]\n"
    t += "/-- Class table by slots: `tab[t][a] = a' + 1` iff the class of `(a, a')` is `cw[t]`. -/\n"
    t += "def tab : List (List Nat) := [\n  " + ",\n  ".join("[" + ", ".join(str(x) for x in row) + "]" for row in C['tab']) + "]\n"
    t += f"\nend {ns}\n"
    files.append(("Params", write(os.path.join(outdir, "Params.lean"), t)))
    for (r, s) in blocks:
        k = f"{r}{s}"
        t = HEADER.format(src=src, what=f"Packed rows of the data `Φ` of block `({r}, {s})`.")
        t += f"import GYNIUpper.UBCheck\n\nnamespace {ns}\n\nset_option maxRecDepth 100000\n\n"
        t += lean_nat_list(f"phi{k}", C['rows'][(r, s)])
        t += f"\nend {ns}\n"
        files.append((f"Phi{k}", write(os.path.join(outdir, f"Phi{k}.lean"), t)))
        t = HEADER.format(src=src, what=f"Packed rows of the factor `L` of block `({r}, {s})`.")
        t += f"import GYNIUpper.UBCheck\n\nnamespace {ns}\n\nset_option maxRecDepth 100000\n\n"
        t += lean_nat_list(f"fac{k}", C['lrows'][(r, s)])
        t += f"\nend {ns}\n"
        files.append((f"Fac{k}", write(os.path.join(outdir, f"Fac{k}.lean"), t)))
        t = HEADER.format(src=src, what=f"Packed columns of the factor `L` of block `({r}, {s})`.")
        t += f"import GYNIUpper.UBCheck\n\nnamespace {ns}\n\nset_option maxRecDepth 100000\n\n"
        t += lean_int_list(f"col{k}", C['PL'][(r, s)])
        t += f"\nend {ns}\n"
        files.append((f"Col{k}", write(os.path.join(outdir, f"Col{k}.lean"), t)))
    # Blocks
    t = HEADER.format(src=src, what="The four blocks.")
    t += f"import {mod}.Params\n" + "".join(f"import {mod}.Phi{r}{s}\n" for (r, s) in blocks)
    t += f"\nnamespace {ns}\n\n"
    t += "/-- The packed data rows of block `(r, s)`. -/\nnoncomputable def blk (r s : Nat) : List Nat :=\n"
    t += "  if r = 0 then (if s = 0 then phi00 else phi01) else (if s = 0 then phi10 else phi11)\n"
    t += f"\nend {ns}\n"
    files.append(("Blocks", write(os.path.join(outdir, "Blocks.lean"), t)))
    OPT = "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n"
    if layout == "split":
        return files + emit_split(C, outdir, Lname, src, ns, mod, OPT, rows_per_chunk, chunks)
    # class checks, symmetry, trace
    t = HEADER.format(src=src, what="Kernel checks: class table, class sums, symmetry, trace.")
    t += f"import {mod}.Blocks\n\nnamespace {ns}\n\n" + OPT
    t += "theorem tab_ok : tabOK (wordAt lev) nW cw tab = true := by decide +kernel\n\n"
    t += "theorem cover_ok : coverOK (wordAt lev) nW cw = true := by decide +kernel\n\n"
    t += "theorem cw_len : cw.length = nC := by decide +kernel\n\n"
    t += "theorem cw_te : cw.getD tE [] = [] := by decide +kernel\n\n"
    t += "theorem tab_shape : tabShapeOK nW nC tE tab = true := by decide +kernel\n\n"
    t += "theorem ones_ok : onesX = packZ (pw bX 1) (List.replicate nN 1) := by decide +kernel\n\n"
    t += ("theorem params_ok : 0 < cS ∧ 0 ≤ eB ∧ 2 * hX = pw bX 1 ∧ 2 * oA = 2 ^ bA ∧ 2 * oL = 2 ^ bL ∧\n"
          "    0 < od ∧ 64 * od = den ∧\n"
          "    2 * (cS * ((oA : Int) + od) + (nN : Int) * ((oL : Int) * (oL : Int)) + eB) < pw bX 1 := by\n"
          "  decide +kernel\n\n")
    t += ("theorem words_ok : wordAt lev lev = [] ∧ wordAt lev (i1 0) = [0] ∧ wordAt lev (i1 1) = [1] ∧\n"
          "    lev < nW ∧ i1 0 < nW ∧ i1 1 < nW ∧ nN = nW * nW := by decide +kernel\n\n")
    t += "theorem ca_ok : caOK bA oA nW nC tE tab blk = true := by decide +kernel\n\n"
    t += "theorem cb_ok : cbOK bA oA nW nC tE tab blk = true := by decide +kernel\n\n"
    for (r, s) in blocks:
        t += f"theorem len{r}{s} : (blk {r} {s}).length = nN := by decide +kernel\n\n"
        t += f"theorem sym{r}{s} : symOK bA (blk {r} {s}) [] 0 = true := by decide +kernel\n\n"
    t += ("theorem trace_ok : (traceSum bA (blk 0 0) 0 + traceSum bA (blk 0 1) 0 + traceSum bA (blk 1 0) 0\n"
          "    + traceSum bA (blk 1 1) 0 : Int) = betaNum + 4 * nN * oA := by decide +kernel\n\n")
    t += f"end {ns}\n"
    files.append(("ChkClass", write(os.path.join(outdir, "ChkClass.lean"), t)))
    # PSD checks per block
    rpc = rows_per_chunk or N
    for (r, s) in blocks:
        k = f"{r}{s}"
        t = HEADER.format(src=src, what=f"Kernel checks: `c A = L Lᵀ + E` for block `({r}, {s})`.")
        t += f"import {mod}.Params\nimport {mod}.Phi{k}\nimport {mod}.Fac{k}\nimport {mod}.Col{k}\n\nnamespace {ns}\n\n" + OPT
        t += f"theorem fac_len{k} : fac{k}.length = nN := by decide +kernel\n\n"
        t += f"theorem col_len{k} : col{k}.length = nN := by decide +kernel\n\n"
        t += f"theorem col_ok{k} : colOK bL oL bX fac{k} col{k} 0 nN = true := by decide +kernel\n\n"
        lo = 0; q = 0
        while lo < N:
            cnt = min(rpc, N - lo)
            t += (f"theorem rows{k}_{q} : rowsChk nN bX bA bL oA oL cS eB hX onesX (objE nW lev i1 od {r} {s})\n"
                  f"    col{k} phi{k} fac{k} {lo} {cnt} = true := by decide +kernel\n\n")
            lo += cnt; q += 1
        t += f"end {ns}\n"
        files.append((f"ChkPSD{k}", write(os.path.join(outdir, f"ChkPSD{k}.lean"), t)))
    for name, size in files:
        print(f"  wrote {Lname}/{name}.lean ({size/1e6:.2f} MB)")
    return files


if __name__ == "__main__" and len(sys.argv) > 2:
    # usage: export_lean.py averaged.pkl outdir Lname [F] [rows_per_theorem] [rows_per_file] [words_per_class_file]
    #        (or: export_lean.py --from-export export.pkl outdir Lname ... to reuse a pickled export)
    args = sys.argv[1:]
    if args[0] == "--from-export":
        with open(args[1], "rb") as f:
            C = pickle.load(f)
        src = "avg_L%d.pkl" % C['L']
        args = args[1:]
    else:
        C = main(args[0], args[1], args[2], int(args[3]) if len(args) > 3 else 24)
        src = os.path.basename(args[0])
    outdir, Lname = args[1], args[2]
    rpc = int(args[4]) if len(args) > 4 else None
    rpf = int(args[5]) if len(args) > 5 else None
    cab = int(args[6]) if len(args) > 6 else None
    cpt = int(args[7]) if len(args) > 7 else None
    chunks = {}
    if rpf:
        chunks['rows_per_file'] = rpf
    if cab:
        chunks['ca'] = cab
    if cpt:
        chunks['cols_per_thm'] = cpt
    emit(C, outdir, Lname, src, rpc, layout="split", chunks=chunks)
