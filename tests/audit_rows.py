"""Read the CERTIFIED row list (publish/GYNI-Causal-Problem/src/mc3.py, build(L, sym=True)) and cache it as a sparse
matrix.  The variable <-> Gamma-entry map is re-derived independently (documented storage convention) and
cross-checked against M.entry.  Nothing else from mc2/mc3 is used by the audit."""
import os, sys, time, pickle
import numpy as np
import scipy.sparse as sp

HERE = os.path.dirname(os.path.abspath(__file__))
PUB = os.path.normpath(os.path.join(HERE, "..", "src"))   # the certified code (mc3.py etc.)
CACHE = os.path.join(HERE, "cache")
os.makedirs(CACHE, exist_ok=True)


def my_var_map(basis, nset=2):
    """independent derivation: blocks ordered (rA,rB) lexicographic; block (rA,rB) indexes pairs (k,l) with
    reg(k)=rA, reg(l)=rB in basis order, local index pos(k)*|members(rB)| + pos(l); upper triangle i<=j stored at
    off + j(j+1)/2 + i.  Returns members, blocks [(rA,rB,nsz,off)], nvar."""
    members = [[i for i, (w, r) in enumerate(basis) if r == rr] for rr in range(nset)]
    blocks = []
    off = 0
    for rA in range(nset):
        for rB in range(nset):
            nsz = len(members[rA]) * len(members[rB])
            blocks.append((rA, rB, nsz, off))
            off += nsz * (nsz + 1) // 2
    return members, blocks, off


def load(L, rebuild=False, check_entries=True):
    path = os.path.join(CACHE, f"rows_L{L}.pkl")
    if os.path.exists(path) and not rebuild:
        with open(path, "rb") as f:
            return pickle.load(f)
    sys.path.insert(0, PUB)
    sys.dont_write_bytecode = True          # never write __pycache__ into publish/src (read-only for the audit)
    import mc3
    t0 = time.time()
    M, rows, obj = mc3.build(L, sym=True, verbose=True)
    # classify rows by provenance (same order as mc3.build: v2 rows first, then fx, fy, swap)
    nv2 = len(mc3.v2_rows(M))
    gm = mc3.group_maps(M)
    nfx = len(mc3.map_rows(M, gm['fx'])); nfy = len(mc3.map_rows(M, gm['fy'])); nsw = len(mc3.swap_rows(M))
    assert nv2 + nfx + nfy + nsw == len(rows)
    kind = np.array([0] * nv2 + [1] * nfx + [2] * nfy + [3] * nsw, dtype=np.int8)
    basis = list(M.A.basis)
    assert basis == list(M.B.basis)
    members, blocks, nvar = my_var_map(basis)
    assert nvar == M.nvar and [tuple(b) for b in blocks] == [tuple(b) for b in M.blocks], "block layout mismatch"
    # cross-check the entry map
    rng = np.random.default_rng(0)
    nchk = 0
    for (rA, rB, nsz, off) in blocks:
        ks, ls = members[rA], members[rB]
        nl = len(ls)
        idx = [(k, l) for k in ks for l in ls]
        pairs = [(i, j) for i in range(nsz) for j in range(nsz)] if nsz <= 100 else \
            [tuple(rng.integers(0, nsz, 2)) for _ in range(20000)]
        for (i, j) in pairs:
            (k, l), (kp, lp) = idx[i], idx[j]
            a, b = min(i, j), max(i, j)
            assert M.entry(k, l, kp, lp) == off + b * (b + 1) // 2 + a
            nchk += 1
    ri, ci, vv, rhs = [], [], [], []
    for n_, (row, b_) in enumerate(rows):
        for v, c in row.items():
            ri.append(n_); ci.append(v); vv.append(c)
        rhs.append(b_)
    A = sp.csr_matrix((vv, (ri, ci)), shape=(len(rows), nvar))
    ovec = np.zeros(nvar)
    for v, c in obj.items():
        ovec[v] += c
    D = dict(L=L, basis=basis, members=members, blocks=blocks, nvar=nvar, A=A, b=np.array(rhs), kind=kind,
             obj=ovec, nchk=nchk)
    with open(path, "wb") as f:
        pickle.dump(D, f)
    print(f"[rows L={L}] {len(rows)} rows (V2 {nv2}, fx {nfx}, fy {nfy}, swap {nsw}), nvar {nvar}, "
          f"entry-map checks {nchk}, {time.time()-t0:.1f}s", flush=True)
    return D


def z_from_gamma(R, G):
    """G: full (n*n) x (n*n) matrix indexed k*n + l (basis order).  Takes Re, keeps only register-diagonal blocks
    (twirl), returns the variable vector z and the list of blocks (real symmetric)."""
    n = len(R['basis'])
    z = np.zeros(R['nvar'])
    blocks = []
    Gr = G.real
    asym = np.abs(G - G.conj().T).max()          # Hermiticity of the genuine Gamma (diagnostic, not hidden)
    for (rA, rB, nsz, off) in R['blocks']:
        ks, ls = R['members'][rA], R['members'][rB]
        idx = np.array([k * n + l for k in ks for l in ls])
        Bk = Gr[np.ix_(idx, idx)]
        asym = max(asym, np.abs(Bk - Bk.T).max())
        iu, ju = np.triu_indices(nsz)
        z[off + ju * (ju + 1) // 2 + iu] = Bk[iu, ju]
        blocks.append((Bk + Bk.T) / 2)
    return z, blocks, asym


def evaluate(R, z, blocks=None):
    r = R['A'] @ z - R['b']
    out = dict(res_all=np.abs(r).max())
    for kk, name in enumerate(("v2", "fx", "fy", "swap")):
        m = R['kind'] == kk
        out["res_" + name] = np.abs(r[m]).max() if m.any() else 0.0
    out["obj"] = R['obj'] @ z
    if blocks is not None:
        out["mineig"] = min(np.linalg.eigvalsh(Bk).min() for Bk in blocks)
    out["argmax"] = int(np.argmax(np.abs(r)))
    return out


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=int, nargs="+", default=[2, 3, 4])
    a = ap.parse_args()
    for L in a.L:
        load(L, rebuild=True)
