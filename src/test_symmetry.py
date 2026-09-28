"""Check symmetry maps against explicitly transformed genuine strategies, then solve L=2 with symmetry."""
import os, sys
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("MKL_NUM_THREADS", "2")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog
start_watchdog(4.0, period=0.1)
import numpy as np
import mc2, symmetry
from genuine import random_valid, random_proj, z_from_strategy
from nssolve import solve_reduced

ws = mc2.all_words(2, 2)
A = mc2.Party(2, [ws, ws]); B = mc2.Party(2, [ws, ws])
system = mc2.build_system(A, B, use_canon=False, verbose=False)
M = system['M']
rng = np.random.default_rng(5)
d = 2
W = random_valid([d, 2 * d, d, 2 * d], rng)
PA = [random_proj(d, 1, rng) for _ in range(2)]
PB = [random_proj(d, 1, rng) for _ in range(2)]
z = z_from_strategy(M, W, PA, PB)


def apply_rows(rows, z):
    # rows: z'_v0 - z_v0 = 0 represented as (sum_terms) - z_v0 ; we recover z'_v0 = sum_terms (excluding the -1 on v0)
    return rows


# explicit transformed strategies
Xr = np.array([[0, 1], [1, 0]])
I2 = np.eye(2); Id = np.eye(d)
# s_fx: register flip on Alice output register (factor order [HA, HA, X, HB, HB, Y])
U = np.kron(np.kron(np.kron(Id, Id), Xr), np.kron(np.kron(Id, Id), I2))
W_fx = U @ W @ U.T
z_fx = z_from_strategy(M, W_fx, [PA[1], PA[0]], [np.eye(d) - PB[0], np.eye(d) - PB[1]])
# s_fy
U = np.kron(np.kron(np.kron(Id, Id), I2), np.kron(np.kron(Id, Id), Xr))
W_fy = U @ W @ U.T
z_fy = z_from_strategy(M, W_fy, [np.eye(d) - PA[0], np.eye(d) - PA[1]], [PB[1], PB[0]])
# swap: W on [A-part (d*2d), B-part (d*2d)] -> swap
nA_ = d * 2 * d
Ws = W.reshape(nA_, nA_, nA_, nA_).transpose(1, 0, 3, 2).reshape(nA_ ** 2, nA_ ** 2)
z_sw = z_from_strategy(M, Ws, PB, PA)

ident = {0: {(0,): 1.0}, 1: {(1,): 1.0}}
swapl = {0: {(1,): 1.0}, 1: {(0,): 1.0}}
compl = {0: {(): 1.0, (0,): -1.0}, 1: {(): 1.0, (1,): -1.0}}


def predicted(rows, z):
    zp = np.array(z, copy=True)
    for row, _ in rows:
        # find the diagonal -1 variable: the one with coefficient -1 that is the target; recompute
        pass
    return zp


for name, TA, TB, swap, ztrue in [("fx", symmetry.party_transform(A, swapl, [1, 0]), symmetry.party_transform(B, compl, [0, 1]), False, z_fx),
                                   ("fy", symmetry.party_transform(A, compl, [0, 1]), symmetry.party_transform(B, swapl, [1, 0]), False, z_fy),
                                   ("swap", None, None, True, z_sw)]:
    if swap:
        pred = np.zeros_like(z)
        for (rA, rB, nsz, off) in M.blocks:
            ks = A.reg_members[rA]; ls = B.reg_members[rB]
            for jj in range(nsz):
                for ii in range(jj + 1):
                    k_, l_ = ks[ii // len(ls)], ls[ii % len(ls)]; kp_, lp_ = ks[jj // len(ls)], ls[jj % len(ls)]
                    pred[off + jj * (jj + 1) // 2 + ii] = z[M.entry(l_, k_, lp_, kp_)]
        print(f'{name}: max |predicted - true transformed Gamma| = {np.abs(pred - ztrue).max():.2e}')
        continue
    rows = symmetry.gamma_map_rows(M, TA, TB, swap=swap)
    # each row: sum_terms(z) - z_target = 0 for the transformed Gamma'; evaluate sum_terms on z (original) and compare
    # with ztrue at the target variable. Target = the variable with coefficient -1 that is listed last (v0).
    err = 0.0
    for (row, _), (rA, rB, nsz, off) in zip(rows, []):
        pass
    # simpler: rebuild prediction entrywise
    pred = np.zeros_like(z)
    k = 0
    for (rA, rB, nsz, off) in M.blocks:
        for jj in range(nsz):
            for ii in range(jj + 1):
                row, _ = rows[k]; k += 1
                v0 = off + jj * (jj + 1) // 2 + ii
                val = sum(c * z[v] for v, c in row.items() if v != v0) + (row.get(v0, 0.0) + 1.0) * z[v0]
                pred[v0] = val
    print(f"{name}: max |predicted - true transformed Gamma| = {np.abs(pred - ztrue).max():.2e}")

rows = symmetry.gyni_symmetry_rows(M)
obj = mc2.objective(M, mc2.gyni_coef())
res = solve_reduced(M.nvar, system['eqs'] + rows, system['psd'], {k: -v for k, v in obj.items()}, solver="clarabel", eps=1e-9)
print(f"L=2 with GYNI symmetry: {res['status']} primal {-res['pobj']:.10f} dual {-res['dobj']:.10f} nullity {res['nullity']}")
