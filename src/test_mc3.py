"""Tests for the dihedral-basis hierarchy: V2 rows on genuine strategies, symmetry maps vs transformed strategies."""
import os, sys
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("MKL_NUM_THREADS", "2")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog
start_watchdog(4.0, period=0.1)
import numpy as np
import mc3
from mc2 import BlockMoment, all_words
from genuine import random_valid, random_proj, z_from_strategy

for L in (2, 3):
    ws = all_words(2, L)
    A = mc3.OParty(2, [ws, ws]); B = mc3.OParty(2, [ws, ws])
    M = BlockMoment(A, B)
    rows = mc3.v2_rows(M)
    gm = mc3.group_maps(M)
    rng = np.random.default_rng(10 + L)
    for d, rk in [(2, 1), (3, 1), (4, 2)]:
        W = random_valid([d, 2 * d, d, 2 * d], rng, frac=1.0)
        PA = [random_proj(d, rk, rng) for _ in range(2)]
        PB = [random_proj(d, rk, rng) for _ in range(2)]
        OA = [2 * P - np.eye(d) for P in PA]; OB = [2 * P - np.eye(d) for P in PB]
        z = z_from_strategy(M, W, OA, OB)
        res = max(abs(sum(c * z[v] for v, c in row.items()) - rhs) for row, rhs in rows)
        # objective vs direct
        obj = mc3.objective(M, __import__('mc2').gyni_coef())
        val = sum(c * z[v] for v, c in obj.items())
        # direct GYNI via idempotent basis
        import mc2
        Mi = BlockMoment(mc2.Party(2, [ws, ws]), mc2.Party(2, [ws, ws]))
        zi = z_from_strategy(Mi, W, PA, PB)
        obji = mc2.objective(Mi, mc2.gyni_coef())
        vali = sum(c * zi[v] for v, c in obji.items())
        # symmetry fx vs transformed strategy
        Xr = np.array([[0, 1], [1, 0]]); I2 = np.eye(2); Id = np.eye(d)
        U = np.kron(np.kron(np.kron(Id, Id), Xr), np.kron(np.kron(Id, Id), I2))
        z_fx = z_from_strategy(M, U @ W @ U.T, [OA[1], OA[0]], [-OB[0], -OB[1]])
        pA, sA, pB, sB, _ = gm['fx']
        err = 0.0
        for (rA, rB, nsz, off) in M.blocks:
            ks = A.reg_members[rA]; ls = B.reg_members[rB]; nl = len(ls)
            for jj in range(nsz):
                for ii in range(jj + 1):
                    k, l = ks[ii // nl], ls[ii % nl]; kp, lp = ks[jj // nl], ls[jj % nl]
                    v0 = off + jj * (jj + 1) // 2 + ii
                    pred = sA[k] * sB[l] * sA[kp] * sB[lp] * z[M.entry(pA[k], pB[l], pA[kp], pB[lp])]
                    err = max(err, abs(pred - z_fx[v0]))
        U2 = np.kron(np.kron(np.kron(Id, Id), I2), np.kron(np.kron(Id, Id), Xr))
        z_fy = z_from_strategy(M, U2 @ W @ U2.T, [-OA[0], -OA[1]], [OB[1], OB[0]])
        pA, sA, pB, sB, _ = gm['fy']
        err2 = 0.0
        for (rA, rB, nsz, off) in M.blocks:
            ks = A.reg_members[rA]; ls = B.reg_members[rB]; nl = len(ls)
            for jj in range(nsz):
                for ii in range(jj + 1):
                    k, l = ks[ii // nl], ls[ii % nl]; kp, lp = ks[jj // nl], ls[jj % nl]
                    v0 = off + jj * (jj + 1) // 2 + ii
                    pred = sA[k] * sB[l] * sA[kp] * sB[lp] * z[M.entry(pA[k], pB[l], pA[kp], pB[lp])]
                    err2 = max(err2, abs(pred - z_fy[v0]))
        print(f"L={L} d={d} rk={rk}: #V2 {len(rows)} max residual {res:.1e}; GYNI O-basis {val:.10f} vs idempotent {vali:.10f}; "
              f"fx map err {err:.1e}, fy map err {err2:.1e}", flush=True)
