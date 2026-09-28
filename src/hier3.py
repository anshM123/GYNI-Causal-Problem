"""Level-L moment hierarchy in the dihedral basis with full GYNI symmetry; single PSD block (0,0), swap-split."""
import os, sys, time, argparse, pickle
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb, mem_gb
start_watchdog(6.5, period=0.1)
import numpy as np
import mc3
from nssolve import solve_reduced

HERE = os.path.dirname(os.path.abspath(__file__))


def solve_level(L, game="gyni", solver="clarabel", eps=1e-9, margin=0.0, verbose=False, scs_iters=400000):
    t0 = time.time()
    M, rows, obj = mc3.build(L, game=game, sym=True)
    psd, (Qp, Qm) = mc3.psd_block00_split(M)
    print(f"  psd cones {[c[0] for c in psd]}  mem {mem_gb():.2f} GB  ({time.time()-t0:.1f}s)", flush=True)
    q = {k: -v for k, v in obj.items()}
    if margin:
        # + margin * Tr Gamma_00  (maximisation) -> q -= margin * dTr/dz
        rA, rB, nsz, off = M.blocks[0]
        for j in range(nsz):
            v = off + j * (j + 1) // 2 + j
            q[v] = q.get(v, 0.0) - margin
    res = solve_reduced(M.nvar, rows, psd, q, solver=solver, eps=eps, verbose=verbose, verbose_uf=True,
                        scs_iters=scs_iters)
    z = res['z']
    val = sum(c * z[v] for v, c in obj.items())
    print(f"HIER3 L={L} game={game} solver={solver} margin={margin}: {res['status']} obj(z) {val:.10f} "
          f"primal {-res['pobj']:.10f} dual {-res['dobj']:.10f} nullity {res['nullity']} "
          f"time {time.time()-t0:.1f}s peak {peak_gb():.2f} GB", flush=True)
    return M, rows, obj, res, (Qp, Qm)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=int, default=3)
    ap.add_argument("--game", default="gyni")
    ap.add_argument("--solver", default="clarabel")
    ap.add_argument("--eps", type=float, default=1e-9)
    ap.add_argument("--save", default=None)
    a = ap.parse_args()
    M, rows, obj, res, Q = solve_level(a.L, a.game, a.solver, a.eps)
    if a.save:
        with open(os.path.join(HERE, a.save), "wb") as f:
            pickle.dump(dict(L=a.L, z=res['z'], duals=res['duals'], value=-res['pobj']), f)
