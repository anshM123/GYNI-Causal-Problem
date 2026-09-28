"""Pure moment hierarchy (Gamma PSD + word-level validity V2; canonical images are implied) for GYNI-type games."""
import os, sys, argparse, time, pickle
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb
start_watchdog(6.0, period=0.1)
import numpy as np
import mc2
from nssolve import solve_reduced

HERE = os.path.dirname(os.path.abspath(__file__))

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--maxlen", type=int, default=2)
    ap.add_argument("--game", default="gyni")
    ap.add_argument("--solver", default="clarabel")
    ap.add_argument("--eps", type=float, default=1e-9)
    ap.add_argument("--canon", action="store_true")
    ap.add_argument("--save", default=None)
    ap.add_argument("--sym", action="store_true")
    a = ap.parse_args()
    nA, nB = (2, 4) if a.game == "ocb" else (2, 2)
    coef = {"gyni": mc2.gyni_coef(), "lgyni": mc2.lgyni_coef(), "ocb": mc2.ocb_coef()}[a.game]
    wsA = mc2.all_words(nA, a.maxlen); wsB = mc2.all_words(nB, a.maxlen)
    A = mc2.Party(nA, [wsA] * nA); B = mc2.Party(nB, [wsB] * nB)
    t = time.time()
    system = mc2.build_system(A, B, use_canon=a.canon)
    obj = mc2.objective(system['M'], coef)
    if a.sym:
        import symmetry
        system['eqs'] = system['eqs'] + symmetry.gyni_symmetry_rows(system['M'])
    res = solve_reduced(system['M'].nvar, system['eqs'], system['psd'], {k: -v for k, v in obj.items()},
                        solver=a.solver, eps=a.eps, scs_iters=300000, verbose_uf=True)
    print(f"HIER game={a.game} L={a.maxlen} canon={a.canon} sym={a.sym} solver={a.solver}: {res['status']} primal {-res['pobj']:.10f} "
          f"dual {-res['dobj']:.10f}  nullity {res['nullity']}  {time.time()-t:.1f}s  peak {peak_gb():.2f} GB", flush=True)
    if a.save:
        with open(os.path.join(HERE, a.save), "wb") as f:
            pickle.dump(dict(res=res, args=vars(a)), f)
