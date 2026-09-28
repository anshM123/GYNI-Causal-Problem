"""OCB validity check at an intermediate level: Alice words of length <= 1, Bob (4 settings) canonical words
(all letters + (r,xi))."""
import os, sys
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("MKL_NUM_THREADS", "2")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb
start_watchdog(4.0, period=0.1)
import numpy as np
import mc2
from nssolve import solve_reduced

wsA = mc2.all_words(2, 1)
A = mc2.Party(2, [wsA, wsA])
B = mc2.Party(4, [mc2.canonical_words(4, r) for r in range(4)])
system = mc2.build_system(A, B, use_canon=False)
obj = mc2.objective(system['M'], mc2.ocb_coef())
res = solve_reduced(system['M'].nvar, system['eqs'], system['psd'], {k: -v for k, v in obj.items()},
                    solver="clarabel", eps=1e-9, verbose_uf=True)
print(f"OCB level (A<=1, B canonical): {res['status']} primal {-res['pobj']:.10f} dual {-res['dobj']:.10f}; "
      f"quantum value (2+sqrt2)/4 = {(2 + np.sqrt(2)) / 4:.10f}; peak {peak_gb():.2f} GB", flush=True)
