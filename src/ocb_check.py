"""OCB validity check at level 2: Alice words <= 2, Bob (4 settings) words = all words of length <= 1 plus the
length-2 words (r, xi) for register r (the words needed by the canonical images)."""
import os, sys
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb
start_watchdog(6.0, period=0.1)
import numpy as np
import mc2
from nssolve import solve_reduced

wsA = mc2.all_words(2, 2)
A = mc2.Party(2, [wsA, wsA])
B = mc2.Party(4, [mc2.canonical_words(4, r) for r in range(4)])
system = mc2.build_system(A, B, use_canon=False)
obj = mc2.objective(system['M'], mc2.ocb_coef())
res = solve_reduced(system['M'].nvar, system['eqs'], system['psd'], {k: -v for k, v in obj.items()},
                    solver="clarabel", eps=1e-9, verbose_uf=True)
print(f"OCB level-2 (pure hierarchy): {res['status']} primal {-res['pobj']:.10f} dual {-res['dobj']:.10f}; "
      f"quantum value (2+sqrt2)/4 = {(2 + np.sqrt(2)) / 4:.10f}; peak {peak_gb():.2f} GB", flush=True)
