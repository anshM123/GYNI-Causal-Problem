"""P-AUDIT: solve the CERTIFIED relaxation (rows of mc3.build(L, sym=True), four register blocks PSD) at low levels
with an independent cvxpy formulation, to check the README's statement about level 1 and the reported values."""
import os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "3"); os.environ.setdefault("MKL_NUM_THREADS", "3")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "3")
import numpy as np
import cvxpy as cp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit_rows as AR

for L in [int(a) for a in sys.argv[1:]] or [1, 2]:
    t0 = time.time()
    R = AR.load(L)
    z = cp.Variable(R['nvar'])
    cons = [R['A'] @ z == R['b']]
    for (rA, rB, nsz, off) in R['blocks']:
        X = cp.Variable((nsz, nsz), symmetric=True)
        iu, ju = np.triu_indices(nsz)
        cons += [X >> 0, X[iu, ju] == z[off + ju * (ju + 1) // 2 + iu]]
    prob = cp.Problem(cp.Maximize(R['obj'] @ z), cons)
    try:
        prob.solve(solver=cp.CLARABEL)
    except cp.error.SolverError:
        prob.solve(solver=cp.SCS, eps=1e-9, max_iters=200000)
    print(f"L={L}: {prob.status} value {prob.value:.8f}  ({time.time()-t0:.1f}s)", flush=True)
