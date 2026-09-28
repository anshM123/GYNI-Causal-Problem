"""Lower bounds from the Lueders normal form with H_A = H_B = C^2 (one Jordan block):
Alice: A_0 = |0><0|, A_1 = |t><t| (angle tA); Lueders instruments + setting register; Bob likewise (angle tB).
For fixed angles the optimal process is an SDP on 2*4*2*4 = 64 dims (real, register-block-diagonal)."""
import os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "2"); os.environ.setdefault("MKL_NUM_THREADS", "2")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog
start_watchdog(3.0, period=0.1)
import numpy as np
from pm_core import BlockProcessParam, kron
from sdp_sparse import SDP
from lc_reproduce import Lin, expect


def lueders_choi(P, x):
    """Choi of rho -> P rho P (x) |x><x| on I (x) O (x) X (2 x 2 x 2)."""
    v = np.zeros(4)
    for i in range(2):
        e = np.zeros(2); e[i] = 1
        v += np.kron(e, P @ e)
    reg = np.zeros((2, 2)); reg[x, x] = 1
    return np.kron(np.outer(v, v), reg)


def projs(t):
    A0 = np.diag([1.0, 0.0])
    k = np.array([np.cos(t), np.sin(t)])
    A1 = np.outer(k, k)
    return [[A0, np.eye(2) - A0], [A1, np.eye(2) - A1]]


def value(tA, tB, param=None):
    param = param or BlockProcessParam((1, 2, 1, 2), cq=[2, 5])
    PA, PB = projs(tA), projs(tB)
    sdp = SDP()
    idx = param.add_to_sdp(sdp)
    obj = Lin()
    for x in (0, 1):
        for y in (0, 1):
            MA = lueders_choi(PA[x][y], x)     # a = y
            MB = lueders_choi(PB[y][x], y)     # b = x
            obj = obj + 0.25 * expect(param, idx, kron(MA, MB))
    sdp.set_objective_min({k: -v for k, v in obj.coef.items()})
    res = sdp.solve("clarabel", eps=1e-9, max_iter=200)
    return obj.const - res['primal'], res['status']


if __name__ == "__main__":
    param = BlockProcessParam((1, 2, 1, 2), cq=[2, 5])
    best = (0, None)
    t0 = time.time()
    for tA in np.linspace(0, np.pi / 2, 19):
        row = []
        for tB in np.linspace(0, np.pi / 2, 19):
            v, st = value(tA, tB, param)
            row.append(v)
            if v > best[0]:
                best = (v, (tA, tB))
        print(f"tA={tA:.3f}: " + " ".join(f"{v:.4f}" for v in row), flush=True)
    print("best grid", best, f"({time.time()-t0:.1f}s)")
    from scipy.optimize import minimize
    f = lambda t: -value(t[0], t[1], param)[0]
    r = minimize(f, np.array(best[1]), method="Nelder-Mead", options=dict(xatol=1e-6, fatol=1e-10))
    print("refined:", -r.fun, r.x)
