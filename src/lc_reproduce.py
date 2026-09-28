"""Reproduce Liu-Chiribella bounds (sparse direct Clarabel formulation; low memory).

Single-trigger canonical instruments (party with m=2 outcomes, n=2 settings, trigger xi):
  input  I  = C^2 (qubit),  output O = O1 (x) O2 = C^2 (x) C^2
  x == xi : M_{a|x} = |a><a|_I (x) |a><a|_O1 (x) |xi><xi|_O2
  x != xi : M_{a|x} = (1/2) |Phi><Phi|_{I,O1} (x) |x><x|_O2      (Phi = |00>+|11>)
Piece (xi,eta) is evaluated on a valid process W'_{xi,eta} on these canonical spaces.

GYNI:  LC bound = min over single-trigger decompositions of sum of piece maxima
      = (by SDP/minimax duality) max over 4 processes W'_{xi eta} with marginal consistency.
"""
import os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "8"); os.environ.setdefault("MKL_NUM_THREADS", "8")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, mem_gb, peak_gb
start_watchdog(6.0)
import numpy as np
from pm_core import BlockProcessParam, kron, is_valid_process
ProcessParam = lambda nq: BlockProcessParam(nq, cq=[2, 5])
from sdp_sparse import SDP

ket = lambda i: np.eye(2)[:, [i]].astype(complex)
proj = lambda i: ket(i) @ ket(i).conj().T
PHI = (np.kron(ket(0), ket(0)) + np.kron(ket(1), ket(1)))
PHIP = PHI @ PHI.conj().T


def canon(xi, a, x):
    """Choi of canonical instrument element on I (x) O1 (x) O2 (8x8)."""
    if x == xi:
        return kron(proj(a), proj(a), proj(xi))
    return 0.5 * kron(PHIP, proj(x))


class Lin:
    """affine expression const + sum coef[var]*z"""
    def __init__(self, const=0.0, coef=None):
        self.const = const; self.coef = dict(coef or {})
    def __add__(self, o):
        if not isinstance(o, Lin): o = Lin(o)
        c = dict(self.coef)
        for k, v in o.coef.items(): c[k] = c.get(k, 0.0) + v
        return Lin(self.const + o.const, c)
    __radd__ = __add__
    def __mul__(self, s):
        return Lin(self.const * s, {k: v * s for k, v in self.coef.items()})
    __rmul__ = __mul__
    def __sub__(self, o):
        return self + (-1.0) * (o if isinstance(o, Lin) else Lin(o))


def expect(param, idx, X):
    const, vec = param.lin_functional(X)
    return Lin(const, {int(i): v for i, v in zip(idx, vec) if abs(v) > 1e-14})


def lc_gyni(weights=None, verbose=False):
    param = ProcessParam((1, 2, 1, 2))
    sdp = SDP()
    pieces = {(xi, eta): param.add_to_sdp(sdp) for xi in (0, 1) for eta in (0, 1)}
    cache = {}
    def P(xi, eta, a, b, x, y):
        key = (xi, eta, a, b, x, y)
        if key not in cache:
            cache[key] = expect(param, pieces[(xi, eta)], kron(canon(xi, a, x), canon(eta, b, y)))
        return cache[key]
    obj = Lin()
    for x in (0, 1):
        for y in (0, 1):
            w = 0.25 if weights is None else weights[x][y]
            obj = obj + w * P(x, y, y, x, x, y)
    for x in (0, 1):
        for y in (0, 1):
            for a in (0, 1):
                e = sum((P(x, y, a, b, x, y) for b in (0, 1)), Lin()) - sum((P(x, 1 - y, a, b, x, y) for b in (0, 1)), Lin())
                sdp.add_eq(e.coef, -e.const)
            for b in (0, 1):
                e = sum((P(x, y, a, b, x, y) for a in (0, 1)), Lin()) - sum((P(1 - x, y, a, b, x, y) for a in (0, 1)), Lin())
                sdp.add_eq(e.coef, -e.const)
    sdp.set_objective_min({k: -v for k, v in obj.coef.items()})
    res = sdp.solve("clarabel", verbose=verbose)
    res['value'] = obj.const - res['primal']
    return res, param, pieces


def single_trigger_value(coef, xi, eta, verbose=False):
    param = ProcessParam((1, 2, 1, 2))
    sdp = SDP()
    idx = param.add_to_sdp(sdp)
    obj = Lin()
    for a in (0, 1):
        for b in (0, 1):
            for x in (0, 1):
                for y in (0, 1):
                    if coef[a][b][x][y] != 0:
                        obj = obj + coef[a][b][x][y] * expect(param, idx, kron(canon(xi, a, x), canon(eta, b, y)))
    sdp.set_objective_min({k: -v for k, v in obj.coef.items()})
    res = sdp.solve("clarabel", verbose=verbose)
    res['value'] = obj.const - res['primal']
    return res, param, idx


if __name__ == "__main__":
    t0 = time.time()
    param = ProcessParam((1, 2, 1, 2))
    print("free params per process:", len(param.free), " mem %.3f GB" % mem_gb(), flush=True)
    rng = np.random.default_rng(0)
    Wr = param.W_from_c(rng.normal(size=len(param.free)) * 0.01)
    chk = is_valid_process(Wr, param.dims)
    print("random param validity:", {k: (round(v, 12) if isinstance(v, float) else v) for k, v in chk.items()}, flush=True)

    coef = np.zeros((2, 2, 2, 2))
    for a in (0, 1):
        for b in (0, 1):
            for x in (0, 1):
                for y in (0, 1):
                    if ((x == 0) or (a == y)) and ((y == 0) or (b == x)):
                        coef[a, b, x, y] = 0.25
    res, _, _ = single_trigger_value(coef, 1, 1)
    print("LGYNI canonical SDP value: %.6f  status %s  time %.1fs mem %.3f GB" % (res['value'], res['status'], res['time'], res['mem_gb']), flush=True)

    res, param, pieces = lc_gyni()
    print("GYNI LC joint value: %.6f status %s time %.1fs mem %.3f GB peak %.3f GB" % (res['value'], res['status'], res['time'], res['mem_gb'], peak_gb()), flush=True)
    np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lc_gyni_z.npy"), res['z'])
    print("total time %.1fs" % (time.time() - t0))
