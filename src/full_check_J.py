"""Independent FULL-SPACE check of a saved J-block strategy (float): assemble W' on
A_I (x) A_O (x) B_I (x) B_O with A_I = (q_in, l_in), A_O = (q_out, l_out, reg) from the saved integer coefficients,
then check (i) Hermitian, (ii) min eigenvalue, (iii) the Araujo et al. validity projector conditions, (iv) Tr W,
(v) normalisation for random product channels, (vi) GYNI value with the explicit Lueders instruments."""
import os, sys, pickle, time, argparse
os.environ.setdefault("OMP_NUM_THREADS", "3"); os.environ.setdefault("MKL_NUM_THREADS", "3")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb, mem_gb
start_watchdog(3.0, period=0.1)
import numpy as np
from jmodel import JModel, PR
from pm_core import is_valid_process
import strategies as S

HERE = os.path.dirname(os.path.abspath(__file__))


def party_full(m, e):
    """full real matrix (with i-phase bookkeeping handled by caller) of a party element in order
    (q_in, l_in, q_out, l_out, reg)."""
    J = m.J
    Lm = m.LB[e['li']][1]                     # (l_in, l_out) J^2 x J^2
    Rg = PR[e['rg']] if e['rg'] == 3 else np.eye(2)
    # kron order (q_in, q_out, reg, l_in, l_out)
    M = np.kron(np.kron(np.kron(PR[e['qi']], PR[e['qo']]), Rg), Lm)
    d = [2, 2, 2, J, J]
    M = M.reshape(d + d)
    # permute to (q_in, l_in, q_out, l_out, reg)
    perm = [0, 3, 1, 4, 2]
    M = M.transpose(perm + [p + 5 for p in perm])
    n = 8 * J * J
    return M.reshape(n, n)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    a = ap.parse_args()
    t0 = time.time()
    with open(os.path.join(HERE, a.path), "rb") as f:
        C = pickle.load(f)
    J, cs, yi, D, k = C['J'], C['cs'], C['yi'], C['D'], C['k']
    m = JModel(J, verbose=False)
    n = 8 * J * J
    Dfull = n * n
    c0 = 1.0 / (4 * J * J)
    s = 2.0 ** -k
    W = c0 * np.eye(Dfull)
    cache = {}
    for t, q in enumerate(yi):
        if q == 0:
            continue
        ia, ib, ph = m.elems[t]
        for idx in (ia, ib):
            if idx not in cache:
                cache[idx] = party_full(m, m.pel[idx])
        term = np.kron(cache[ia], cache[ib])
        if ia != ib:
            term += np.kron(cache[ib], cache[ia])
        W += (1 - s) * (q / D) * ph * term
    print(f"assembled W' ({Dfull}x{Dfull}), {time.time()-t0:.1f}s, mem {mem_gb():.2f} GB", flush=True)
    dims = [2 * J, 4 * J, 2 * J, 4 * J]
    print("symmetric:", np.abs(W - W.T).max())
    chk = is_valid_process(W, dims, tol=1e-9)
    print(f"validity: c1 {chk['c1']:.2e} c2 {chk['c2']:.2e} c3 {chk['c3']:.2e}  min eig {chk['mineig']:.3e}  "
          f"trace err {chk['trace_err']:.2e}  ok={chk['ok']}", flush=True)
    rng = np.random.default_rng(1)
    worst = 0.0
    for _ in range(3):
        CA = S.random_channel_choi(2 * J, 4 * J, rng).real
        CB = S.random_channel_choi(2 * J, 4 * J, rng).real
        v = np.trace(W @ np.kron(CA, CB))
        worst = max(worst, abs(v - 1))
    print(f"random real product channels: max |Tr[W (C_A x C_B)] - 1| = {worst:.2e}", flush=True)
    # GYNI value with explicit Lueders instruments (float)
    ths = C['thetas']

    def lueders(a_, x_):
        P = np.zeros((2 * J, 2 * J))          # on H_A = (q, l)
        for l, t in enumerate(ths):
            sg = 1 if x_ == 1 else -1
            ph_ = np.array([np.cos(t / 2), sg * np.sin(t / 2)])
            P0 = np.outer(ph_, ph_)
            Pl = P0 if a_ == 0 else np.eye(2) - P0
            E = np.zeros((J, J)); E[l, l] = 1
            P += np.kron(Pl, E)
        v = np.zeros(4 * J * J)
        for i in range(2 * J):
            e = np.zeros(2 * J); e[i] = 1
            v += np.kron(e, P @ e)           # (q_in,l_in) (x) (q_out,l_out)
        reg = np.zeros(2); reg[x_] = 1
        v = np.kron(v, reg)
        return np.outer(v, v)
    val = 0.0
    for x in (0, 1):
        for y in (0, 1):
            val += 0.25 * np.trace(W @ np.kron(lueders(y, x), lueders(x, y)))
    print(f"GYNI value (float, full space): {val:.12f}  vs exact {float(C['value']):.12f}; total {time.time()-t0:.1f}s "
          f"peak {peak_gb():.2f} GB", flush=True)
