"""Export a jexact.py strategy certificate (pickle) to a SELF-CONTAINED .npz file that verify_strategy.py can check
without any of the construction code: explicit integer party operators, pair list, integer coefficients, rational
instrument parameters."""
import os, sys, pickle, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from jmodel import JModel
from full_check_J import party_full

HERE = os.path.dirname(os.path.abspath(__file__))

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("pkl"); ap.add_argument("out")
    a = ap.parse_args()
    with open(os.path.join(HERE, a.pkl), "rb") as f:
        C = pickle.load(f)
    J = C['J']
    m = JModel(J, verbose=False)
    used = sorted({i for t, (ia, ib, ph) in enumerate(m.elems) if C['yi'][t] != 0 for i in (ia, ib)})
    remap = {e: n for n, e in enumerate(used)}
    R = np.zeros((len(used), 8 * J * J, 8 * J * J), dtype=np.int8)
    mim = np.zeros(len(used), dtype=np.int64)
    for n, e in enumerate(used):
        M = party_full(m, m.pel[e])
        Mi = np.rint(M).astype(np.int64)
        assert np.abs(M - Mi).max() < 1e-12 and np.abs(Mi).max() < 127
        R[n] = Mi
        mim[n] = m.pel[e]['nY']          # number of imaginary factors: operator = i^nY * R
    pairs, ys = [], []
    for t, (ia, ib, ph) in enumerate(m.elems):
        if C['yi'][t] != 0:
            pairs.append((remap[ia], remap[ib])); ys.append(int(C['yi'][t]))
    cs = C['cs']
    np.savez_compressed(os.path.join(HERE, a.out), J=J, R=R, mim=mim, pairs=np.array(pairs, dtype=np.int64),
                        y=np.array(ys, dtype=np.int64), D=np.array(C['D'], dtype=np.int64), k=np.array(C['k']),
                        c_num=np.array([c.numerator for c, s in cs], dtype=np.int64),
                        c_den=np.array([c.denominator for c, s in cs], dtype=np.int64),
                        s_num=np.array([s.numerator for c, s in cs], dtype=np.int64),
                        s_den=np.array([s.denominator for c, s in cs], dtype=np.int64),
                        claimed_value_num=np.array(str(C['value'].numerator)),
                        claimed_value_den=np.array(str(C['value'].denominator)))
    print(f"exported {a.pkl} -> {a.out}: J={J}, {len(used)} party operators, {len(pairs)} pair terms")
