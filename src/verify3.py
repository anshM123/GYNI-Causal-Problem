"""Stand-alone exact verification of a dihedral-basis certificate (certify3.py output); no SDP solver."""
import os, sys, pickle, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mc3
from certify2 import verify_exact

HERE = os.path.dirname(os.path.abspath(__file__))

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    a = ap.parse_args()
    t0 = time.time()
    with open(os.path.join(HERE, a.path), "rb") as f:
        C = pickle.load(f)
    M, rows, obj = mc3.build(C['L'], sym=True, verbose=False)
    assert len(C['lam_int']) == len(rows)
    ok, beta, worst = verify_exact(dict(M=M, eqs=rows), obj, C['lam_int'], C['D'])
    print(f"{a.path}: dihedral L={C['L']}: all dual blocks PD = {ok}; VERIFIED BOUND = {float(beta):.12f} "
          f"(= {beta.numerator}/{beta.denominator})  [{time.time()-t0:.1f}s]")
