"""Stand-alone exact verification of a saved hierarchy certificate (certify2.py output). No SDP solver used:
rebuilds the rows deterministically, recomputes the Gamma-block duals Y_k exactly from the rational multipliers
lam = lam_int / D, and checks Sylvester's criterion with exact integer (Bareiss) arithmetic."""
import os, sys, pickle, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from certify2 import build, verify_exact

HERE = os.path.dirname(os.path.abspath(__file__))

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    a = ap.parse_args()
    t0 = time.time()
    with open(os.path.join(HERE, a.path), "rb") as f:
        C = pickle.load(f)
    system, obj = build(C['maxlen'], C['sym'], C.get('game', 'gyni'))
    assert len(C['lam_int']) == len(system['eqs'])
    ok, beta, worst = verify_exact(system, obj, C['lam_int'], C['D'])
    print(f"{a.path}: L={C['maxlen']} sym={C['sym']}: dual blocks PD = {ok}; VERIFIED BOUND <= 0.{-((-beta.numerator * 10**12) // beta.denominator):012d} (rounded up) "
          f"(= {beta.numerator} / {beta.denominator})  [{time.time()-t0:.1f}s]")
