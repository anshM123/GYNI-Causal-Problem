"""Produce a dihedral-basis certificate (certify3.py of the GYNI repository) for a given level and margin.

The certificate is written to GYNIUpper/data/cert3_L<L>.pkl (same format as the shipped cert3_L*.pkl files:
L, basis, sym, D, lam_int, beta, ok, eps). Nothing is written into the source repository.
Usage: python make_cert.py L eps"""
import os, sys
sys.dont_write_bytecode = True  # never write caches into the source repository
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.abspath(os.path.join(HERE, "..", "..", "..", "publish", "GYNI-Causal-Problem", "src"))
sys.path.insert(0, SRC)
import certify3

if __name__ == "__main__":
    L = int(sys.argv[1]); eps = float(sys.argv[2])
    out = os.path.abspath(os.path.join(HERE, "..", "data", f"cert3_L{L}.pkl"))
    ok, beta = certify3.main(L, eps=eps, save=out)
    print("saved", out, "ok", ok, "beta", beta, float(beta))
