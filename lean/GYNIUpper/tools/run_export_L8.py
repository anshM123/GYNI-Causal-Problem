"""Level-8 export driver: builds the Cholesky certificates, runs all mirror checks, pickles the result
(GYNIUpper/data/export_L8.pkl) for the Lean emission step. Memory-capped at 3 GB."""
import os, sys, time, pickle
sys.dont_write_bytecode = True  # never write caches into the source repository
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.abspath(os.path.join(HERE, "..", "..", "..", "publish", "GYNI-Causal-Problem", "src")))
from memguard import start_watchdog, peak_gb
start_watchdog(3.0, period=0.2)
sys.set_int_max_str_digits(0)
import export_lean

if __name__ == "__main__":
    F = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    t0 = time.time()
    C = export_lean.main(os.path.join(HERE, "..", "data", "avg_L8.pkl"), os.path.join(HERE, "..", "L8"), "L8", F)
    with open(os.path.join(HERE, "..", "data", "export_L8.pkl"), "wb") as f:
        pickle.dump(C, f)
    print(f"done in {time.time()-t0:.1f}s, peak {peak_gb():.2f} GB", flush=True)
