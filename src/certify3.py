"""Exact certificate for the dihedral-basis symmetric hierarchy (mc3), any level L.

1. Solve the reduced problem (single PSD block (0,0), swap-split) with margin: max o + eps*Tr Gamma_00.
2. Yhat = eps*I + Qp Y+ Qp^T + Qm Y- Qm^T  (>= eps I) on block (0,0); spread to all four blocks with the signed
   permutations of the symmetry group: Y_k = S_k^T Yhat S_k / 4.
3. u_v = sum_k <Y_k, dGamma_k/dz_v>; project o+u onto the row space (remove null-space components); LSQR for the
   multipliers lambda of the FULL row list (V2 + symmetry + normalisation).
4. Round lambda to integers/2^50 and verify EXACTLY (certify2.verify_exact): Y_k re-defined by stationarity, all four
   blocks PD by Sylvester/Bareiss; bound beta = lambda.b."""
import os, sys, time, argparse, pickle
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb, mem_gb
start_watchdog(6.5, period=0.1)
import numpy as np
import scipy.sparse.linalg as spla
import mc3
from hier3 import solve_level
from nssolve import eq_matrix, nullspace_uf
from certify2 import verify_exact

HERE = os.path.dirname(os.path.abspath(__file__))


def main(L, eps=1e-6, D=2 ** 50, save=None, from_file=None, noproj=False):
    """If from_file is given, reuse the dual of a saved plain (no-margin) solve: since every diagonal entry of
    Gamma_00 is fixed to 1 by V2 (unitary words => TP x TP pairs), Tr Gamma_00 = N is constant on the feasible set,
    so Yhat = Y_opt + eps*I satisfies stationarity exactly as well as Y_opt does (cost eps*N in the bound)."""
    t0 = time.time()
    if from_file:
        with open(os.path.join(HERE, from_file), "rb") as f:
            R = pickle.load(f)
        assert R['L'] == L
        M, rows, obj = mc3.build(L, sym=True)
        psd, (Qp, Qm) = mc3.psd_block00_split(M)
        Yp, Ym = R['duals'][0], R['duals'][1]
        print(f"  loaded plain-solve dual from {from_file} (value {R['value']:.10f})", flush=True)
    else:
        M, rows, obj, res, (Qp, Qm) = solve_level(L, margin=eps, eps=1e-10)
        Yp, Ym = res['duals'][0], res['duals'][1]
    N0 = Qp.shape[0]
    Yhat = eps * np.eye(N0) + Qp @ Yp @ Qp.T + Qm @ Ym @ Qm.T
    print(f"  Yhat min eig {np.linalg.eigvalsh(Yhat).min():.3e}", flush=True)
    n = M.nvar
    u = np.zeros(n)
    for (rA, rB, nsz, off) in M.blocks:
        if (rA, rB) == (0, 0):
            Yk = Yhat / 4
        else:
            pi, s = mc3.block_signed_perm_from00(M, (rA, rB))
            Yk = (s[:, None] * s[None, :]) * Yhat[np.ix_(pi, pi)] / 4
        for j in range(nsz):
            for i in range(j + 1):
                v = off + j * (j + 1) // 2 + i
                u[v] = Yk[i, i] if i == j else 2 * Yk[i, j]
    ovec = np.zeros(n)
    for v, c in obj.items():
        ovec[v] += c
    if not noproj:
        x0, Bm, _, _ = nullspace_uf(rows, n, verbose=False)
        Q, _ = np.linalg.qr(Bm)
        viol = Q.T @ (ovec + u)
        print(f"  stationarity violation |N^T(o+u)| = {np.abs(viol).max():.2e} (nullity {Bm.shape[1]})", flush=True)
        u = u - Q @ viol
        del Q, Bm
    rhs = ovec + u
    Aeq, beq = eq_matrix(rows, n)
    sol = spla.lsqr(Aeq.T.tocsr(), rhs, atol=1e-16, btol=1e-16, iter_lim=500000)
    lam = sol[0]
    r = Aeq.T @ lam - rhs
    print(f"  LSQR residual {np.abs(r).max():.2e} iters {sol[2]}; lam.b = {lam @ beq:.12f}  mem {mem_gb():.2f} GB", flush=True)
    lam_int = [int(round(x * D)) for x in lam]
    system = dict(M=M, eqs=rows)
    t1 = time.time()
    ok, beta, worst = verify_exact(system, obj, lam_int, D)
    print(f"EXACT L={L}: all four Gamma-block duals PD: {ok}; smallest pivot ~{worst:.3e}; CERTIFIED beta = {float(beta):.12f} "
          f"(= {beta.numerator}/{beta.denominator}); exact check {time.time()-t1:.1f}s; total {time.time()-t0:.1f}s; "
          f"peak {peak_gb():.2f} GB", flush=True)
    if save:
        with open(os.path.join(HERE, save), "wb") as f:
            pickle.dump(dict(L=L, basis="dihedral", sym=True, D=D, lam_int=lam_int, beta=beta, ok=ok, eps=eps), f)
    return ok, beta


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=int, default=4)
    ap.add_argument("--eps", type=float, default=1e-6)
    ap.add_argument("--save", default=None)
    ap.add_argument("--from_file", default=None)
    ap.add_argument("--noproj", action="store_true")
    a = ap.parse_args()
    main(a.L, a.eps, save=a.save, from_file=a.from_file, noproj=a.noproj)
