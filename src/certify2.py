"""Exact dual certificate for the pure moment hierarchy (Gamma PSD + V2 [+ GYNI symmetry rows]).

For every z with rows l_i(z) = b_i and Gamma blocks G_k(z) >= 0:
   o.z = sum_i lam_i b_i - sum_k <Y_k, G_k(z)>  <=  beta := sum_i lam_i b_i
whenever Y_k (defined entrywise from lam by stationarity) is PSD.  lam is rational with a common denominator D;
PSD of Y_k is certified exactly by Sylvester's criterion (all leading principal minors > 0), computed with the
fraction-free Bareiss algorithm on the integer matrix D' * Y_k.
Validity of the symmetry rows: the group average of the moment matrices of transformed strategies satisfies them
and has the same objective (GYNI is invariant)."""
import os, sys, time, argparse, pickle
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb
start_watchdog(6.0, period=0.1)
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from fractions import Fraction
import mc2
from nssolve import solve_reduced, eq_matrix

HERE = os.path.dirname(os.path.abspath(__file__))


def bareiss_leading_minors(Mint):
    """Mint: list of lists of Python ints (square). Returns list of leading principal minors (exact) using
    fraction-free Gaussian elimination without pivoting (stops at the first zero pivot)."""
    n = len(Mint)
    A = [row[:] for row in Mint]
    minors = []
    prev = 1
    for k in range(n):
        piv = A[k][k]
        minors.append(piv)
        if piv == 0:
            break
        for i in range(k + 1, n):
            Aik = A[i][k]
            rowi = A[i]; rowk = A[k]
            for j in range(k + 1, n):
                rowi[j] = (rowi[j] * piv - Aik * rowk[j]) // prev
            rowi[k] = 0
        prev = piv
    return minors


def build(maxlen, sym, game="gyni"):
    nA, nB = 2, 2
    ws = mc2.all_words(2, maxlen)
    A = mc2.Party(2, [ws, ws]); B = mc2.Party(2, [ws, ws])
    system = mc2.build_system(A, B, use_canon=False, verbose=False)
    if sym:
        import symmetry
        system['eqs'] = system['eqs'] + symmetry.gyni_symmetry_rows(system['M'])
    coef = {"gyni": mc2.gyni_coef(), "lgyni": mc2.lgyni_coef()}[game]
    obj = mc2.objective(system['M'], coef)
    return system, obj


def exact_coef(x, maxden=64):
    f = Fraction(x).limit_denominator(maxden)
    assert abs(float(f) - x) < 1e-12, x
    return f


def verify_exact(system, obj, lam_int, D):
    """lam = lam_int / D. Returns (all_pd, beta Fraction, min leading-minor sign info)."""
    M = system['M']; n = M.nvar
    rows = system['eqs']
    # scale: row coefficients are multiples of 1/2 at most -> use S = 2 * lcm; objective multiples of 1/4
    SC = 8
    Sv = [0] * n              # SC * D * sum_i lam_i l_{i,v}   (integers)
    beta_num = 0              # SC * D * beta
    for li, (row, b_) in zip(lam_int, rows):
        if li == 0:
            continue
        bf = exact_coef(b_)
        beta_num += int(li * bf * SC)
        for v, c in row.items():
            cf = exact_coef(c)
            val = li * cf * SC
            assert val.denominator == 1
            Sv[v] += int(val)
    OF = [0] * n
    for v, c in obj.items():
        f = exact_coef(c) * SC * D
        assert f.denominator == 1
        OF[v] = int(f)
    all_pd = True
    worst = None
    for (rA, rB, nsz, off) in M.blocks:
        # <Y, dG/dz_v> = (Sv - OF)/(SC D); Y_ii = that, Y_ij = that/2  -> integer matrix 2*SC*D*Y
        Yint = [[0] * nsz for _ in range(nsz)]
        for j in range(nsz):
            for i in range(j + 1):
                v = off + j * (j + 1) // 2 + i
                val = Sv[v] - OF[v]
                if i == j:
                    Yint[i][i] = 2 * val
                else:
                    Yint[i][j] = Yint[j][i] = val
        minors = bareiss_leading_minors(Yint)
        pd = len(minors) == nsz and all(m > 0 for m in minors)
        all_pd &= pd
        # log10 of smallest ratio of consecutive minors (= pivot size) for info
        piv = [float(Fraction(minors[k], minors[k - 1] if k else 1)) / (2 * SC * D) for k in range(len(minors))]
        mp = min(piv)
        worst = mp if worst is None else min(worst, mp)
    beta = Fraction(beta_num, SC * D)
    return all_pd, beta, worst


def main(maxlen=2, sym=True, eps=1e-7, D=2 ** 50, game="gyni", save=None):
    t0 = time.time()
    system, obj = build(maxlen, sym, game)
    M = system['M']; n = M.nvar
    psd = system['psd']
    obj_eps = dict(obj)
    for (nn, terms, F0) in psd:
        for v, F in terms:
            tr = F.diagonal().sum()
            if tr != 0:
                obj_eps[v] = obj_eps.get(v, 0.0) + eps * tr
    res = solve_reduced(n, system['eqs'], psd, {k: -v for k, v in obj_eps.items()}, solver="clarabel", eps=1e-10)
    val = sum(c * res['z'][v] for v, c in obj.items())
    print(f"[L={maxlen} sym={sym} eps={eps}] {res['status']} primal(eps-obj) {-res['pobj']:.10f} dual {-res['dobj']:.10f} obj(z) {val:.10f} ({time.time()-t0:.1f}s)", flush=True)
    Ys = [Y + eps * np.eye(Y.shape[0]) for Y in res['duals']]
    print("  numerical min eig Y:", min(np.linalg.eigvalsh(Y).min() for Y in Ys), flush=True)
    ovec = np.zeros(n)
    for v, c in obj.items():
        ovec[v] += c
    u = np.zeros(n)
    for Y, (nn, terms, F0) in zip(Ys, psd):
        for v, F in terms:
            u[v] += (F.multiply(Y)).sum()
    # project u onto {u : N^T (o + u) = 0} (stationarity consistency), N = null space of the equality rows
    from nssolve import nullspace_uf
    z0_, Bm, _, _ = nullspace_uf(system['eqs'], n, verbose=False)
    Q, _ = np.linalg.qr(Bm)
    viol = Q.T @ (ovec + u)
    print(f"  stationarity violation before projection |N^T(o+u)| = {np.abs(viol).max():.2e}", flush=True)
    u = u - Q @ viol
    # recompute Y blocks from projected u and report min eigenvalue
    minev = []
    for (rA, rB, nsz, off) in M.blocks:
        Yb = np.zeros((nsz, nsz))
        for j in range(nsz):
            for i in range(j + 1):
                vv = off + j * (j + 1) // 2 + i
                if i == j:
                    Yb[i, i] = u[vv]
                else:
                    Yb[i, j] = Yb[j, i] = u[vv] / 2
        minev.append(np.linalg.eigvalsh(Yb).min())
    print(f"  after projection: min eig Y = {min(minev):.3e}", flush=True)
    rhs = ovec + u
    Aeq, beq = eq_matrix(system['eqs'], n)
    sol = spla.lsqr(Aeq.T.tocsr(), rhs, atol=1e-15, btol=1e-15, iter_lim=200000)
    lam = sol[0]
    r = Aeq.T @ lam - rhs
    print(f"  LSQR residual max {np.abs(r).max():.2e} (iters {sol[2]}); lam.b = {lam @ beq:.10f}", flush=True)
    lam_int = [int(round(x * D)) for x in lam]
    t1 = time.time()
    ok, beta, worst = verify_exact(system, obj, lam_int, D)
    print(f"EXACT: all Gamma-block duals PD (Sylvester/Bareiss): {ok}; smallest pivot ~{worst:.3e}; "
          f"CERTIFIED BOUND beta = {float(beta):.12f}  (exact check {time.time()-t1:.1f}s, total {time.time()-t0:.1f}s, peak {peak_gb():.2f} GB)", flush=True)
    if save:
        with open(os.path.join(HERE, save), "wb") as f:
            pickle.dump(dict(maxlen=maxlen, sym=sym, game=game, D=D, lam_int=lam_int, beta=beta, ok=ok), f)
    return ok, beta


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--maxlen", type=int, default=2)
    ap.add_argument("--nosym", action="store_true")
    ap.add_argument("--eps", type=float, default=1e-7)
    ap.add_argument("--game", default="gyni")
    ap.add_argument("--save", default=None)
    a = ap.parse_args()
    main(a.maxlen, not a.nosym, a.eps, game=a.game, save=a.save)
