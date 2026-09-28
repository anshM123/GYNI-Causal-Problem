"""Lower bounds from the Lueders normal form with TWO Jordan blocks per party:
H_A = C^2 (Jordan qubit q) (x) C^2 (label l), A_0 = |0><0|_q (x) 1, A_1 = sum_j |t_j><t_j| (x) |j><j|.
Process on AI=(q_in,l_in), AO=(q_out,l_out,reg) per party (1024 dims).  WLOG (twirls that leave all instruments
invariant): real, diagonal in the registers, invariant under label phases U (x) conj(U) on (l_in,l_out) of each
party -> block diagonal in the charge sectors (j_in - j_out) of both parties.
Basis of invariant valid operators: products over the 5 qubit slots of each party of
q_in, q_out in {I,X,Y,Z}, reg in {I,Z}, label pair in {II, IZ, ZI, ZZ, XX-YY, XY+YX} (commutant of U (x) conj U)."""
import os, sys, time, itertools, argparse, pickle
os.environ.setdefault("OMP_NUM_THREADS", "4"); os.environ.setdefault("MKL_NUM_THREADS", "4")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from memguard import start_watchdog, peak_gb, mem_gb
start_watchdog(5.0, period=0.1)
import numpy as np
import scipy.sparse as sp
from pm_core import allowed
from sdp_sparse import SDP

I2 = sp.identity(2, format='csr', dtype=complex)
PX = sp.csr_matrix(np.array([[0, 1], [1, 0]], dtype=complex))
PY = sp.csr_matrix(np.array([[0, -1j], [1j, 0]], dtype=complex))
PZ = sp.csr_matrix(np.array([[1, 0], [0, -1]], dtype=complex))
P1 = [I2, PX, PY, PZ]
# label-pair operators as lists of (coef, P_lin, P_lout)
LABEL = {
    "II": [(1.0, 0, 0)], "IZ": [(1.0, 0, 3)], "ZI": [(1.0, 3, 0)], "ZZ": [(1.0, 3, 3)],
    "XXmYY": [(1.0, 1, 1), (-1.0, 2, 2)], "XYpYX": [(1.0, 1, 2), (1.0, 2, 1)],
}
LAB_IN = {"II": 0, "IZ": 0, "ZI": 1, "ZZ": 1, "XXmYY": 1, "XYpYX": 1}
LAB_OUT = {"II": 0, "IZ": 1, "ZI": 0, "ZZ": 1, "XXmYY": 1, "XYpYX": 1}
LAB_IM = {"II": 0, "IZ": 0, "ZI": 0, "ZZ": 0, "XXmYY": 0, "XYpYX": 1}


def skron(ops):
    out = ops[0]
    for o in ops[1:]:
        out = sp.kron(out, o, format='csr')
    return out


def party_elements():
    """list of (terms, pattern_in, pattern_out, imag_parity) for one party; terms: list of (coef, [5 Pauli idx])
    qubit order: q_in, l_in, q_out, l_out, reg"""
    out = []
    for qi in range(4):
        for qo in range(4):
            for rg in (0, 3):
                for lab, terms in LABEL.items():
                    pin = (qi != 0) or LAB_IN[lab]
                    pout = (qo != 0) or (rg != 0) or LAB_OUT[lab]
                    im = (qi == 2) + (qo == 2) + LAB_IM[lab]
                    tl = [(c, [qi, li, qo, lo, rg]) for (c, li, lo) in terms]
                    out.append((tl, bool(pin), bool(pout), im % 2))
    return out


class J2Model:
    def __init__(self):
        t0 = time.time()
        pe = party_elements()
        self.D = 1024
        elems = []
        for (ta, ain, aout, aim), (tb, bin_, bout, bim) in itertools.product(pe, pe):
            pat = [ain, aout, bin_, bout]
            if not any(pat):
                continue
            if not allowed(pat):
                continue
            if (aim + bim) % 2:
                continue
            elems.append((ta, tb))
        self.elems = elems
        # sector structure: basis index bits for qubits [qA_in, lA_in, qA_out, lA_out, rA, qB_in, lB_in, qB_out, lB_out, rB]
        idx = np.arange(self.D)
        bit = lambda q: (idx >> (9 - q)) & 1
        chA = bit(1) - bit(3); chB = bit(6) - bit(8)
        rA = bit(4); rB = bit(9)
        keys = list(zip(rA, chA, rB, chB))
        sectors = {}
        for i, k in enumerate(keys):
            sectors.setdefault(k, []).append(i)
        self.sectors = [np.array(v) for k, v in sorted(sectors.items())]
        self.c0 = 64.0 / self.D   # Tr W = dAO dBO = 8*8
        # matrices
        self.mats = []
        for ta, tb in elems:
            M = None
            for ca, pa in ta:
                for cb, pb in tb:
                    op = ca * cb * skron([P1[i] for i in pa + pb])
                    M = op if M is None else M + op
            M = M.tocsr()
            assert abs(M - M.conj().T).max() < 1e-12
            if abs(M.imag).max() > 1e-12:
                assert abs(M.real).max() < 1e-12
                raise ValueError("imaginary element slipped through")
            self.mats.append(M.real.tocsr())
        # check invariance/block structure: off-sector entries must vanish
        sec_of = np.empty(self.D, dtype=np.int64)
        for s, ind in enumerate(self.sectors):
            sec_of[ind] = s
        for M in self.mats[:200]:
            Mc = M.tocoo()
            assert np.all(sec_of[Mc.row] == sec_of[Mc.col]), "element not block diagonal"
        self.blocks = []
        for ind in self.sectors:
            self.blocks.append([M[ind][:, ind].tocsr() for M in self.mats])
        print(f"[J2Model] {len(self.mats)} invariant valid basis elements, {len(self.sectors)} sector blocks "
              f"sizes {sorted(set(len(s) for s in self.sectors))}, {time.time()-t0:.1f}s, mem {mem_gb():.2f} GB", flush=True)

    def omega(self, thA, thB):
        """GYNI performance operator (1024x1024 real) for Jordan angles thA=(t0,t1), thB."""
        def lueders_vecs(th):
            A0 = np.kron(np.diag([1.0, 0.0]), np.eye(2))
            A1 = np.zeros((4, 4))
            for j, t in enumerate(th):
                k = np.array([np.cos(t), np.sin(t)])
                A1 += np.kron(np.outer(k, k), np.diag([1.0 - j, float(j)]))
            P = {(0, 0): A0, (1, 0): np.eye(4) - A0, (0, 1): A1, (1, 1): np.eye(4) - A1}
            vecs = {}
            for (a, x), Pm in P.items():
                v = np.zeros(4 * 4)
                for i in range(4):
                    e = np.zeros(4); e[i] = 1
                    v += np.kron(e, Pm @ e)
                # qubit order in: (q_in, l_in); out: (q_out, l_out); then reg
                reg = np.zeros(2); reg[x] = 1
                vecs[(a, x)] = np.kron(v, reg)
            return vecs
        va, vb = lueders_vecs(thA), lueders_vecs(thB)
        Om = np.zeros((self.D, self.D))
        for x in (0, 1):
            for y in (0, 1):
                u = np.kron(va[(y, x)], vb[(x, y)])
                Om += 0.25 * np.outer(u, u)
        return Om

    def value(self, thA, thB, return_W=False):
        Om = self.omega(thA, thB)
        sdp = SDP()
        idx = sdp.add_vars(len(self.mats))
        for b, ind in enumerate(self.sectors):
            n = len(ind)
            terms = [(int(i), self.blocks[b][j]) for j, i in enumerate(idx) if self.blocks[b][j].nnz]
            sdp.add_psd(n, terms, sp.identity(n, format='csr') * self.c0)
        q = {int(i): -float(M.multiply(Om).sum()) for i, M in zip(idx, self.mats)}
        sdp.set_objective_min(q)
        res = sdp.solve("clarabel", eps=1e-8, max_iter=300)
        const = self.c0 * np.trace(Om)
        val = const - res['primal']
        if return_W:
            return val, res
        return val, res['status']


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--starts", type=int, default=4)
    a = ap.parse_args()
    model = J2Model()
    t = 0.62943
    v, st = model.value((t, t), (t, t))
    print(f"check J=1 embedding (equal angles {t}): {v:.8f} [{st}] (expected 0.6067069)", flush=True)
    from scipy.optimize import minimize
    rng = np.random.default_rng(0)
    best = (0, None)
    for s in range(a.starts):
        x0 = rng.uniform(0.1, 1.4, size=2) if s else np.array([0.4, 0.9])
        def f(th):
            try:
                v = model.value(tuple(th), tuple(th))[0]
            except Exception as e:
                print('   eval failed', th, e, flush=True); v = 0.0
            print(f'   eval {th} -> {v:.8f}', flush=True)
            return -v
        r = minimize(f, x0, method="Nelder-Mead", options=dict(xatol=1e-3, fatol=1e-7, maxfev=60))
        print(f"start {s}: symmetric angles {r.x} -> {-r.fun:.8f}  ({r.nfev} evals)", flush=True)
        if -r.fun > best[0]:
            best = (-r.fun, r.x)
    print("best symmetric J=2:", best, f"peak {peak_gb():.2f} GB")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lueders_J2_best.pkl"), "wb") as f:
        pickle.dump(dict(value=best[0], angles=best[1]), f)
