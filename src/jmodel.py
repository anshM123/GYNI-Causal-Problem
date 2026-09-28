"""General-J Lueders family: H_A = C^2 (Jordan qubit q) (x) C^J (label l), BISECTOR basis in each Jordan block:
   A_0 = sum_j |phi_j^-><phi_j^-| (x) |j><j|,  A_1 = sum_j |phi_j^+><phi_j^+| (x) |j><j|,  phi_j^+- = (cos(t_j/2), +-sin(t_j/2)).
Lueders instruments + setting register.  Same angles for Alice and Bob (so party swap is a symmetry).
Exact SDP over valid W for fixed instruments, reduced by (all WLOG, value-preserving, validity-preserving):
  - register twirl (block diagonal in registers), realness (real instruments),
  - label phase twirl U (x) conj(U) on (l_in, l_out) of each party (commutant basis below),
  - GYNI group: fx = [Z on Alice's q_in,q_out + Alice register flip] x [R90 on Bob's q_in,q_out];
                fy = mirror image; swap.  In the bisector basis these act by theta-independent signs.
=> W = c0*1 + sum_t c_t E_t, E_t = a(x)b + b(x)a over allowed-pattern party elements with fx/fy signs +1.
PSD needed only on register block (0,0) and sector blocks (cA <= cB); objective = <u_00|W|u_00>."""
import os, sys, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sp
from pm_core import allowed

PR = [np.eye(2), np.array([[0., 1.], [1., 0.]]), np.array([[0., -1.], [1., 0.]]), np.diag([1., -1.])]
# real parts; Pauli Y = i * PR[2]  (imaginary flag)
SIGN_Z = [1, -1, -1, 1]     # conjugation by Z:   X->-X, Y->-Y
SIGN_R = [1, -1, 1, -1]     # conjugation by R90: X->-X, Z->-Z


def label_basis(J):
    """list of (name, M_real (J^2 x J^2), pin, pout, imag) for the commutant of U (x) conj(U) on (l_in,l_out)."""
    I = np.eye(J)
    D = []
    for k in range(1, J):
        d = np.zeros(J); d[:k] = 1.0; d[k] = -k
        D.append(np.diag(d))
    out = [("I", np.kron(I, I), 0, 0, 0)]
    for k, Dk in enumerate(D):
        out.append((f"Din{k}", np.kron(Dk, I), 1, 0, 0))
        out.append((f"Dout{k}", np.kron(I, Dk), 0, 1, 0))
    for k, Dk in enumerate(D):
        for m, Dm in enumerate(D):
            out.append((f"DD{k}{m}", np.kron(Dk, Dm), 1, 1, 0))
    for a in range(J):
        for c in range(a + 1, J):
            E = np.zeros((J, J)); E[a, c] = 1.0
            X = np.kron(E, E)
            out.append((f"S{a}{c}", X + X.T, 1, 1, 0))
            out.append((f"A{a}{c}", X - X.T, 1, 1, 1))     # i*(X - X^T) is Hermitian; stored real part (antisym)
    assert len(out) == 2 * J * J - J
    return out


class JModel:
    def __init__(self, J, verbose=True):
        t0 = time.time()
        self.J = J
        LB = label_basis(J)
        self.LB = LB
        # party elements
        pel = []
        for qi in range(4):
            for qo in range(4):
                for rg in (0, 3):
                    for li, (nm, Lm, lpin, lpout, lim) in enumerate(LB):
                        pin = int(qi != 0 or lpin)
                        pout = int(qo != 0 or rg != 0 or lpout)
                        im = ((qi == 2) + (qo == 2) + lim) % 2
                        sZ = SIGN_Z[qi] * SIGN_Z[qo] * (-1 if rg == 3 else 1)   # Z-conj + register flip
                        sR = SIGN_R[qi] * SIGN_R[qo]                             # R90-conj
                        nY = (qi == 2) + (qo == 2) + lim
                        pel.append(dict(qi=qi, qo=qo, rg=rg, li=li, pin=pin, pout=pout, im=im, sZ=sZ, sR=sR, nY=nY))
        self.pel = pel
        # sectors of one party: 0 = charge-0 (basis |jj>), then (j,k) j != k
        self.sectors = [("0", [(j, j) for j in range(J)])] + [(f"{j}{k}", [(j, k)]) for j in range(J) for k in range(J) if j != k]
        # restricted party matrices for register r in {0,1}: kron(Pq_in (x) Pq_out, L_c) * <r|P_rg|r> * (i factors real part)
        self.rest = {}
        for e_idx, e in enumerate(pel):
            Pq = np.kron(PR[e['qi']], PR[e['qo']])
            Lm = LB[e['li']][1]
            for r in (0, 1):
                regf = 1.0 if (e['rg'] == 0 or r == 0) else -1.0
                for s_idx, (nm, st) in enumerate(self.sectors):
                    idx = [a * J + b for (a, b) in st]
                    Lc = Lm[np.ix_(idx, idx)]
                    self.rest[(e_idx, r, s_idx)] = regf * np.kron(Pq, Lc)
        # invariant pair elements
        elems = []
        n = len(pel)
        for ia in range(n):
            a = pel[ia]
            for ib in range(ia, n):
                b = pel[ib]
                pat = [bool(a['pin']), bool(a['pout']), bool(b['pin']), bool(b['pout'])]
                if not any(pat) or not allowed(pat):
                    continue
                if (a['im'] + b['im']) % 2:
                    continue
                # fx: Z-signs on A, R-signs on B ; fy: R-signs on A, Z-signs on B
                if a['sZ'] * b['sR'] != 1 or a['sR'] * b['sZ'] != 1:
                    continue
                # real factor from i^(nY_a + nY_b): i^(even) = +-1
                ny = a['nY'] + b['nY']
                phase = (-1) ** (ny // 2)
                elems.append((ia, ib, phase))
        self.elems = elems
        self.c0 = 1.0 / (4 * J * J)
        if verbose:
            print(f"[JModel J={J}] party elements {n}, invariant pair elements {len(elems)}, sectors/party "
                  f"{len(self.sectors)}  ({time.time()-t0:.1f}s)", flush=True)

    def block(self, t, rA, rB, cA, cB):
        ia, ib, ph = self.elems[t]
        Aa = self.rest[(ia, rA, cA)]; Bb = self.rest[(ib, rB, cB)]
        M = np.kron(Aa, Bb)
        if ia != ib:
            M = M + np.kron(self.rest[(ib, rA, cA)], self.rest[(ia, rB, cB)])
        return ph * M

    def u_vec(self, th, a, x):
        """restricted (charge-0, register x) vector |P_{a|x}>> in basis (q_in, q_out, l)."""
        J = self.J
        v = np.zeros(4 * J)
        for l, t in enumerate(th):
            s = +1 if x == 1 else -1
            ph = np.array([np.cos(t / 2), s * np.sin(t / 2)])
            P0 = np.outer(ph, ph)
            P = P0 if a == 0 else np.eye(2) - P0
            for qi in range(2):
                for qo in range(2):
                    v[(qi * 2 + qo) * J + l] = P[qo, qi]
        return v

    def lmi(self, th, split=True):
        """returns (C blocks, A blocks (k,n,n), b, const) for the LMI  max b.y  s.t. C - sum y_i A_i >= 0  in the form
        used by ipm.solve_lmi (C = F0, A_i = -F_i)."""
        k = len(self.elems)
        nsec = len(self.sectors)
        Cs, As = [], []
        pairs = [(cA, cB) for cA in range(nsec) for cB in range(cA, nsec)]
        for (cA, cB) in pairs:
            nA = self.rest[(0, 0, cA)].shape[0]; nB = self.rest[(0, 0, cB)].shape[0]
            n = nA * nB
            F = np.zeros((k, n, n))
            for t in range(k):
                F[t] = self.block(t, 0, 0, cA, cB)
            F0 = self.c0 * np.eye(n)
            if cA == cB and split:
                # swap-split: basis (i,j) <-> (j,i) on the (A,B) index pair
                idx = [(i, j) for i in range(nA) for j in range(nB)]
                pos = {p: q for q, p in enumerate(idx)}
                plus, minus, seen = [], [], set()
                for q, (i, j) in enumerate(idx):
                    q2 = pos[(j, i)]
                    if q in seen:
                        continue
                    seen.add(q); seen.add(q2)
                    if q == q2:
                        e = np.zeros(n); e[q] = 1; plus.append(e)
                    else:
                        e = np.zeros(n); e[q] = e[q2] = 1 / np.sqrt(2); plus.append(e)
                        f = np.zeros(n); f[q] = 1 / np.sqrt(2); f[q2] = -1 / np.sqrt(2); minus.append(f)
                for Q in (np.array(plus).T, np.array(minus).T):
                    if Q.size == 0:
                        continue
                    Fq = np.einsum('ia,kij,jb->kab', Q, F, Q)
                    Cs.append(Q.T @ F0 @ Q); As.append(-Fq)
            else:
                Cs.append(F0); As.append(-F)
        # objective
        uA = self.u_vec(th, 0, 0)
        u = np.kron(uA, uA)
        b = np.array([u @ self.block(t, 0, 0, 0, 0) @ u for t in range(k)])
        const = self.c0 * (u @ u)
        return Cs, As, b, const

    def block_sparse(self, t, rA, rB, cA, cB):
        if not hasattr(self, '_rest_sp'):
            self._rest_sp = {key: sp.csr_matrix(v) for key, v in self.rest.items()}
        ia, ib, ph = self.elems[t]
        R = self._rest_sp
        M = sp.kron(R[(ia, rA, cA)], R[(ib, rB, cB)], format='csr')
        if ia != ib:
            M = M + sp.kron(R[(ib, rA, cA)], R[(ia, rB, cB)], format='csr')
        return (ph * M).tocsr()

    def lmi_sparse(self, th):
        """(C blocks dense, Asp blocks sparse k x n^2 with rows vec(A_i) = vec(-F_i), b, const); swap-split diagonal
        sector blocks with sparse orthonormal Q."""
        k = len(self.elems)
        nsec = len(self.sectors)
        Cs, Asp = [], []
        for cA in range(nsec):
            for cB in range(cA, nsec):
                nA = self.rest[(0, 0, cA)].shape[0]; nB = self.rest[(0, 0, cB)].shape[0]
                n = nA * nB
                Fs = [self.block_sparse(t, 0, 0, cA, cB) for t in range(k)]
                if cA == cB:
                    idx = [(i, j) for i in range(nA) for j in range(nB)]
                    pos = {p: q for q, p in enumerate(idx)}
                    pr, pc, pv, mr, mc, mv = [], [], [], [], [], []
                    npl = nmi = 0; seen = set()
                    for q, (i, j) in enumerate(idx):
                        q2 = pos[(j, i)]
                        if q in seen:
                            continue
                        seen.add(q); seen.add(q2)
                        if q == q2:
                            pr.append(q); pc.append(npl); pv.append(1.0); npl += 1
                        else:
                            s2 = 1 / np.sqrt(2)
                            pr += [q, q2]; pc += [npl, npl]; pv += [s2, s2]; npl += 1
                            mr += [q, q2]; mc += [nmi, nmi]; mv += [s2, -s2]; nmi += 1
                    Qs = [sp.csr_matrix((pv, (pr, pc)), shape=(n, npl)), sp.csr_matrix((mv, (mr, mc)), shape=(n, nmi))]
                else:
                    Qs = [None]
                for Q in Qs:
                    if Q is not None and Q.shape[1] == 0:
                        continue
                    m_ = n if Q is None else Q.shape[1]
                    rows, cols, vals = [], [], []
                    for t, F in enumerate(Fs):
                        G = F if Q is None else (Q.T @ F @ Q).tocoo()
                        G = sp.coo_matrix(G)
                        G.eliminate_zeros()
                        rows.extend([t] * G.nnz); cols.extend((G.row * m_ + G.col).tolist()); vals.extend((-G.data).tolist())
                    Asp.append(sp.csr_matrix((vals, (rows, cols)), shape=(k, m_ * m_)))
                    Cs.append(self.c0 * np.eye(m_))
        uA = self.u_vec(th, 0, 0)
        u = np.kron(uA, uA)
        b = np.array([u @ (self.block_sparse(t, 0, 0, 0, 0) @ u) for t in range(k)])
        const = self.c0 * (u @ u)
        return Cs, Asp, b, const

    def value_sparse(self, th, tol=1e-9, verbose=False, maxit=100, return_sol=False):
        from ipm_sparse import solve_lmi_sparse
        if not hasattr(self, '_lmi_cache'):
            Cs, Asp, b, const = self.lmi_sparse(th)
            self._lmi_cache = (Cs, Asp)
        Cs, Asp = self._lmi_cache
        uA = self.u_vec(th, 0, 0)
        u = np.kron(uA, uA)
        b = np.array([u @ (self.block_sparse(t, 0, 0, 0, 0) @ u) for t in range(len(self.elems))])
        const = self.c0 * (u @ u)
        sol = solve_lmi_sparse(Cs, Asp, b, maxit=maxit, tol=tol, verbose=verbose)
        val = sol['dobj'] + const
        if return_sol:
            return val, sol, const
        return val

    def value(self, th, tol=1e-9, verbose=False, return_sol=False, maxit=100):
        from ipm import solve_lmi
        Cs, As, b, const = self.lmi(th)
        sol = solve_lmi(Cs, As, b, maxit=maxit, tol=tol, verbose=verbose)
        val = sol['dobj'] + const
        if return_sol:
            return val, sol, const
        return val

    def du_vec(self, th, l):
        """derivative of u_vec(th, 0, 0) w.r.t. theta_l"""
        J = self.J
        v = np.zeros(4 * J)
        t = th[l]
        ph = np.array([np.cos(t / 2), -np.sin(t / 2)])
        dph = np.array([-np.sin(t / 2) / 2, -np.cos(t / 2) / 2])
        dP = np.outer(dph, ph) + np.outer(ph, dph)
        for qi in range(2):
            for qo in range(2):
                v[(qi * 2 + qo) * J + l] = dP[qo, qi]
        return v

    def value_and_grad(self, th, tol=1e-8, maxit=60, sparse=True):
        """value and envelope-theorem gradient d/dtheta <u_00|W*|u_00> (u_00 = uA (x) uB, same angles)."""
        if sparse:
            val, sol, const = self.value_sparse(th, tol=tol, return_sol=True, maxit=maxit)
        else:
            val, sol, const = self.value(th, tol=tol, return_sol=True, maxit=maxit)
        y = sol['y']
        Wb = self.c0 * np.eye((4 * self.J) ** 2)
        for t in range(len(self.elems)):
            if y[t] != 0:
                Wb += y[t] * self.block(t, 0, 0, 0, 0)
        uA = self.u_vec(th, 0, 0)
        u = np.kron(uA, uA)
        Wu = Wb @ u
        g = np.zeros(len(th))
        for l in range(len(th)):
            d = self.du_vec(th, l)
            du = np.kron(d, uA) + np.kron(uA, d)
            g[l] = 2 * du @ Wu
        return val, g, sol

    def full_value_check(self, th, y):
        """sum_xy 1/4 <u_xy|W|u_xy> computed from all four register blocks (consistency with invariance)."""
        k = len(self.elems)
        tot = 0.0
        for x in (0, 1):
            for yy in (0, 1):
                ua = self.u_vec(th, yy, x)      # Alice outcome a = y, setting x
                ub = self.u_vec(th, x, yy)      # Bob outcome b = x, setting y
                u = np.kron(ua, ub)
                val = self.c0 * (u @ u)
                for t in range(k):
                    if y[t] != 0:
                        val += y[t] * (u @ self.block(t, x, yy, 0, 0) @ u)
                tot += 0.25 * val
        return tot
