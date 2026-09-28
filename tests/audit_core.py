"""P-AUDIT: independent implementation of general process-matrix strategies, the Lemma-1 (Lueders normal form)
construction, and the moment matrix Gamma.  Does NOT import mc2/mc3 (those are used only in audit_rows.py to read
the certified row list).

Conventions (as in PROOF.md):
  Choi of a map F: C_F = sum_ij |i><j| (x) F(|i><j|)   on  in (x) out;  |K>> := sum_i |i> (x) K|i>  (index i*dout+o).
  p(a,b|x,y) = Tr[W (M_{a|x} (x) N_{b|y})],  W on A_I (x) A_O (x) B_I (x) B_O.
  Word tuple (x1,...,xn)  ->  operator O_{x1} O_{x2} ... O_{xn},  O_x = 2 P_{0|x} - 1.
  Word vector |w,r> = |w>> (x) |r>  on  H (x) H (x) X.
"""
import numpy as np
import scipy.linalg as sla

AI, AO, BI, BO = 0, 1, 2, 3


# ----------------------------------------------------------------------------------------------------------------
# generic helpers
# ----------------------------------------------------------------------------------------------------------------
def haar_isometry(dout, din, rng, real=False):
    G = rng.normal(size=(dout, din)) + (0 if real else 1j * rng.normal(size=(dout, din)))
    Q, R = np.linalg.qr(G)
    Q = Q * (np.diag(R) / np.abs(np.diag(R)))[None, :]
    return Q


def haar_unitary(d, rng, real=False):
    return haar_isometry(d, d, rng, real)


def vecop(K):
    """|K>> = sum_i |i> (x) K|i>  (index i*dout + o)"""
    return K.T.reshape(-1)


def choi_from_kraus(Ks):
    return sum(np.outer(vecop(K), vecop(K).conj()) for K in Ks)


def ptrace_out(C, din, dout):
    """Tr_out of an operator on in (x) out"""
    return np.einsum('iojo->ij', C.reshape(din, dout, din, dout))


def trace_replace(W, dims, S):
    """_S W := Tr_S W (x) 1_S / d_S  (subsystems S, list of indices)."""
    n = len(dims)
    D = int(np.prod(dims))
    T = W.reshape(list(dims) + list(dims))
    for s in S:
        Ts = np.trace(T, axis1=s, axis2=n + s)
        E = np.eye(dims[s]) / dims[s]
        Tn = np.multiply.outer(Ts, E)
        T = np.moveaxis(Tn, [2 * n - 2, 2 * n - 1], [s, n + s])
    return T.reshape(D, D)


def LV(W, dims):
    """projector onto the bipartite valid-process subspace (Araujo et al., NJP 17, 102001 (2015))"""
    tr = lambda S: trace_replace(W, dims, S)
    return (tr([AO]) + tr([BO]) - tr([AO, BO]) - tr([BI, BO]) + tr([AO, BI, BO]) - tr([AI, AO]) + tr([AI, AO, BO]))


def validity_report(W, dims):
    """independent conditions: (a) _{BI BO}W = _{AO BI BO}W, (b) _{AI AO}W = _{AI AO BO}W,
    (c) W = _{AO}W + _{BO}W - _{AO BO}W, trace, hermiticity, min eigenvalue"""
    tr = lambda S: trace_replace(W, dims, S)
    a = np.abs(tr([BI, BO]) - tr([AO, BI, BO])).max()
    b = np.abs(tr([AI, AO]) - tr([AI, AO, BO])).max()
    c = np.abs(W - tr([AO]) - tr([BO]) + tr([AO, BO])).max()
    t = abs(np.trace(W) - dims[AO] * dims[BO])
    h = np.abs(W - W.conj().T).max()
    ev = np.linalg.eigvalsh((W + W.conj().T) / 2).min()
    return dict(a=a, b=b, c=c, trace=t, herm=h, mineig=ev)


def random_valid_W(dims, rng, boundary=0.999, real=False):
    D = int(np.prod(dims))
    X = rng.normal(size=(D, D)) + (0 if real else 1j * rng.normal(size=(D, D)))
    X = X + X.conj().T
    Y = LV(X, dims)
    Y = Y - np.trace(Y) / D * np.eye(D)
    c = dims[AO] * dims[BO] / D
    ev = np.linalg.eigvalsh(Y).min()
    return c * np.eye(D) + boundary * c / abs(ev) * Y


def ocb_W():
    I = np.eye(2); Z = np.diag([1.0, -1.0]); X = np.array([[0, 1.0], [1.0, 0]])
    k = lambda *ops: np.kron(np.kron(ops[0], ops[1]), np.kron(ops[2], ops[3]))
    return 0.25 * (k(I, I, I, I) + (k(I, Z, Z, I) + k(Z, I, X, Z)) / np.sqrt(2))


def local_unitary(W, dims, rng):
    U = haar_unitary(dims[0], rng)
    for d in dims[1:]:
        U = np.kron(U, haar_unitary(d, rng))
    return U @ W @ U.conj().T


def random_instrument_kraus(dI, dO, kappa, rng, m=2, real=False):
    """returns K[a] = list of kappa Kraus operators (dO x dI); generic non-projective instrument"""
    V = haar_isometry(m * kappa * dO, dI, rng, real)
    return [[V[(a * kappa + k) * dO:(a * kappa + k + 1) * dO, :] for k in range(kappa)] for a in range(m)]


def instrument_choi(Kx):
    return [choi_from_kraus(Ka) for Ka in Kx]


def probs_direct(W, KA, KB, dA, dB):
    """p[a,b,x,y] = Tr[W (M_{a|x} (x) N_{b|y})]; KA[x][a] = Kraus list"""
    p = np.zeros((2, 2, 2, 2))
    for x in (0, 1):
        CA = instrument_choi(KA[x])
        for y in (0, 1):
            CB = instrument_choi(KB[y])
            for a in (0, 1):
                for b in (0, 1):
                    p[a, b, x, y] = np.trace(W @ np.kron(CA[a], CB[b])).real
    return p


def gyni_value(p):
    return 0.25 * sum(p[y, x, x, y] for x in (0, 1) for y in (0, 1))


# ----------------------------------------------------------------------------------------------------------------
# Lemma 1: Lueders normal form
# ----------------------------------------------------------------------------------------------------------------
def lemma1(Kx, dI, dO, rng, m=2, nX=2, extra_dprime=0):
    """Kx[x][a] = list of Kraus ops (dO x dI).  Implements PROOF.md Lemma 1 literally with a RANDOM isometry J and a
    RANDOM unitary completion (adversarial choices).  Returns party data:
      dH, J (dH x dI), U[x], P0[x] = P_{0|x} (dH x dH), P[x][a], absorb = list of (T_{x,e} (dO x dH), register x)."""
    kappa = max(len(Kx[x][a]) for x in range(nX) for a in range(m))
    dE = m * kappa
    dprime = max(1, int(np.ceil(dI / (dO * dE)))) + extra_dprime
    dH = dO * dE * dprime
    J = haar_isometry(dH, dI, rng)
    QJ = sla.null_space(J.conj().T)
    U, P, T = [], [], []
    absorb = []
    for x in range(nX):
        V = np.zeros((dH, dI), dtype=complex)
        for a in range(m):
            for k, K in enumerate(Kx[x][a]):
                e = np.zeros(dE * dprime); e[(a * kappa + k) * dprime + 0] = 1.0
                V += np.kron(K, e[:, None])               # H = A_O (x) C^m (x) C^kappa (x) C^d'
        iso_err = np.abs(V.conj().T @ V - np.eye(dI)).max()
        QV = sla.null_space(V.conj().T)
        R = haar_unitary(dH - dI, rng) if dH > dI else np.zeros((0, 0))
        Ux = V @ J.conj().T + QV @ R @ QJ.conj().T
        uerr = max(np.abs(Ux.conj().T @ Ux - np.eye(dH)).max(), np.abs(Ux @ J - V).max())
        Pi = [np.kron(np.eye(dO), np.kron(np.diag(np.eye(m)[a]), np.eye(kappa * dprime))) for a in range(m)]
        Px = [Ux.conj().T @ Pi[a] @ Ux for a in range(m)]
        U.append(Ux); P.append(Px)
        for e in range(dE * dprime):
            ev = np.zeros(dE * dprime); ev[e] = 1.0
            Txe = np.kron(np.eye(dO), ev[None, :]) @ Ux    # (1_{A_O} (x) <e|) U_x
            absorb.append((Txe, x))
        T.append(dict(iso_err=iso_err, unitary_err=uerr))
    return dict(dH=dH, dI=dI, dO=dO, J=J, U=U, P=P, P0=[P[x][0] for x in range(nX)], absorb=absorb, diag=T,
                kappa=kappa, dprime=dprime, nX=nX)


def lemma1_identity_error(party, Kx):
    """|| Choi(T_x o L_{a|x} o J(.)J^+) - Choi(M_{a|x}) ||  and || Phi(Choi(M~_{a|x})) - Choi(M_{a|x}) ||"""
    dH, dI, dO, J = party['dH'], party['dI'], party['dO'], party['J']
    e1 = e2 = 0.0
    for x in range(party['nX']):
        for a in range(2):
            C_true = choi_from_kraus(Kx[x][a])
            # T_x o L_{a|x} o J : Kraus {(1 (x) <e|) U_x P_{a|x} J}
            Ks = [Txe @ party['P'][x][a] @ J for (Txe, xx) in party['absorb'] if xx == x]
            e1 = max(e1, np.abs(choi_from_kraus(Ks) - C_true).max())
            # Phi_A applied to the Lueders Choi |P,x><P,x| via the absorbed Kraus (J^T (x) T_{x',e} (x) <x'|)
            e2 = max(e2, np.abs(phi_choi(party, lueders_choi_vec(party, a, x)) - C_true).max())
    return e1, e2


def lueders_choi_vec(party, a, x):
    """|P_{a|x}, x> on H (x) H (x) X"""
    dH, nX = party['dH'], party['nX']
    return np.kron(vecop(party['P'][x][a]), np.eye(nX)[x])


def absorbed_kraus_matrices(party):
    """explicit Kraus matrices of Phi_A at Choi level: J^T (x) T_{x,e} (x) <x|_X : H (x) H (x) X -> A_I (x) A_O"""
    nX = party['nX']
    return [np.kron(party['J'].T, np.kron(Txe, np.eye(nX)[r][None, :])) for (Txe, r) in party['absorb']]


def phi_choi(party, v):
    """Phi_A(|v><v|) for a vector v on H (x) H (x) X"""
    out = 0
    for K in absorbed_kraus_matrices(party):
        u = K @ v
        out = out + np.outer(u, u.conj())
    return out


# ----------------------------------------------------------------------------------------------------------------
# moment matrix
# ----------------------------------------------------------------------------------------------------------------
def word_op(w, P0):
    d = P0[0].shape[0]
    O = [2 * P0[x] - np.eye(d) for x in range(len(P0))]
    M = np.eye(d, dtype=complex)
    for c in w:
        M = M @ O[c]
    return M


def word_vectors(basis, P0, nX=2, reverse=False):
    """columns |w,r> = |w>> (x) |r>  (H (x) H (x) X)"""
    cols = []
    for (w, r) in basis:
        ww = tuple(reversed(w)) if reverse else w
        cols.append(np.kron(vecop(word_op(ww, P0)), np.eye(nX)[r]))
    return np.array(cols).T


def party_F(party, basis, reverse=False, explicit=False):
    """F[j] (dI*dO x n): columns (J^T (x) T_j (x) <x_j|)|w,r>  =  delta_{r,x_j} |T_j w J>>  (Lemma-1 absorbed Kraus)."""
    if explicit:
        V = word_vectors(basis, party['P0'], party['nX'], reverse)
        return [K @ V for K in absorbed_kraus_matrices(party)]
    J = party['J']
    Ws = [word_op(tuple(reversed(w)) if reverse else w, party['P0']) for (w, r) in basis]
    F = []
    for (Txe, x) in party['absorb']:
        cols = [vecop(Txe @ Wo @ J) if r == x else np.zeros(party['dI'] * party['dO'], dtype=complex)
                for Wo, (w, r) in zip(Ws, basis)]
        F.append(np.array(cols).T)
    return F


def gamma_from_F(W, FA, FB, dimA, dimB):
    """Gamma[(k,l),(k',l')] = sum_{j,j'} <F_A[j]_k (x) F_B[j']_l | W | F_A[j]_k' (x) F_B[j']_l'>  (= <k,l|W~|k',l'>)
    dimA = dAI*dAO, dimB = dBI*dBO.  Returned as (nA*nB) x (nA*nB), index k*nB + l."""
    nA = FA[0].shape[1]; nB = FB[0].shape[1]
    GA = sum(np.einsum('ak,cm->akcm', F.conj(), F) for F in FA)   # dimA x nA x dimA x nA
    GB = sum(np.einsum('bl,dn->bldn', F.conj(), F) for F in FB)
    W4 = W.reshape(dimA, dimB, dimA, dimB)
    T1 = np.einsum('abcd,akcm->bdkm', W4, GA)
    G = np.einsum('bdkm,bldn->klmn', T1, GB)
    return G.reshape(nA * nB, nA * nB)


def gamma_from_Wtilde(Wt, VA, VB):
    V = np.kron(VA, VB)
    return V.conj().T @ Wt @ V


def Wtilde_explicit(W, partyA, partyB):
    """(Phi_A^+ (x) Phi_B^+)(W) formed explicitly (small dims only)"""
    KA = absorbed_kraus_matrices(partyA); KB = absorbed_kraus_matrices(partyB)
    nA = KA[0].shape[1]; nB = KB[0].shape[1]
    Wt = np.zeros((nA * nB, nA * nB), dtype=complex)
    for Ka in KA:
        for Kb in KB:
            K = np.kron(Ka, Kb)
            Wt += K.conj().T @ W @ K
    return Wt


# ----------------------------------------------------------------------------------------------------------------
# GYNI group acting on Lueders-form strategies (explicitly, at the strategy level)
# ----------------------------------------------------------------------------------------------------------------
def party_letter_swap(party):
    """x -> 1-x:  P'_{a|x} = P_{a|1-x};  register relabelled so that the new instrument writes |x>:
    W~' = F_X W~ F_X  <=>  absorbed Kraus (T, r) -> (T, 1-r)."""
    q = dict(party)
    q['P'] = [party['P'][1], party['P'][0]]
    q['P0'] = [q['P'][0][0], q['P'][1][0]]
    q['absorb'] = [(T, 1 - r) for (T, r) in party['absorb']]
    return q


def party_outcome_flip(party):
    """a -> 1-a:  P'_{a|x} = P_{1-a|x}  (O_x -> -O_x)"""
    q = dict(party)
    q['P'] = [[party['P'][x][1], party['P'][x][0]] for x in range(party['nX'])]
    q['P0'] = [q['P'][x][0] for x in range(party['nX'])]
    return q


def swap_W(W, dims):
    """exchange the parties: W' on (B_I B_O A_I A_O)"""
    dA = dims[0] * dims[1]; dB = dims[2] * dims[3]
    return W.reshape(dA, dB, dA, dB).transpose(1, 0, 3, 2).reshape(dA * dB, dA * dB)


def strategy_orbit(W, dims, pA, pB):
    """the 8 transformed Lueders strategies (W, dims, partyA, partyB) of the GYNI group
    generated by fx (Alice x->1-x, Bob b->1-b), fy (Bob y->1-y, Alice a->1-a), swap."""
    def fx(S):
        W_, d_, a_, b_ = S
        return (W_, d_, party_letter_swap(a_), party_outcome_flip(b_))

    def fy(S):
        W_, d_, a_, b_ = S
        return (W_, d_, party_outcome_flip(a_), party_letter_swap(b_))

    def sw(S):
        W_, d_, a_, b_ = S
        return (swap_W(W_, d_), [d_[2], d_[3], d_[0], d_[1]], b_, a_)
    S0 = (W, list(dims), pA, pB)
    orbit = []
    for s in (False, True):
        for f1 in (False, True):
            for f2 in (False, True):
                S = S0
                if f1:
                    S = fx(S)
                if f2:
                    S = fy(S)
                if s:
                    S = sw(S)
                orbit.append(S)
    return orbit
