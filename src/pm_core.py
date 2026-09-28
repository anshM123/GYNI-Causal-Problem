"""Core utilities for bipartite process-matrix SDPs (qubit-register systems).

Systems are ordered  [A_I, A_O, B_I, B_O], each group consisting of an integer number of qubits.
A process matrix is parametrised in the Pauli (Hilbert-Schmidt) basis restricted to the allowed
term types of a valid bipartite process:
    1, AI, BI, AI.BI, AO.BI, AI.AO.BI, AI.BO, AI.BI.BO
Rule used: (AO in S => BI in S and BO not in S) and (BO in S => AI in S and AO not in S).
Normalisation: Tr W = d_AO * d_BO.
"""
import itertools
import numpy as np
import scipy.sparse as sp

PAULI = [np.eye(2, dtype=complex),
         np.array([[0, 1], [1, 0]], dtype=complex),
         np.array([[0, -1j], [1j, 0]], dtype=complex),
         np.array([[1, 0], [0, -1]], dtype=complex)]


def kron(*ops):
    out = np.array([[1.0 + 0j]])
    for o in ops:
        out = np.kron(out, o)
    return out


def pauli_string(s):
    return kron(*[PAULI[i] for i in s])


def allowed(pattern):
    AI, AO, BI, BO = pattern
    if AO and not (BI and not BO):
        return False
    if BO and not (AI and not AO):
        return False
    return True


def valid_pauli_strings(nq):
    """nq = (nAI, nAO, nBI, nBO) numbers of qubits. Returns list of allowed Pauli strings (tuples)."""
    groups = []
    for g, n in enumerate(nq):
        groups += [g] * n
    N = sum(nq)
    out = []
    for s in itertools.product(range(4), repeat=N):
        pat = [False] * 4
        for q, si in enumerate(s):
            if si != 0:
                pat[groups[q]] = True
        if allowed(pat):
            out.append(s)
    return out


def ptrace(rho, dims, keep):
    """Partial trace keeping subsystems in `keep` (list of indices)."""
    n = len(dims)
    rho = rho.reshape(dims + dims)
    trace_out = [i for i in range(n) if i not in keep]
    # iterate tracing out highest index first
    cur_dims = list(dims)
    for i in sorted(trace_out, reverse=True):
        m = len(cur_dims)
        rho = np.trace(rho, axis1=i, axis2=i + m)
        cur_dims.pop(i)
    d = int(np.prod(cur_dims)) if cur_dims else 1
    return rho.reshape(d, d)


def trace_replace(W, dims, sys):
    """_{sys} W := (1/d_sys) 1_sys (x) Tr_sys W, for a list of subsystem indices sys (in dims ordering)."""
    n = len(dims)
    keep = [i for i in range(n) if i not in sys]
    red = ptrace(W, dims, keep)
    dsys = int(np.prod([dims[i] for i in sys]))
    # build 1_sys (x) red in the right order
    big = np.kron(red, np.eye(dsys) / dsys)
    # current order: keep + sys ; permute back
    order = keep + list(sys)
    perm_dims = [dims[i] for i in order]
    big = big.reshape(perm_dims + perm_dims)
    inv = np.argsort(order)
    big = big.transpose(list(inv) + [i + n for i in inv])
    D = int(np.prod(dims))
    return big.reshape(D, D)


def is_valid_process(W, dims, tol=1e-7):
    """dims = [dAI, dAO, dBI, dBO]. Checks the Araujo et al. projector conditions + PSD + trace."""
    AI, AO, BI, BO = 0, 1, 2, 3
    tr = lambda S: trace_replace(W, dims, S)
    c1 = np.linalg.norm(tr([BI, BO]) - tr([AO, BI, BO]))
    c2 = np.linalg.norm(tr([AI, AO]) - tr([AI, AO, BO]))
    c3 = np.linalg.norm(W - (tr([AO]) + tr([BO]) - tr([AO, BO])))
    ev = np.linalg.eigvalsh((W + W.conj().T) / 2).min()
    t = np.trace(W).real - dims[1] * dims[3]
    return dict(c1=c1, c2=c2, c3=c3, mineig=ev, trace_err=t,
                ok=(c1 < tol and c2 < tol and c3 < tol and ev > -tol and abs(t) < tol))


def herm_to_real(H):
    """Real symmetric embedding of Hermitian H: [[Re, -Im],[Im, Re]]."""
    return np.block([[H.real, -H.imag], [H.imag, H.real]])


class ProcessParam:
    """Affine Pauli parametrisation W = sum_s c_s sigma_s of valid bipartite processes."""

    def __init__(self, nq):
        self.nq = nq
        self.N = sum(nq)
        self.D = 2 ** self.N
        self.dims = [2 ** k for k in nq]
        self.strings = valid_pauli_strings(nq)
        assert self.strings[0] == tuple([0] * self.N)
        self.free = self.strings[1:]
        self.c0 = self.dims[1] * self.dims[3] / self.D  # coefficient of identity
        # basis matrices (sparse, complex) for free strings
        self.mats = [sp.csr_matrix(pauli_string(s)) for s in self.free]
        # real embeddings (sparse) for PSD constraints
        self.real_mats = [sp.csr_matrix(herm_to_real(M.toarray())) for M in self.mats]
        self.real_F0 = sp.csr_matrix(herm_to_real(self.c0 * np.eye(self.D)))
        # transposed data for fast functionals: Tr[M X] = sum(M.T * X)
        self._MT = [M.T.tocsr() for M in self.mats]

    def W_from_c(self, c):
        W = self.c0 * np.eye(self.D, dtype=complex)
        for ci, M in zip(c, self.mats):
            W = W + ci * M.toarray()
        return W

    def lin_functional(self, X):
        """Returns (const, vec) with Tr[W X] = const + vec @ c."""
        X = np.asarray(X)
        const = self.c0 * np.trace(X)
        vec = np.array([M.multiply(X).sum() for M in self._MT])  # Tr[M X]
        return const.real, vec.real

    def c_from_W(self, W):
        return np.array([np.trace(M.toarray() @ W).real / self.D for M in self.mats])

    def add_to_sdp(self, sdp):
        """Adds a process variable block + its PSD constraint to an SDP; returns variable indices."""
        idx = sdp.add_vars(len(self.free))
        sdp.add_psd(2 * self.D, list(zip(idx, self.real_mats)), self.real_F0)
        return idx


class BlockProcessParam:
    """Pauli parametrisation of valid processes restricted to
       - real W (even number of Y's), and
       - W diagonal (only I/Z) on the 'classical' qubits `cq` (e.g. setting registers),
    so that W = sum_k |k><k|_cq (x) W_k with real symmetric blocks W_k.  PSD <=> all blocks PSD.
    WLOG whenever all instruments are real and diagonal on cq (twirl + complex conjugation)."""

    def __init__(self, nq, cq):
        self.nq = nq
        self.N = sum(nq)
        self.D = 2 ** self.N
        self.dims = [2 ** k for k in nq]
        self.cq = list(cq)
        allstr = valid_pauli_strings(nq)
        keep = []
        for s in allstr:
            if any(s[q] in (1, 2) for q in self.cq):
                continue
            if sum(1 for t in s if t == 2) % 2 == 1:
                continue
            keep.append(s)
        assert keep[0] == tuple([0] * self.N)
        self.free = keep[1:]
        self.c0 = self.dims[1] * self.dims[3] / self.D
        self.rest = [q for q in range(self.N) if q not in self.cq]
        self.nb = 2 ** len(self.cq)
        self.bd = 2 ** len(self.rest)
        # block matrices for each free string
        self.blocks = []  # list over strings of list over k of sparse real bd x bd
        for s in self.free:
            rest_op = pauli_string([s[q] for q in self.rest]).real if sum(1 for t in s if t == 2) % 2 == 0 else None
            # Y^2 count even -> product real overall; but individual rest part may be imaginary when the
            # cq part contains Y - excluded. rest part: even #Y -> real
            M = pauli_string([s[q] for q in self.rest])
            assert np.allclose(M.imag, 0)
            M = M.real
            blist = []
            for k in range(self.nb):
                bits = [(k >> (len(self.cq) - 1 - i)) & 1 for i in range(len(self.cq))]
                sign = 1.0
                for q, bt in zip(self.cq, bits):
                    if s[q] == 3 and bt == 1:
                        sign = -sign
                blist.append(sp.csr_matrix(sign * M))
            self.blocks.append(blist)
        self.F0 = sp.csr_matrix(self.c0 * np.eye(self.bd))
        self.mats = None

    def full_matrix(self, s):
        return pauli_string(s)

    def W_from_c(self, c):
        W = self.c0 * np.eye(self.D, dtype=complex)
        for ci, s in zip(c, self.free):
            W = W + ci * pauli_string(s)
        return W

    def lin_functional(self, X):
        """Tr[W X] = const + vec@c for full-space operator X (D x D)."""
        X = np.asarray(X)
        const = (self.c0 * np.trace(X)).real
        # Tr[sigma_s X] computed via reshaping: use explicit strings (small sizes only)
        if not hasattr(self, '_stackT'):
            self._stackT = np.array([pauli_string(s).T for s in self.free])
        vec = np.real(np.einsum('kij,ij->k', self._stackT, X))
        return const, vec

    def add_to_sdp(self, sdp):
        idx = sdp.add_vars(len(self.free))
        for k in range(self.nb):
            terms = [(i, self.blocks[j][k]) for j, i in enumerate(idx)]
            sdp.add_psd(self.bd, terms, self.F0)
        return idx
