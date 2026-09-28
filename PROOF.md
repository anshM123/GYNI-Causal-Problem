# Proofs: the GYNI upper bound (soundness of the certified relaxation) and the lower-bound strategy

*Scope: strategies with finite-dimensional local Hilbert spaces of arbitrary dimension. Local ancillas and shared entanglement are included; infinite-dimensional processes are not covered.*

Sections 0–2 below replace an earlier sketch. They state the relaxation **exactly as certified** by `src/cert3_L8.pkl` and `src/verify3.py`: the rows of `mc3.build(L, sym=True)`, i.e. V1 + V2 + GYNI symmetry, with no canonical-process constraints. They prove directly in the dihedral word basis that this relaxation contains every quantum strategy. The text was produced and checked in an internal adversarial audit (see `AUDIT_REPORT.md`); independent external review is still welcome.

## 0. Conventions

**Choi operators.** All Hilbert spaces are finite-dimensional, with fixed orthonormal bases; `T` (transpose) and
the bar (complex conjugate) refer to these bases. For a linear map F : L(H_in) -> L(H_out),

    C_F := sum_{ij} |i><j| (x) F(|i><j|)  in L(H_in (x) H_out),      |Phi> := sum_i |i>|i>  (unnormalised).

We use four elementary facts (all one-line computations):

- (F1) F is completely positive iff C_F >= 0.
- (F2) F(rho) = Tr_in[(rho^T (x) 1) C_F]; hence Tr F(rho) = Tr[rho^T Tr_out C_F]. We say F has *scalar trace* lambda
  (lambda in C) if Tr F(rho) = lambda Tr rho for all rho; equivalently Tr_out C_F = lambda 1_in.
  Trace-preserving (TP): lambda = 1. Trace-annihilating (TA): lambda = 0.
- (F3) If A : H' -> H_in is linear, A(rho) := A rho A^dagger, and T(omega) = sum_k T_k omega T_k^dagger, then
  C_{T o F o A} = sum_k (A^T (x) T_k) C_F (A^T (x) T_k)^dagger.
- (F4) For operators w, w' on H and register states |r>, |r'> of X, put |w,r> := (1 (x) w)|Phi> (x) |r> in H (x) H (x) X.
  Then |w',r'><w,r| is the Choi operator of rho -> w' rho w^dagger (x) |r'><r|, and
  Tr_{H (x) X} |w',r'><w,r| = delta_{rr'} (w^dagger w')^T.

**Processes and strategies.** A (bipartite) *process* is an operator W on A_I (x) A_O (x) B_I (x) B_O with W >= 0 and
Tr[W (C_A (x) C_B)] = 1 for all Choi operators C_A, C_B of CPTP maps A_I -> A_O, B_I -> B_O.
[This is the definition of Oreshkov-Costa-Brukner, Nat. Commun. 3, 1092 (2012); it is equivalent to their
definition that allows local ancillas in an arbitrary joint state, because W (x) rho_{A'B'} is again a process in
the above sense (the added factors live on input spaces), and it is equivalent to the linear characterisation of
Araujo et al., NJP 17, 102001 (2015): W >= 0, Tr W = d_AO d_BO and W in the valid subspace.]
A *strategy* S = (W; M_{a|x}; N_{b|y}), x,y,a,b in {0,1}, consists of a process and instruments: CP maps
M_{a|x} : L(A_I) -> L(A_O) with sum_a M_{a|x} TP (same for Bob). Its correlations are
p(a,b|x,y) = Tr[W (C_{M_{a|x}} (x) C_{N_{b|y}})], and

    I_GYNI(S) := 1/4 sum_{x,y} p(a = y, b = x | x, y),        I_GYNI^max := sup_S I_GYNI(S)

(supremum over all finite dimensions; shared entanglement / local ancillas are included by the remark above).

## 1. The relaxation P_L that is certified

**Words.** G := Z_2 * Z_2 = <g_0, g_1 | g_0^2 = g_1^2 = e>. W_L := the reduced words w = (x_1,...,x_n), 0 <= n <= L,
x_i in {0,1}, x_i != x_{i+1} (|W_L| = 2L+1). For w, w' in W_L, w^{-1} w' denotes the reduced word of the product in G
(`mc3.wmul(mc3.inv(w), w')`). Letter exchange sigma: 0 <-> 1 (an automorphism of G). |w| = length.

**Index sets.** Each party has the index set K := W_L x {0,1} (word, register). A pair (k, k') = ((w,r),(w',r')) with
r = r' is called *admissible*; its *class* is t(k,k') := w^{-1} w' in G.

**Variables.** Four real symmetric matrices Gamma_{rs} (r, s in {0,1}), each indexed by W_L x W_L (Alice word,
Bob word). We write Gamma[(k,l),(k',l')] := Gamma_{rs}[(w,v),(w',v')] if k = (w,r), k' = (w',r), l = (v,s),
l' = (v',s); entries with r_k != r_k' or s_l != s_l' are not variables (they are 0). For coefficient vectors c on
Alice pairs and d on Bob pairs put <c (x) d, Gamma> := sum c_{kk'} d_{ll'} Gamma[(k,l),(k',l')].

**Constraints** (exactly the rows of `mc3.build(L, sym=True)`):

- (V1) Gamma_{rs} >= 0 for all four (r,s).
- (V2) Let pi_0 := (((),0),((),0)) (same for Bob, rho_0). Let D_A be the set of vectors e_{p} - e_{p'} with p, p'
  admissible Alice pairs of the same class (similarly D_B). Then
  (V2a) <c (x) d, Gamma> = 0 for c in D_A and d in D_B u {e_{rho_0}};
  (V2b) <e_{pi_0} (x) d, Gamma> = 0 for d in D_B;
  (V2c) Gamma[(((),0),((),0)),(((),0),((),0))] = 1.
  (`v2_rows` generates these rows for the spanning subset of D_A, D_B consisting of the differences e_{p_1} - e_p with
  p_1 the first pair of each class, and removes proportional duplicates; this has the same linear span, hence the
  same feasible set.)
- (S) Gamma = f * Gamma for f in {fx, fy, sw}, where, with k = (w,r), l = (v,s) etc.,
  (fx * Gamma)[(k,l),(k',l')] := (-1)^{|v|+|v'|} Gamma[((sigma w, 1-r),(v,s)), ((sigma w', 1-r'),(v',s'))],
  (fy * Gamma)[(k,l),(k',l')] := (-1)^{|w|+|w'|} Gamma[((w,r),(sigma v, 1-s)), ((w',r'),(sigma v', 1-s'))],
  (sw * Gamma)[(k,l),(k',l')] := Gamma[(l,k),(l',k')]
  (`map_rows(fx)`, `map_rows(fy)`, `swap_rows`; an entry mapped to itself with sign -1 is set to 0).
- **Objective.** u_{a|x} := (1/2) e_{((),x)} + (1/2)(-1)^a e_{((x),x)} in R^K, and
  o(Gamma) := 1/4 sum_{x,y} <(u_{y|x} (x) u_{x|y}), Gamma (u_{y|x} (x) u_{x|y})>   (`objective(M, gyni_coef())`).

beta_L := sup{ o(Gamma) : Gamma satisfies (V1), (V2), (S) }.

**Theorem 1 (soundness).** For every L >= 1 and every strategy S (any finite dimension) there is a Gamma satisfying
(V1), (V2), (S) with o(Gamma) = I_GYNI(S). Hence I_GYNI^max <= beta_L.

**Corollary.** `verify3.py cert3_L8.pkl` exhibits rational multipliers lambda for all rows with
Y_k := (stationarity expression) positive definite for the four blocks; for every feasible Gamma,
o(Gamma) = lambda.b - sum_k <Y_k, Gamma_k> <= lambda.b = 700548845513581/2^50. With Theorem 1:
I_GYNI^max <= 0.622212366531.

The proof occupies Lemmas 1-5.

## 2. Proofs

### Lemma 1 (Lueders normal form with setting registers)
Let S = (W; M_{a|x}; N_{b|y}) be a strategy. There exist finite-dimensional H_A, H_B, orthogonal projectors
P_{a|x} on H_A and Q_{b|y} on H_B (sum_a P_{a|x} = 1, sum_b Q_{b|y} = 1), and a process W~ on
H_A (x) (H_A (x) X) (x) H_B (x) (H_B (x) Y), X = Y = C^2, such that with the instruments

    M~_{a|x}(rho) := P_{a|x} rho P_{a|x} (x) |x><x|_X,        N~_{b|y}(sigma) := Q_{b|y} sigma Q_{b|y} (x) |y><y|_Y

one has p(a,b|x,y) = Tr[W~ (C_{M~_{a|x}} (x) C_{N~_{b|y}})] for all a,b,x,y. Moreover W~ is block diagonal in the
registers: W~ = sum_{r,s} Pi_{rs} W~ Pi_{rs}, Pi_{rs} := 1 (x) (1 (x) |r><r|_X) (x) 1 (x) (1 (x) |s><s|_Y).

*Proof.* (Alice; Bob is identical.) Choose kappa and Kraus operators K_{akx} : A_I -> A_O, k = 1..kappa (pad with
zeros), with M_{a|x}(rho) = sum_k K_{akx} rho K_{akx}^dagger. Let E := C^2 (x) C^kappa with basis |a,k> and
H_A := A_O (x) E. Put V_x := sum_{a,k} K_{akx} (x) |a,k> : A_I -> H_A. Since sum_a M_{a|x} is TP,
V_x^dagger V_x = sum_{a,k} K_{akx}^dagger K_{akx} = 1, so V_x is an isometry; in particular dim A_I <= dim H_A.
Fix any isometry J : A_I -> H_A. The partial isometry V_x J^dagger maps ran J onto ran V_x; since
dim (ran J)^perp = dim (ran V_x)^perp, it extends to a unitary U_x on H_A with U_x J = V_x. Define

    P_{a|x} := U_x^dagger (1_{A_O} (x) |a><a| (x) 1_kappa) U_x,        T_{x,e} := (1_{A_O} (x) <e|) U_x : H_A -> A_O  (e in [2] x [kappa]).

The P_{a|x} are orthogonal projectors summing to 1, and sum_e T_{x,e}^dagger T_{x,e} = 1. For e = (a',k'):
T_{x,e} P_{a|x} J = (1 (x) <e|)(1 (x) |a><a| (x) 1) V_x = delta_{a a'} K_{a k' x}. Hence

    (1)  sum_e T_{x,e} P_{a|x} J rho J^dagger P_{a|x} T_{x,e}^dagger = M_{a|x}(rho).

Let T : L(H_A (x) X) -> L(A_O), T(omega) := sum_{x,e} (T_{x,e} (x) <x|) omega (T_{x,e} (x) <x|)^dagger. It is CPTP
because sum_{x,e} (T_{x,e} (x) <x|)^dagger (T_{x,e} (x) <x|) = sum_x 1 (x) |x><x| = 1. Let J(rho) := J rho J^dagger and,
on Choi operators C in L(H_A (x) H_A (x) X),

    Phi_A(C) := sum_{x,e} Khat_{x,e} C Khat_{x,e}^dagger,      Khat_{x,e} := J^T (x) T_{x,e} (x) <x|_X .

By (F3), Phi_A(C_F) = C_{T o F o J} for every linear F : L(H_A) -> L(H_A (x) X). Consequently:
(i) Phi_A maps Choi operators of CPTP maps to Choi operators of CPTP maps (composition of CPTP maps);
(ii) Phi_A(C_{M~_{a|x}}) = C_{M_{a|x}}, because T o M~_{a|x} o J(rho) equals the left side of (1) (the register is
|x><x|, so only the x-terms of T contribute).
Define W~ := (Phi_A^dagger (x) Phi_B^dagger)(W) = sum (Khat_{x,e} (x) Khat'_{y,f})^dagger W (Khat_{x,e} (x) Khat'_{y,f}),
the adjoint taken w.r.t. the Hilbert-Schmidt inner product. Then W~ >= 0 (Kraus form). For CPTP F_A, F_B,
Tr[W~ (C_{F_A} (x) C_{F_B})] = Tr[W (Phi_A(C_{F_A}) (x) Phi_B(C_{F_B}))] = 1 by (i) and validity of W; so W~ is a
process. By (ii), Tr[W~ (C_{M~_{a|x}} (x) C_{N~_{b|y}})] = Tr[W (C_{M_{a|x}} (x) C_{N_{b|y}})] = p(a,b|x,y). Finally each
term Khat^dagger (.) Khat has the form Z (x) |x><x|_X (and |y><y|_Y on Bob's side), which gives the block diagonality. QED

*Remarks.* The padding space C^{d'} of the earlier version is unnecessary (V_x is already an isometry into
A_O (x) E). The register twirl of the earlier version is unnecessary (block diagonality is automatic). The
transpose in J^T is essential for complex J (with J^dagger the statistics are not reproduced; audit negative
control N4).

### Lemma 2 (scalar-trace factorisation)
Let W be a process, C_A in L(A_I (x) A_O) with Tr_{A_O} C_A = lambda_A 1 and C_B in L(B_I (x) B_O) with
Tr_{B_O} C_B = lambda_B 1 (lambda_A, lambda_B in C; C_A, C_B need not be Hermitian). Then
Tr[W (C_A (x) C_B)] = lambda_A lambda_B.

*Proof.* Step 1 (spanning). Every C with Tr_out C = lambda 1 is a complex combination sum_i alpha_i C_i of Choi
operators of CPTP maps with sum_i alpha_i = lambda. Indeed C = H_1 + i H_2 with Hermitian H_1 = (C + C^dagger)/2,
H_2 = (C - C^dagger)/(2i), and Tr_out(C^dagger) = (Tr_out C)^dagger gives Tr_out H_j = mu_j 1 with mu_1 = Re lambda,
mu_2 = Im lambda. For Hermitian H with Tr_out H = mu 1 let D := 1 (x) 1/d_out (completely depolarising channel) and
K := H - mu D, so Tr_out K = 0. For t > d_out ||K|| the operator D + K/t is positive with Tr_out = 1, i.e. a CPTP
Choi operator, and H = mu D + t (D + K/t) - t D.
Step 2 (one-party reduction). Let C_B be CPTP and X := Tr_B[W (1 (x) C_B)]. Then Tr[X C_A'] = 1 for every CPTP
C_A', hence, by Step 1 with lambda = 0, Tr[X Z] = 0 for all Z with Tr_{A_O} Z = 0. The annihilator of the kernel of
the linear map Tr_{A_O} under the non-degenerate pairing (X, Z) -> Tr[X Z] is the range of its adjoint,
{tau (x) 1_{A_O}}. So X = tau (x) 1 with Tr tau = Tr[X D] = 1.
Step 3. By Step 1 for Bob and linearity, Tr_B[W (1 (x) C_B)] = sum_i alpha_i tau_i (x) 1 = tau (x) 1 with Tr tau = lambda_B.
Then Tr[W (C_A (x) C_B)] = Tr[(tau (x) 1) C_A] = Tr[tau Tr_{A_O} C_A] = lambda_A Tr tau = lambda_A lambda_B. QED

### Lemma 3 (moment matrix of a Lueders-form strategy; V1, V2, objective)
Let (W~, P, Q) be as in Lemma 1, O_x := P_{0|x} - P_{1|x}, R_y := Q_{0|y} - Q_{1|y} (unitary involutions). By the
universal property of the free product there are unique group homomorphisms pi_A : G -> U(H_A), g_x -> O_x, and
pi_B : G -> U(H_B), g_y -> R_y; extend them linearly to the group algebra R[G]. For k = (w,r) in K put
|k> := (1 (x) pi_A(w))|Phi> (x) |r> (Bob: |l> with pi_B), and

    Gamma^0[(k,l),(k',l')] := <k,l| W~ |k',l'>        (k,k' in K_A; l,l' in K_B).

Then: (a) Gamma^0 is Hermitian positive semidefinite; (b) Gamma^0[(k,l),(k',l')] = 0 unless r_k = r_k' and
s_l = s_l'; (c) Gamma^0 satisfies (V2a)-(V2c); (d) o(Gamma^0) = I_GYNI(S).

*Proof.* (a) Gamma^0 = V^dagger W~ V with V the matrix of columns |k> (x) |l>. (b) Lemma 1 (block diagonality).
(c) For a coefficient vector c on admissible Alice pairs let C_A(c) := sum c_{kk'} |k'><k|, the Choi operator of
rho -> sum c_{kk'} pi_A(w') rho pi_A(w)^dagger (x) |r><r| (F4). By (F4) and pi_A(w)^dagger = pi_A(w^{-1}),
Tr_out C_A(c) = [pi_A(sum_{kk'} c_{kk'} t(k,k'))]^T. For c = e_p - e_{p'} (same class) the argument is 0 in R[G], so
Tr_out C_A(c) = 0 (TA); for c = e_{pi_0}, t = e and Tr_out C_A(c) = 1 (TP). The same holds for Bob. Since
<c (x) d, Gamma^0> = Tr[W~ (C_A(c) (x) C_B(d))], Lemma 2 gives 0 for (V2a), (V2b) and 1 for (V2c). The identities
used are identities in G (g_x^2 = e), hence valid in every realisation; no relation specific to particular
projectors (P = 0, 1, P_{0|0} = P_{0|1}, commuting, ...) is ever used.
(d) C_{M~_{a|x}} = |P_{a|x}, x><P_{a|x}, x| with |P_{a|x}, x> := (1 (x) P_{a|x})|Phi> (x) |x> = sum_k u_{a|x}(k) |k>, because
P_{a|x} = (1/2) pi_A(e) + (1/2)(-1)^a pi_A(g_x). Hence p(a,b|x,y) = <u_{a|x} (x) u_{b|y}, Gamma^0 (u_{a|x} (x) u_{b|y})>. QED

### Lemma 4 (realness and block form)
Gamma^1 := Re Gamma^0, restricted to the register-diagonal blocks, is a feasible point of (V1), (V2) with
o(Gamma^1) = I_GYNI(S).

*Proof.* conj(Gamma^0) = (Gamma^0)^T is PSD, so Re Gamma^0 = (Gamma^0 + conj Gamma^0)/2 is real, symmetric and PSD, and so
are its principal (register) blocks; by Lemma 3(b) nothing is lost by the restriction. (V2) and the objective are
real-linear with real coefficients and real right-hand sides and are satisfied by Gamma^0; take real parts. The
symmetric storage of `BlockMoment` (one variable for Gamma[(k,l),(k',l')] and Gamma[(k',l'),(k,l)]) is exact for the
real symmetric Gamma^1. QED

### Lemma 5 (GYNI symmetry)
For a Lueders-form strategy S = (W~, P, Q) define
- fx.S := (F_X W~ F_X, P', Q') with P'_{a|x} := P_{a|1-x}, Q'_{b|y} := Q_{1-b|y}, F_X the register flip |r> -> |1-r> on X;
- fy.S := (F_Y W~ F_Y, P'', Q'') with P''_{a|x} := P_{1-a|x}, Q''_{b|y} := Q_{b|1-y};
- sw.S := (Sw W~ Sw^dagger, Q, P), Sw exchanging Alice's and Bob's systems.
Then: (i) each f.S is a Lueders-form strategy (W~' is a process, block diagonal in the registers);
(ii) I_GYNI(f.S) = I_GYNI(S); (iii) Gamma^0(f.S) = f * Gamma^0(S) with the maps of (S); (iv) fx^2 = fy^2 = sw^2 = id,
fx fy = fy fx, sw fx sw = fy, so fx, fy, sw generate a finite group GG (a quotient of the dihedral group of order 8)
acting on Lueders-form strategies.

*Proof* (fx; fy is symmetric, sw is immediate). (i) F_X W~ F_X = (Psi^dagger (x) id)(W~) with Psi(C) = (1 (x) F_X) C (1 (x) F_X),
the Choi-level form of post-composition with the unitary channel F_X (.) F_X, which maps CPTP maps to CPTP maps and
is CP; so the argument of Lemma 1 applies. The flip permutes the register blocks. (ii) (1 (x) F_X)|P_{a|1-x}, x> =
|P_{a|1-x}, 1-x>, so p'(a,b|x,y) = p(a, 1-b | 1-x, y) and I' = 1/4 sum_{x,y} p(y, 1-x | 1-x, y) = I (substitute x -> 1-x).
For sw, p'(a,b|x,y) = p(b,a|y,x) and I' = 1/4 sum p(x,y|y,x) = I. (iii) O'_x = O_{1-x}, so pi'_A = pi_A o sigma;
R'_y = -R_y, so pi'_B(v) = (-1)^{|v|} pi_B(v). Hence the new word vectors are |(w,r)>' = F_X |(sigma w, 1-r)> (F_X on
the register) and |(v,s)>' = (-1)^{|v|} |(v,s)>, and
Gamma^0(fx.S)[(k,l),(k',l')] = (-1)^{|v|+|v'|} <(sigma w,1-r),(v,s)| W~ |(sigma w',1-r'),(v',s')> = (fx * Gamma^0(S))[(k,l),(k',l')].
(iv) direct computation on (W~, P, Q). QED

### Proof of Theorem 1
Let S be any strategy; replace it by its Lueders normal form (Lemma 1), still called S, with the same I_GYNI.
Define

    Gamma-bar := (1/|GG|) sum_{g in GG} Re Gamma^0(g.S)   (register-diagonal blocks).

Each summand is feasible for (V1), (V2) and has objective I_GYNI(S) (Lemmas 3, 4, 5(i),(ii)); these constraints are
convex and the objective is linear, so Gamma-bar satisfies (V1), (V2) and o(Gamma-bar) = I_GYNI(S). The maps f * are
signed permutations preserving the register-block structure, so they commute with Re and with the block
restriction; by Lemma 5(iii), f * Gamma-bar = (1/|GG|) sum_g Re Gamma^0(f g . S) = Gamma-bar for f in {fx, fy, sw}
(left multiplication by f permutes GG). Hence Gamma-bar satisfies (S). QED

### Remarks
1. **V3 is not part of the certified program.** The Liu-Chiribella canonical single-trigger processes are linear
   images of Gamma, and their validity can be added as further constraints (earlier versions did so; numerically
   they do not change the value). The certificate `cert3_L8.pkl` is a dual certificate for the program
   (V1)+(V2)+(S) only; adding constraints could only lower the value, so no statement about V3 is needed for the
   bound. The comparison with Liu-Chiribella belongs to a remark: level 1 of the certified program already gives
   0.74626 < 0.7592.
2. **Idempotent basis.** The same proof applies verbatim to words in the idempotents P_{0|x} (free algebra of two
   idempotents, `mc2.py`); it is not needed for the certified result, which is proved directly in the dihedral basis.
3. **Scope.** The bound holds for the supremum over all finite-dimensional strategies, including local ancillas and
   shared entanglement (absorbed into W). Infinite-dimensional process matrices are not covered by Lemma 1 as stated.
4. **Numerical cross-check.** P-AUDIT (iqoqi/programs/gyni_audit) tested Theorem 1 with code independent of mc2/mc3:
   more than 100 strategies, the full level-8 row list, and the group average from explicitly transformed
   strategies. No row is violated beyond 2.1e-14 and no eigenvalue is below -8.5e-15 relative to ||Gamma||. The
   published J=3 and J=4 strategies are contained at every level 2..8 with the exact objective value.

## 3. Exact certificates (upper bound)
Dual: minimise λ·b subject to Y_k := (stationarity expression in λ) ⪰ 0, where λ are the multipliers of all equality rows.

Procedure (`certify3.py`):
1. Solve with a margin ε·Tr Γ (ε = 1e-7).
2. Take the solver's dual, add ε·I, and spread it over all register blocks.
3. Solve for the multipliers of all rows by least squares.
4. Round them to the common denominator D = 2^50.
5. Define each Y_k exactly from the rational λ.
6. Check that each Y_k is positive definite with Sylvester's criterion: all leading principal minors are positive, computed by fraction-free Bareiss elimination on integers.
7. The bound is β = λ·b, computed exactly.

`verify3.py` repeats steps 5–7 from the stored integers λ_int, with no solver involved. At level 8 there are four dual blocks of size 289 × 289, all positive definite, and β₈ = 700548845513581 / 2^50 = 0.622212366531.

## 4. The lower-bound strategy (J = 4)
Alice and Bob use the same construction:
- A_I = C² ⊗ C⁴ (a Jordan qubit and a label), and A_O = A_I ⊗ C² (a setting register).
- In label block j, P_{0|x} = Σ_j |φ_j^x⟩⟨φ_j^x| ⊗ |j⟩⟨j|, with φ_j^x = (c_j, (−1)^{x+1} s_j) and c_j² + s_j² = 1 exactly (rational tan(t_j/4)).
- The instruments are Lüders instruments writing the setting into the register.
- W = c₀·1 + (1 − 2^{−k}) Σ_t (y_t/D) i^{m_a+m_b}(R_a ⊗ R_b + R_b ⊗ R_a), with integer matrices R.

`verify_strategy.py` checks in exact arithmetic:
1. Hermiticity and realness.
2. Process validity: every R is "pattern-pure", and every product pattern is allowed. This puts W in the valid subspace, and Tr W = 256 = d_{A_O} d_{B_O}.
3. Block structure: 26 classes per party, 676 blocks.
4. Exact positive-definiteness of all 676 integer blocks (Bareiss).
5. Instrument validity.
6. The exact value I_GYNI = 0.6221659013539084… (a rational number; so I_GYNI ≥ 0.622165901353).

The factor (1 − 2^{−k}) makes the positivity strict. The certified value is the value of this slightly shrunk strategy.
