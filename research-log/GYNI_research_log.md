> **Note (2026-09-28):** this is the unedited working log. Some decimals below were rounded to nearest. Rigorous values:
> - lower bounds rounded down: J=4 ≥ 0.622165901353 (exact 0.6221659013539…), J=3 ≥ 0.622146712690;
> - upper bounds rounded up: L4 ≤ 0.6233558, L6 ≤ 0.6222569, L8 ≤ 0.622212366531.
> See the README erratum.

# P-GYNI running log

Started 2026-09-27. Goal: rigorous dimension-free upper bound on I_GYNI below 0.7592 (Liu–Chiribella), or matching lower bounds.

## Conventions
- p(a,b|x,y) = Tr[W (M_{a|x} (x) N_{b|y})], Choi M = sum_ij |i><j| (x) M(|i><j|) on A_I (x) A_O.
- Valid bipartite W: W >= 0, Tr W = d_AO d_BO, Hilbert–Schmidt (Pauli) terms only of types
  1, AI, BI, AI.BI, AO.BI, AI.AO.BI, AI.BO, AI.BI.BO  (rule: AO in S => BI in S and BO notin S; BO in S => AI in S and AO notin S).
- I_GYNI = (1/4) sum_{x,y} p(a=y, b=x | x,y).

## Step 1 - LC reproduction (DONE)
- Memory incident: first cvxpy formulation (4 x 64x64 complex PSD, per-entry cvxpy constraints) blew up to >13 GB and was killed by the coordinator (twice). Rewrote as direct sparse Clarabel conic problem (sdp_sparse.py) + symmetry reduction: canonical instruments are real and diagonal on the setting registers O2 -> WLOG W real and block-diagonal in (O2_A,O2_B): 4 real 16x16 blocks, 99 Pauli params per process. Memory now negligible.
- LGYNI single-trigger canonical SDP: 0.819401 (LC: 0.8194). OK.
- GYNI LC bound, computed as the joint problem (4 canonical processes W'_{xi eta} + marginal consistency; this is the Lagrange dual of LC's min over single-trigger decompositions): 0.759190 (LC: 0.7592). OK. Clarabel status Solved, 0.8 s.
- Observation: LC bound == joint relaxation with only marginal consistency between the 4 pieces. Tightening requires genuinely new coupling constraints.

## Step 2 - Moment + canonical-image relaxation "MC1" (NEW)
Idea: WLOG (Naimark + absorbing pre/post-processing into the process) every instrument is a Lueders instrument of a
projective measurement {P_{a|x}} on H_A with the setting copied into an output register X. Word vectors
|w,r> = (1 (x) w)|Phi> (x) |r>. Moment matrix Gamma = Gram matrix of W on word vectors (A words x B words).
Constraints: (V1) Gamma PSD, real WLOG; (V2) word-level validity: Tr[W(L_A (x) L_B)] = 0 for L_A trace-annihilating
and L_B trace-proportional (and A<->B), =1 for TP x TP; trace functionals compared in the free algebra of two
idempotents; (V3) the four Liu-Chiribella single-trigger canonical processes W'_{xi eta} are LINEAR IMAGES of Gamma
(comb E_xi = sum_a |a>(x)P_{a|xi}; D_xi = discard O1 if register==xi, else C_x o R_xi with Kraus K_c = sum_a <a+c|(x)P_{a|xi})
and must be valid processes. All pieces now share one Gamma -> coupling beyond marginals.
- Words {1,A0,A1,A0A1,A1A0} x 2 registers per party: Gamma 100x100. 6586 raw V2 rows, 4646 independent equalities (with canonical ones), 5446 vars -> ~800 free parameters.
- Bug found & fixed: sign of RHS in canonical-image equalities (caught by plugging a genuine strategy into the assembled conic system).
- Validity tests (test_mc_validity.py): random genuine strategies (dA=2,3) satisfy V2 to 1e-16, canonical images valid to 1e-15, objective reproduced.
- RESULT (numerical, Clarabel AlmostSolved): GYNI MC1 primal 0.64348483, dual 0.64348807.  (LC: 0.759190)
- Sanity: LGYNI MC1 = 0.81940038 (exact 0.819401); 4 random single-trigger functionals: MC1 equals exact LC canonical value within 5e-6 (solver accuracy; must be >= exact if valid).
- Literature check (2026-09-27): citations of 2403.02749 (Semantic Scholar 17, INSPIRE 18), 2606.20519 (0), 2606.19438 (7) + arXiv API queries: no GYNI upper bound below 0.7592, no lower bound above 0.6219, no SDP hierarchy for process-matrix correlations beyond LC. (2609.22998's principle is trivial for binary outputs.)

- High-accuracy: SCS eps=1e-9 (493 s): status solved, primal 0.6434843197, dual 0.6434843196. Clarabel (faer): AlmostSolved, 0.6434848 / 0.6434881. Strict-feasibility test: max t with Gamma - tI >= 0 is 0.0016 (small interior), images - tI: 0.25.
- Coordinator (after API reset) asked: validity proof in REPORT.md; OCB check; general-strategy feasibility test; seesaw-strategy containment; exact certificate; MC2.
- Plan: rewrite as general module mc2.py with register-block-diagonal Gamma (WLOG by twirling the output setting register with Z/Fourier phases - a local unitary on outputs; kills off-register Gram entries) -> 4 blocks 25x25 instead of 100x100; image validity imposed directly as forbidden-Pauli-component equalities on Gamma (no auxiliary variables) -> clean Lagrangian dual for exact certification.

## Step 3 - Validity proof of the MC relaxation (for the record)

Lemma 1 (Lueders normal form, every dimension). For every strategy (W; M_{a|x}; N_{b|y}) there are finite-dim H_A, H_B,
projectors P_{a|x} (sum_a P_{a|x} = 1), Q_{b|y}, and a valid process W~ on H_A (x) (H_A (x) X) (x) H_B (x) (H_B (x) Y)
(X = C^{nA}, Y = C^{nB} setting registers) with Tr[W~ (M~_{a|x} (x) N~_{b|y})] = p(a,b|x,y), where
M~_{a|x}(rho) = P_{a|x} rho P_{a|x} (x) |x><x|_X.
Proof: Kraus M_{a|x}(rho) = sum_k K_{akx} rho K_{akx}^+. H_A := A_O (x) C^m (x) C^kappa (x) C^d' (d' so that dim A_I <= dim H_A),
J: A_I -> H_A fixed isometry, V_x := sum_{a,k} K_{akx} (x) |a>|k>|0> (isometry A_I -> H_A). Extend V_x J^+ to a unitary U_x
(U_x J = V_x). P_{a|x} := U_x^+ (1 (x) |a><a| (x) 1) U_x, T_x(s) := Tr_{C^m C^kappa C^d'}[U_x s U_x^+]. Then
M_{a|x} = T_x o L_{a|x} o J(.)J^+ with L_{a|x}(s) = P s P. Let T(w) := sum_x T_x(<x|w|x>_X) (a channel) and
Phi_A(F) := T o F o J(.)J^+ ; at Choi level Phi_A(C) = sum_k (J^T (x) T_k) C (J^T (x) T_k)^+ (CP), and Phi_A maps channels
to channels. W~ := (Phi_A^+ (x) Phi_B^+)(W) is PSD and gives 1 on all product channels -> valid. Phi_A(M~_{a|x}) = M_{a|x}. QED
WLOG symmetrisations (used only via convexity): register twirl by clock unitaries on X,Y (local unitaries on outputs;
all M~ are X-diagonal) -> Gamma block-diagonal in (rA,rB); complex conjugation (W~*,P*,Q*) is a strategy with same p
-> Gamma real.
Moment matrix: word vectors |w,r> = (1 (x) w)|Phi> (x) |r>, Gamma[(k,l),(k',l')] = <k,l|W~|k',l'>. |k'><k| is the Choi of
rho -> w' rho w^+ (x) |r'><r|, trace functional Tr_{A_O}|k'><k| = delta_{rr'} (w^+ w')^T.
(V1) Gamma PSD (Gram matrix of W~ >= 0).
(V2) If sum c delta w^+ w' = 0 in the FREE algebra of idempotents (=> as operators in every realisation; L_A trace-
annihilating) and sum d delta v^+ v' = lambda*1 (L_B trace-proportional) then sum c d Gamma = 0; TP x TP -> 1.
Proof: for a channel C_B, Tr_B[W~(1 (x) C_B)] is a one-party process rho (x) 1_{A_O}; trace-proportional maps are linear
combinations of channels (HP/anti-HP split; HP-TP maps = affine hull of channels since the depolarising channel is in
the relative interior), so Tr_B[W~(1 (x) Choi L_B)] = tau (x) 1 with Tr tau = lambda, and pairing with Choi L_A gives
Tr[tau^T Tr_{A_O} Choi L_A] = 0 for TA L_A (= lambda for TP). Same with A<->B. QED
(V3) For each trigger pair (xi,eta): E_xi(rho) = V rho V^+, V = sum_a |a>_R (x) P_{a|xi} (isometry H_A -> R (x) H_M);
D_xi reads register O2=r classically: r = xi -> discard O1, output H_M, write |xi>; r = x != xi -> R_xi(s) = sum_c K_c s K_c^+,
K_c = sum_a <a+c|_{O1} (x) P_{a|xi} (sum_c K_c^+K_c = 1, K_0 V = 1, K_1 V = 0), then Lueders channel C_x, write |x>.
T -> D_xi o (T (x) id_M) o E_xi is CP-preserving (link product with PSD Choi operators) and channel-preserving, so the
linked process W'_{xi eta} is valid on (C^2, C^2 (x) C^nA, C^2, C^2 (x) C^nB); it reproduces p(a,b|xi,eta) and the LC
non-trigger marginals exactly (it IS LC's canonical process). Effective Choi of canonical unit |c><c'| (c=(i,o,r)):
r = xi: delta_{oo'} |P_{i|xi},xi><P_{i'|xi},xi| ; r = x != xi: delta_{o+i,o'+i'} sum_a' |P_{a'|x}P_{i|xi},x><P_{a'|x}P_{i'|xi},x|.
So W'_{xi eta} = linear image of Gamma; impose image PSD (register blocks), forbidden HS components = 0, Tr = dAO dBO.
Objective p(a,b|x,y) = <P_{a|x},x;Q_{b|y},y|W~|...> linear in Gamma.
THEOREM: MC value >= I_GYNI of every strategy in every dimension; MC <= LC (V3 implies the LC joint problem).

## Step 4 - reformulations for robustness
- mc2.py: register-block Gamma (GYNI MC1 words: 4 blocks 25x25, 1300 vars), image validity as forbidden-Pauli equalities.
- Clarabel chordal decomposition caused NumericalError -> disabled. nssolve.py: eliminate all equalities by an orthonormal
  null-space basis (eigendecomposition of A^T A), solve pure PSD problem (well conditioned, no redundancy).
- Reduced-form results (Clarabel, AlmostSolved): GYNI MC1 (words <=2) 0.6434842814 / dual 0.6434845707 (2.5 s);
  GYNI minimal canonical words 0.6750326; LGYNI minimal 0.8194007, words<=2 0.8194004 (exact 0.819401; consistent).
- OCB (Bob 4 settings, minimal canonical words, 8 blocks 32x32, 8 images): system feasible at genuine strategies
  (residual 6e-14), Clarabel NumericalError -> SCS run started.
- MEMORY INCIDENT 2: OCB with all words <=2 (blocks 85, 29240 vars) -> dense QR tried to allocate ~10 GB; memguard aborted
  (it overshot to 10 GB before the 0.5 s poll). Fix: nssolve refuses dense allocations > 2 GB; watchdog poll 0.1 s.

## Step 5 - Validation + EXACT CERTIFICATE (MC1, words of length <= 2)
- Containment test with GENERAL instruments (mc_feas.py): random boundary valid W (d=2,3), causally separable W with
  random channels (d=2,3), OCB process + random local unitaries; random general (non-projective, non-Lueders) 2-outcome
  instruments with 2 Kraus ops per outcome. min delta (max |p_MC - p_target|) <= 1.7e-9 in all 15 cases -> contained.
  (These points are interior-ish, GYNI ~0.25; stronger tests with seesaw strategies below.)
- Seesaw (real W, real general instruments, d=2): best 0.56940072 = Boghiu-Simonov d=2 value 0.5694 (reproduced).
- EXACT CERTIFICATE (certify.py): eps-margin dual (eps=1e-7), Clarabel; lambda (free multipliers of all 1816 equality
  rows) and image duals Z_m rounded to rationals (denominators <= 1e12); Gamma-block duals Y_k DEFINED exactly by
  stationarity; exact rational symmetric Gaussian elimination: all 4 Y_k (25x25) positive definite (min pivot 2.4e-7),
  all 16 Z_m (16x16) positive definite (min pivot 1.0e-7).
  ==> CERTIFIED: I_GYNI <= beta = 0.6434936237 (exact rational, 56-digit denominator), valid in every dimension.
  (Numerical MC1 optimum 0.6434843; margin cost 9e-6.) Certificate saved: cert_mc1_gyni.pkl.

## Step 6 - Ablations: what gives the improvement?  (Clarabel, reduced form, lineality pruned)
- images + V2, NO Gamma PSD: 0.75918997  (= LC exactly)
- images only (no V2, no Gamma PSD): 0.75918995 (= LC)
- Gamma PSD + V2, NO canonical images: 0.64348431 (= full MC1)  -> the LC canonical images are IMPLIED
  (image PSD = sum of congruences of Gamma; image validity = V2 rows for comb-derived maps, since every identity used in
  the comb calculus holds in the free idempotent algebra).
- => The relaxation is a clean NPA-like hierarchy: "moment matrix of the process on word vectors (1 (x) w)|Phi> (x) |r>,
  Gamma PSD, trace-functional (TA x TP) validity in the free algebra". Key ingredient = Gamma PSD coupling.
- Hierarchy levels (words of length <= L, both registers): L=1: 0.7462629 (already < LC 0.7592!); L=2: 0.6434843; L=3 running.
- no-V2 ablation and the with-images L=3 SCS run were killed (redundant; CPU budget).

## Step 7 - Symmetry reduction + hierarchy level 3
- symmetry.py: GYNI group generated by party swap, (x->1-x, b->1-b), (y->1-y, a->1-a); implemented as linear maps on
  word space (letter swap / complement substitution B -> 1-B are automorphisms of the free idempotent algebra, so V2 is
  invariant). Verified against explicitly transformed genuine strategies (errors ~1e-16). Imposed as equalities (valid:
  group average of feasible points is feasible with the same objective).
- nssolve: exact affine union-find elimination of 1-/2-term rows before the dense null space (enables larger levels).
- RESULTS (pure hierarchy, Clarabel AlmostSolved):
  L=1: 0.7462629 | L=2: 0.6434843 (nullity 58 with symmetry) | L=3: 0.62674 (primal 0.6267400, dual 0.6267556; nullity 162; 77 s)
  => gap to the seesaw lower bound 0.6219 is now ~0.0048 (was 0.137 with LC).

## Step 8 - EXACT CERTIFICATES for the pure hierarchy with symmetry (certify2.py / verify2.py)
Method: eps-margin primal (obj + eps*sum Tr Gamma_k), Clarabel; dual Y_k = solver dual + eps*I; project the
stationarity vector onto the consistent affine space (N^T(o+u)=0, N = null space of the rows); LSQR for the free
multipliers lam of ALL equality rows (V2 + symmetry), round lam to common denominator D = 2^50; DEFINE Y_k exactly by
stationarity; certify Y_k PD exactly by Sylvester's criterion (all leading principal minors > 0, fraction-free Bareiss
integer elimination). beta = lam.b exactly. Standalone verifier verify2.py (no solver) re-checks from saved lam.
- L=2 (eps=1e-7): PD True, beta = 724502058451657 / 2^50 = 0.643487093345   (cert2_L2_sym.pkl)
- L=3 (eps=1e-6; eps=1e-7 failed: LSQR residual 1e-7 destroyed the 1e-7 margin -> added projection step):
  PD True (smallest pivot 7.5e-6), beta = 352853192480783 / 2^49 = 0.626793181767   (cert2_L3_sym.pkl)
  ==> RIGOROUS: I_GYNI <= 0.6267932 in every dimension. Gap to 0.6219 now 0.0049.

## Step 9 - Validation (coordinator items 2a-2c)
(a) OCB (Bob 4 settings) and LGYNI at hierarchy level 1: OCB 0.9045083 >= (2+sqrt2)/4 = 0.8535534 (valid, not tight);
    LGYNI 0.8942997 >= 0.819401 (valid). (OCB with images/SCS run was killed for memory; OCB L=2 to be run after L=4.)
(b) GENERAL-instrument strategies: (i) solver-based containment (mc_feas.py): 15 random strategies (boundary valid W d=2,3;
    causally separable W; OCB process + random local unitaries) with random general 2-Kraus instruments: min delta <= 2e-9.
    (ii) SOLVER-FREE check of Lemma 1 (lemma1_check.py): explicit construction of the Lueders normal form (Kraus from
    Choi, isometry V_x, unitary completion U_x, P_{a|x} = U_x^+ (1 (x) |a><a| (x) 1) U_x, absorbed Kraus J^T (x)
    [(1 (x) <e|) U_x (x) <x|]) and Gamma computed as a sum of Gram matrices: all V2 rows satisfied to <= 1.6e-15 (random,
    OCB) and 3.9e-11 (seesaw optimum; limited by that strategy's own instrument normalisation accuracy), Gamma PSD,
    p reproduced (<= 6e-11).
    Negative controls (L=2): isotropic mixtures of the perfect GYNI box with white noise are rejected iff GYNI > MC value:
    GYNI 0.60/0.62/0.63 -> delta ~1e-9 (accepted), 0.66 -> 0.021, 0.70 -> 0.059, 1.0 -> 0.357 (rejected).
(c) Explicit high-value strategy: real d=2 seesaw optimum 0.569401 is contained (both tests above). d=3 seesaw running.

## Step 10 - more checks
- test_rows_L.py: all 7106 level-3 V2 rows satisfied by genuine strategies (boundary W, d = 2,3,4, projector ranks 1,2)
  to <= 3.3e-16; symmetry map s_fx verified at level 3 (<= 7e-16).
- inspect_L.py (level 3 optimum): the optimal box is fully symmetric: p(a=y,b=x|x,y) = 0.626740 for all (x,y),
  p(a=y, b!=x) = p(a!=y, b=x) = 0.077773, p(both wrong) = 0.217713; marginal guessing probability 0.704513 per party.
  Gamma blocks (49x49) have numerical rank 36-39 -> not flat, no finite-dimensional strategy can be read off.

## Step 11 - hierarchy level 4 (with symmetry)
- L=4: 13284 vars -> 6332 UF roots, 45760 multi-term rows, rank 5984, nullity 348; Clarabel AlmostSolved:
  primal 0.6232682743, dual 0.6232777874 (1239 s, peak 4.44 GB).
- Sequence: L1 0.74626 | L2 0.64348 | L3 0.62674 | L4 0.62327 (differences 0.1028, 0.0167, 0.0035; ratio ~0.2)
  -> naive geometric extrapolation L_inf ~ 0.6222-0.6225, i.e. consistent with the seesaw value 0.6219 being (close to)
  optimal. Certificate for L=4 next.

- test_rows_L.py --maxlen 4: all 20820 level-4 V2 rows satisfied by genuine strategies (d=2,3,4) to <= 3.9e-16;
  s_fx symmetry map verified at level 4 (<= 1.1e-15).


=====================================================================================================================
# FINAL REPORT (P-GYNI, 2026-09-28)
=====================================================================================================================
## 1. Headline
A new NPA-type SDP hierarchy for bipartite process-matrix correlations ("Lueders-word moment hierarchy") gives
dimension-free upper bounds on I_GYNI far below Liu-Chiribella (LC):
  level:            L=1       L=2        L=3        L=4
  numerical value:  0.746263  0.643484   0.626740   0.623268 (primal) / 0.623278 (dual)
  CERTIFIED (exact rational dual, solver-free verification):
                    -         0.6434871  0.6267932  (L=4: see Step 12)
Previous: LC 0.7592 (reproduced: 0.759190); seesaw lower bound 0.6219 (Boghiu-Simonov; our real d=2 seesaw
reproduces their d=2 value 0.569401). Certified gap reduced from 0.137 to 0.0049 (L=3); numerical L=4 gap 0.0014.

## 2. The relaxation (validity proof: Step 3)
(i) Lueders normal form (Lemma 1): WLOG instruments are Lueders instruments of projective measurements P_{a|x} on H_A
    with the setting copied to an output register X; x-independent pre-processing (isometry J) and the X-controlled
    post-processing are absorbed into a new VALID process W~ (Choi-level CP adjoint, channel-preserving).
(ii) Word vectors |w,r> = (1 (x) w)|Phi> (x) |r>, w = words in A_x = P_{0|x}; moment matrix Gamma = <k,l|W~|k',l'>;
    WLOG real (complex conjugation) and register-block-diagonal (twirl of the output registers).
(iii) Constraints: Gamma PSD; V2: Sum c d Gamma = 0 whenever the Alice combination is trace-annihilating and the Bob
    combination trace-proportional (or vice versa), where the trace functional of the pair (w,r)->(w',r') is
    delta_{rr'} w^dag w' evaluated in the FREE algebra of two idempotents (so the identities hold in every
    realisation/dimension); = 1 on TP x TP. (Proof: reduced one-party processes are rho (x) 1.)
(iv) GYNI symmetry (party swap; x->1-x with b->1-b; y->1-y with a->1-a): letter swap / B->1-B are automorphisms of
    the free algebra; symmetrised moment matrices are feasible with the same objective.
Level L = all words of length <= L in both registers. Monotone in L. The Liu-Chiribella canonical single-trigger
processes are linear images of Gamma (explicit comb Kraus operators in the word algebra) and their validity/PSD is
IMPLIED by (iii) (checked numerically: with/without images identical, 0.64348431), so level >= 2 contains LC's
relaxation; level 1 (0.7463) already beats LC. Key ingredient (ablation): Gamma PSD (without it one gets LC exactly).

## 3. Certification (certify2.py; verify2.py re-checks from saved multipliers without any solver)
eps-margin primal (objective + eps*Sum Tr Gamma_k); dual Y_k from Clarabel + eps*I; projection of the stationarity
vector onto the consistent affine space; LSQR for the free multipliers of ALL equality rows; multipliers rounded to a
common denominator 2^50; Y_k DEFINED exactly by stationarity; PD certified by Sylvester's criterion with fraction-free
Bareiss integer elimination; bound beta = lam.b exactly.
  L=2: beta = 724502058451657/2^50 = 0.643487093345 (eps=1e-7)
  L=3: beta = 352853192480783/2^49 = 0.626793181767 (eps=1e-6)
Rows are generated by code; every row type was tested on genuine strategies (all 7106 L=3 and 20820 L=4 V2 rows,
d = 2,3,4, boundary W: residual <= 4e-16; symmetry maps vs transformed strategies <= 1e-15).

## 4. Validation
- LC reproduced (0.759190, LGYNI 0.819401). LGYNI in the hierarchy: L1 0.8943, L2 0.81940 (= exact, tight).
- OCB: L1 0.9045 >= (2+sqrt2)/4 = 0.85355 (valid). (L2 OCB runs were stopped for memory/time.)
- General (non-projective) instruments: solver-based containment of 15 random strategies (delta <= 2e-9) and a
  solver-free explicit construction of the Lueders normal form (lemma1_check.py) for random, OCB-process and the
  optimal d=2 seesaw strategy (0.569401): all rows satisfied (<= 4e-11, limited by the seesaw strategy's own accuracy).
- Negative controls: noisy perfect-GYNI boxes rejected exactly when GYNI > level value.

## 5. Next steps
- Level 5 (29.5k variables; needs sparse exact elimination or symmetry-adapted block diagonalisation).
- Convergence of the hierarchy to the process-matrix value (GNS-type reconstruction of a valid process) is OPEN.
- Extract near-optimal strategies from the level-4 moment matrix to attack the remaining 0.0014 gap from below.
- Apply to LGYNI variants, OCB family, multipartite causal inequalities (code is general in #settings).

- (check) LGYNI, pure hierarchy L=2 (no images): 0.8194007221 / 0.8194007236 = exact LC value 0.819401 -> tight.

## Step 12 - EXACT CERTIFICATE at level 4 (with symmetry)
- certify2.py --maxlen 4 --eps 2e-6: Clarabel AlmostSolved (eps-objective primal 0.6233719, dual 0.6233817; plain
  objective at the solution 0.6232681), dual min eig 2.0e-6; stationarity violation 7.9e-7 projected away (min eig
  1.44e-6 after projection); LSQR residual 2e-13; exact Bareiss/Sylvester: all four 81x81 Gamma-block duals PD
  (smallest pivot 1.4e-5).
  ==> CERTIFIED: I_GYNI <= beta = 701865376290605 / 2^50 = 0.623381680756, valid in every dimension.
  Independent solver-free re-verification (verify2.py cert2_L4_sym.pkl): PD True, same beta (9.8 s).
- Cross-solver check: L=2 with SCS (eps 1e-9): 0.6434843139 / 0.6434843136 (Clarabel 0.6434843).
- Certified gap to the best lower bound (0.6219, Boghiu-Simonov): 0.00148.

## Step 13 - OCB tightness + cross-checks
- OCB (Bob 4 settings; Alice words <= 1, Bob canonical words; ocb_check2.py): Clarabel 0.8535530 (primal) /
  0.8535532 (dual) vs exact (2+sqrt2)/4 = 0.8535534 -> the hierarchy REPRODUCES the exact OCB maximum (to solver
  accuracy ~3e-7). Solver-free containment (ocb_contain.py): the optimal OCB strategy (OCB process, Alice Z-measure &
  prepare |x>, Bob Z-measure (b'=0) / X-measure & prepare |y+b> (b'=1)) put in Lueders normal form satisfies all rows
  (5.6e-16), PSD (-7e-16), objective 0.8535533906 -> relaxation value >= (2+sqrt2)/4 exactly; hence tight.
- SCS cross-check of L=3 (sym): solved, 0.6267499317 / 0.6267499319 (Clarabel AlmostSolved 0.6267400 / 0.6267556).

## FINAL REPORT - update of Section 1 (supersedes the draft headline above)
  level:            L=1       L=2        L=3                    L=4
  numerical:        0.746263  0.643484   0.626750 (SCS solved)  0.623268 (primal) / 0.623278 (dual), Clarabel
  CERTIFIED bound:  -         0.64348709 0.62679318             0.62338168   (exact rationals x/2^50 or x/2^49)
  => RIGOROUS, DIMENSION-FREE:  I_GYNI <= 0.6233817  (701865376290605 / 2^50), certificate cert2_L4_sym.pkl,
     verified solver-free by verify2.py.  Previous best 0.7592 (LC).  Best lower bound 0.6219 (seesaw, B-S 2026).
     Remaining gap 0.0015 (was 0.137): 98.9% of the gap closed.
  Tightness checks of the same hierarchy: LGYNI 0.819401 (exact, LC) and OCB (2+sqrt2)/4 (exact) are reproduced.
  Files: mc2.py (relaxation), symmetry.py, nssolve.py (UF + null space + Clarabel/SCS), hier.py, certify2.py,
  verify2.py, validation: genuine.py, test_rows_L.py, lemma1_check.py, mc_feas.py, mc_feas2.py, ocb_contain.py,
  test_symmetry.py; LC reproduction: lc_reproduce.py; seesaw.py (lower bounds).

## Step 14 - lower bounds + final containment
- Real seesaw d=3 (general real instruments, 8 starts): best 0.60463279 (seeds: 0.6028, 0.5000, 0.6046, 0.5694,
  0.6018, 0.6002, 0.6006, 0.6043). (B-S complex d=3: 0.6104; no attempt to beat 0.6219, as instructed.)
- Solver-free containment of this 0.604633 strategy (dH = 54 Lueders normal form) at L=2 and L=3: all rows satisfied
  to 2.5e-13 (limited by the strategy's own normalisation accuracy), Gamma PSD (min eig -1.7e-16), p reproduced 2.7e-13.
## Incidents / honesty notes
- Two memory incidents: (1) first cvxpy formulation reached 13.5 GB (killed twice by coordinator); (2) a dense QR for
  OCB at full word length 2 tried ~10 GB (memguard aborted). Afterwards: sparse direct solvers, UF elimination,
  2 GB dense-allocation guard, 0.1 s watchdog; later runs peaked at 4.44 GB.
- Solver statuses are mostly "AlmostSolved" (degenerate SDPs); all headline bounds are therefore stated only via the
  exact certificates. Rigor rests on (a) the written validity proof (Step 3/Final Report), (b) the code-generated rows
  (every row type tested on genuine strategies d=2..4 to ~1e-16; symmetry maps verified; LGYNI and OCB exact values
  reproduced), (c) exact rational verification of the dual (verify2.py).
- Open: convergence of the hierarchy to the process-matrix value (no proof); whether 0.6219 is optimal.

## Step 15 - Coordinator: close the gap (level 5+, strategy extraction, PSLQ). Plan:
- Switch word basis to observables O_x = 2A_x - 1 (O_x^2 = 1): words = elements of the infinite dihedral group Z2*Z2;
  same span at each level L (triangular change of basis) -> identical relaxation value. Advantages: trace functional
  of a pair = single group element w^{-1}w'; the GYNI symmetry maps become SIGNED PERMUTATIONS (O -> -O for output
  relabelling) -> no fill-in; union-find removes all symmetry rows; only block (0,0) needs a PSD cone (others are
  signed-permutation congruences); block (0,0) splits into swap-symmetric/antisymmetric parts.
- Certificate: reduced dual Yhat on block (0,0) -> spread to all blocks Y_k = S_k^T Yhat S_k / 4 -> LSQR multipliers for
  the FULL row list -> rational rounding -> exact PD check of all Y_k (existing verify_exact).

- mc3 (dihedral basis) validated: V2 rows on genuine strategies d=2,3,4 (<= 2e-15), objective equals idempotent-basis
  value, fx/fy signed-permutation maps vs transformed strategies (<= 8e-16).
- hier3 (single PSD block (0,0), swap split): L=2 0.6434843145 (Solved, 0.1 s); L=3 0.6267499151 (0.5 s);
  L=4 0.6232747193 / dual 0.6232747194 (Solved, 27 s, 0.67 GB)  [previously 1239 s, 4.4 GB].

## Step 16 - LEVEL 5 solved and CERTIFIED
- hier3 L=5: 29524 vars -> 2746 UF roots -> nullity 640; cones 66+55; Clarabel Solved: 0.6224091565 / 0.6224091566
  (214 s, 1.5 GB).
- certify3 (dihedral, symmetric, margin eps*Tr Gamma00 with eps=1e-7 -> cost 1.21e-5):
  L=4: beta = 701836146356539/2^50 = 0.623355719359 (eps 1e-6)
  L=5: beta = 350392017401955/2^49 = 0.622421256583  -> all four 121x121 dual blocks PD (Bareiss), exact.
  ==> RIGOROUS: I_GYNI <= 0.6224213 in every dimension. Gap to 0.6219 (seesaw): 0.00052.
- Sequence L1..L5: 0.746263, 0.643484, 0.626750, 0.623275, 0.622409; successive differences 0.1028, 0.01673,
  0.003475, 0.000866 (ratios 0.163, 0.208, 0.249).

## Step 17 - structure of the optimum / lower-bound families
- Qubit Lueders family (H_A = H_B = C^2, one Jordan angle per party, setting register; lueders_J1.py; exact SDP over W
  for fixed angles, 19x19 grid + Nelder-Mead): max 0.6067069 at tA = tB = 0.62943 rad (36.06 deg).
  Any process that dephases the Jordan label is a mixture of such strategies => <= 0.6067: beating 0.6067 REQUIRES
  coherence between Jordan blocks with different angles.
- Level-5 optimum, Alice's reduced functional phi(g) (Bob: identity channel): phi(O_x) = 0.4654, moments of
  U = O_0 O_1: c_k = phi(U^k) = [1, 0.3217, 0.0306, -0.1206, 0.0308, 0.0712] -> not a single angle (single-atom fit
  predicts c_2 = -0.793): the relaxation optimum spreads over many Jordan angles, consistent with the seesaw value
  creeping up with dimension (B-S: d=4 0.6217, d=5 0.6218, d=6,7 0.6219) and suggesting the supremum may only be
  approached in the limit d -> infinity.

- Observation used for cheaper certificates: in the dihedral basis every diagonal entry of Gamma_00 is a TP x TP pair
  (unitary words) and is fixed to 1 by V2, so Tr Gamma_00 = N is constant on the feasible set. Hence Yhat = Y_opt +
  eps*I is an exact-stationarity dual whenever Y_opt is (no second "margin" solve needed); cost eps*N.
  Re-certified L=5 from the plain solve: beta = 350392017421605/2^49 = 0.622421256618 (PD True).
- J2 Lueders family (two Jordan angles per party, coherent label; lueders_J2.py): commutant of the label twirl
  U (x) conj(U) on (l_in,l_out) = span{II,IZ,ZI,ZZ,XX-YY,XY+YX}; 1411 invariant valid real basis elements, 36 sector
  blocks (<= 64). Check: equal angles reproduce the J=1 value 0.6067070. Angle optimisation running.

- Heuristic extrapolation of L1..L5 (extrapolate.py; NOT rigorous): geometric tail / Aitken 0.62212; linearly
  increasing ratios 0.62200; power law a + b L^-c (exact fit to L=3,4,5) 0.62188. All consistent with the
  hierarchy converging to ~0.6219-0.6221, i.e. to (or very near) the seesaw value 0.6219.

## Step 18 - custom Schur-complement IPM (ipm.py, hier_ipm.py)
- HKM direction + Mehrotra predictor-corrector for the reduced LMI (cones = swap-split block (0,0)); Schur complement
  k x k (k = nullity) costs O(k^2 n^2 + k n^3) instead of Clarabel's svec-space Hessians.
- Validation vs Clarabel/SCS: L=3 0.6267499226/0.6267499230 (0.3 s), L=4 0.6232747192/0.6232747200 (1.6 s),
  L=5 0.6224091564/0.6224091574 (11.6 s, 1 thread; Clarabel needed 214 s). Relative gap ~5e-10, pinf ~1e-11.
- Clarabel L=6 run killed after ~30 min (superseded by the IPM).

- IPM L=6: 0.6222399110 (dual b.y) / 0.6222399121 (primal <C,X>), 18 iterations, 34 s, 1.8 GB.
  Differences L4->L5 0.0008656, L5->L6 0.0001692 (ratio 0.196, DEcreased from 0.249).

## Step 19 - LEVEL 6 CERTIFIED
- certify3 --from_file ipm_L6.pkl (IPM dual + 1e-7*I; no projection needed: LSQR residual 1.2e-12):
  all four 169x169 dual blocks PD (Bareiss); beta = 175149721699139/2^48 = 0.622256812119.
  ==> RIGOROUS: I_GYNI <= 0.6222569. Gap to 0.6219: 0.00036.

## Step 20 - L=7 BUG found and fixed (no certified claim affected)
- First IPM L=7 run returned 0.6230079 > L6 (impossible: hierarchy is monotone). check_sol.py: that z violates
  141880 rows (max 0.037). Cause: LAPACK dsyevr subset-by-value (bisection + inverse iteration) returned an
  inaccurate basis for the 1638-fold zero eigenvalue cluster of A_r^T A_r (max |A_r N| = 3.5e-2; the same call in a
  test run happened to give 3e-14 -> nondeterministic failure). The spectrum itself is clean (1638 eigenvalues
  < 1e-11, none in [1e-11, 1e-2]).
- Fix: full divide-and-conquer eigh (np.linalg.eigh) up to 12000 roots, after freeing the Python row objects
  (consume=True); every null basis is now CHECKED (max |A_r N| <= 1e-8 else abort). L<=6 results were computed with
  the dense path (verified: L6 solution satisfies all 265742 rows to 4e-14; certificates are independent of this
  step anyway since verify3 re-checks exactly).

- Flatness (L=6 IPM optimum, block (0,0)): rank 134/169 (tol 1e-4) vs 109/121 on words <= 5; 154 vs 117 at 1e-8 ->
  NOT flat; no finite-dimensional strategy can be read off (consistent with a spread of Jordan angles).

## Step 21 - LEVEL 7 (IPM, robust null space)
- L=7: 101700 vars -> 10088 roots, nullity 1638 (spectral gap [2.9e-13, 8.0], max |A_r N| = 3.4e-13);
  IPM 20 iterations: 0.6221973574 (dual) / 0.6221973591 (primal), 112 s, peak 4.63 GB.
- Sequence L1..L7: 0.746263, 0.643484, 0.626750, 0.623275, 0.622409, 0.622240, 0.622197
  differences 0.10278, 0.016734, 0.003475, 0.000866, 0.000169, 0.0000426; ratios 0.163, 0.208, 0.249, 0.196, 0.251.
  Geometric extrapolation (ratio 0.25-0.30): limit ~ 0.62218 +- 0.00002  (> seesaw 0.6219).

## Step 22 - LEVEL 7 CERTIFIED; two-Jordan-block family reaches 0.6215
- certify3 L=7 (IPM dual + 1e-7 I): all four 225x225 dual blocks PD (Bareiss, 288 s);
  beta = 700557281382181/2^50 = 0.622219859087.  ==> RIGOROUS: I_GYNI <= 0.6222199. (standalone verify3 running)
- Two-Jordan-block Lueders family (J=2; symmetric angles (t1,t2) for both parties; exact W-SDP per point, Clarabel
  AlmostSolved, ~25 s per point): grid t in {0.3,0.5,0.63,0.8,1.0,1.2}:
    best 0.6215449 at (0.3,1.0); (0.3,1.2) 0.6214655; (0.5,1.2) 0.6208675; (0.3,0.8) 0.6194902; equal angles
    reproduce J=1 (0.6067087 at 0.63). => coherent superposition of TWO Jordan angles already gives ~0.6215
    (vs 0.6067 for one angle); refinement running.

- verify3.py cert3_L7.pkl (standalone, no solver): all dual blocks PD = True; VERIFIED BOUND = 0.622219859087
  (= 700557281382181/2^50), 250 s.

- J2 refinement (Nelder-Mead, 40 evals, symmetric angles): 0.62179063 at (t1, t2) = (0.39646, 1.22663) rad
  [(22.7 deg, 70.3 deg)] (Clarabel AlmostSolved; exact verification next). A strategy with H_A = C^2 (x) C^2
  (two qubit Jordan blocks, coherent label) essentially reaches the best known seesaw value 0.6219 (B-S, d=6,7).

- Note: a stray taskkill /IM python.exe was run at some point; this explains the unexplained
  exit-code-1 termination of the first J2 Nelder-Mead run and the OCB level-2 check. All results reported in this log
  come from runs that completed and printed their final lines; nothing is inferred from killed runs.

## Step 23 - RIGOROUS LOWER BOUND from an explicit two-Jordan-block strategy (j2_exact2.py)
- Rational angles (tan(t/2) rational): (cos,sin) = (459543/498185, 192376/498185) [t1 = 0.39645825] and
  (27393/81185, 76424/81185) [t2 = 1.22662731]; Alice = Bob.  H_A = C^2 (Jordan qubit) (x) C^2 (label),
  A_0 = |0><0| (x) 1, A_1 = sum_j |t_j><t_j| (x) |j><j|; Lueders instruments + setting register (A_I = C^4, A_O = C^8).
- W from the exact-instrument SDP (Clarabel), coefficients rounded to denominator 2^40 in the invariant valid Pauli
  basis (=> valid subspace + normalisation exact by construction), mixed with the maximally mixed process with weight
  2^-21; all 36 sector blocks certified PD exactly (Sylvester via Bareiss on integer matrices).
- EXACT GYNI value (rational arithmetic): 0.621789802790.  ==> RIGOROUS LOWER BOUND I_GYNI >= 0.6217898 with an
  explicit strategy in local dimension 4 (input) / 8 (output incl. register). (Best known: 0.6219, B-S d=6,7.)
- Asymmetric angles (4-parameter Nelder-Mead, ~35 evaluations) did not improve on the symmetric optimum (max 0.6217904).
- Killed jobs: the first j2_exact_strategy.py (Fraction LDL too slow) was superseded by j2_exact2.py.

=====================================================================================================================
# FINAL REPORT v2 (2026-09-28) - supersedes the earlier headline
=====================================================================================================================
UPPER BOUNDS (rigorous, dimension-free; exact rational duals, verified by solver-free scripts verify2/verify3):
  level L:        2          3          4          5          6          7
  certified:   0.6434871  0.6267932  0.6233557  0.6224213  0.6222568  0.6222199
  (L7 = 700557281382181 / 2^50; cert3_L7.pkl; verify3.py: PD True)
  numerical:   0.6434843  0.6267499  0.6232747  0.6224092  0.6222399  0.6221974   (L1: 0.7462629)
  heuristic extrapolation of L1..L7 (NOT rigorous): 0.62208 (power law) - 0.62218 (geometric/Aitken).
LOWER BOUNDS: best known 0.6219 (Boghiu-Simonov seesaw, d=6,7). Ours (rigorous, exact rational verification):
  I_GYNI >= 0.6217898 with an explicit, highly structured strategy: two qubit Jordan blocks (angles 22.7 deg and 70.3 deg)
  in coherent superposition via a label qubit (A_I = C^4, A_O = C^4 (x) setting register); one Jordan block only gives
  0.6067 (exact SDP), so label coherence is essential.
GAP: certified 0.6222199 - 0.6219 = 3.2e-4 (was 0.137 with Liu-Chiribella). Not closed to 1e-4 -> no PSLQ attempted.
  The hierarchy appears to converge to ~0.6221-0.6222, i.e. slightly ABOVE the best seesaw value: either strategies
  better than 0.6219 exist (requiring more than two Jordan angles / larger dimension), or the hierarchy is not tight.
Technical: observable (dihedral) word basis -> symmetry = signed permutations -> single PSD block (swap-split);
  custom HKM/Mehrotra IPM (ipm.py) with Schur complement -> L=5 in 12 s, L=6 in 34 s, L=7 in 112 s (Clarabel: 214 s,
  >30 min, infeasible); robust null space (checked max|A_r N|); L=7 bug (inaccurate LAPACK subset eigenvectors) caught
  by the monotonicity check and fixed before any claim.

## Step 24 - Coordinator round 3: J>=3 Jordan families (lower side), level 8 if cheap, convergence argument.
Plan (lower side): general-J Lueders family in the BISECTOR basis of each Jordan qubit (A_0 at -t_j/2, A_1 at +t_j/2):
then the GYNI group acts by theta-INDEPENDENT signed maps (fx: Z on Alice's Jordan qubits + register flip + R90 on
Bob's; fy symmetric; swap), so the invariant valid basis = orbit sums, computed once per J. Label twirl commutant:
{1x1, D_k x 1, 1 x D_k, D_k x D_m, |a><c|x|a><c| + h.c., i(...)} (dim 2J^2-J). Only register block (0,0) and sector
blocks (cA <= cB) need PSD; objective = <u_00|W|u_00>.

- Null space by connected components: after union-find the multi-term rows split into many small components
  (L=6: 264 comps, largest 264 roots; L=7: 357 comps, largest 364). Component-wise SVD gives a SPARSE orthonormal
  null basis; L=6 reproduced exactly (0.6222399110; peak 0.73 GB vs 1.8 GB). Lineality pruning via k x k Gram matrix.
  -> level 8 is cheap: running.

## Step 25 - LEVEL 8 + first J=3 result
- L=8 (IPM, component null space: 464 components, largest 480 roots, nullity 2392, cones 153+136):
  0.6221834652 (dual) / 0.6221834665 (primal), 21 its, 220 s, peak 2.63 GB.
- JModel (general J, bisector basis, GYNI-group reduced; jmodel.py) validated: J=1 reproduces 0.6067069 and J=2
  reproduces 0.62178994 at (0.39646, 1.22663) [4-register-block consistency check identical]. J=2: 191 invariant
  elements (vs 1411 unreduced), 3 s per point. J=3: 746 invariant elements, ~250 s per point (custom IPM).
- J=3 with the J=2 optimum embedded (repeated angle) = 0.62178994 (consistent).
- J=3 at angles (0.2, 0.7, 1.25) rad: 0.6220597 (numerical)  > 0.6219 (best known!) -> exact verification next.

- Envelope-theorem gradient of the J-family value w.r.t. the Jordan angles (feasible set of invariant valid W is
  theta-independent in the bisector basis): dV/dtheta_l = 2 <d u_00/d theta_l | W* | u_00>; checked vs central finite
  differences at J=2 (3.3714e-4 / 8.1110e-4 vs 3.3713e-4 / 8.1109e-4). -> L-BFGS-B angle search (j_grad_search.py).
- jexact.py (general J exact verifier) validated at J=2: PD True, exact value 0.621789944842.

## Step 26 - NEW RECORD LOWER BOUND (exactly verified): I_GYNI >= 0.622059709419
- jexact.py --J 3 at rational angles (bisector basis, tan(t/4) rational): t = (0.19999997, 0.69999864, 1.24999983) rad
  = (11.459, 40.107, 71.620) deg between A_0 and A_1 in the three Jordan blocks; same for Bob; coherent qutrit label.
  Local dims: A_I = C^2 (x) C^3 = 6, A_O = 6 (x) setting register = 12.
- W from the reduced SDP (746 invariant elements; IPM gap 1.5e-9), coefficients rounded to 2^-40, mixed with the
  maximally mixed process with weight 2^-30; all 28 integer sector blocks certified positive definite (Bareiss);
  validity/normalisation exact by construction; value computed exactly from all four register blocks:
      0.622059709419  (> 0.6219, the previous best seesaw value of Boghiu-Simonov, d=6,7).
- Angles were NOT optimised yet (first guess); gradient search running.

## Step 27 - Convergence of the hierarchy: analysis (no proof)
Setting: q* = sup over finite-dim strategies; beta_L (level L) is non-increasing, beta_L >= q*.
(a) Universality of the Jordan family: by Lemma 1 + Jordan's lemma every strategy is, up to absorbing local
    isometries, a J-block Lueders strategy (qubit Jordan blocks, 1-dim blocks = angles 0 or pi/2, coherent label,
    possibly different angle sets for Alice and Bob). Hence q* = sup_J V_J (V_J = J-family optimum): an explicit,
    monotone lower-bound sequence. Numerically V_1 = 0.606707, V_2 >= 0.621790, V_3 >= 0.622060 (and rising).
(b) What the hierarchy sees: the word vectors (1 (x) w)|Phi> are vectorisations of operators in the algebra
    A = alg(O_0, O_1) = (+)_j M_2 (x) |j><j| (Jordan), i.e. they live in the label charge-0 sector span{|jj>}. So
    Gamma = compression of W to vec(A_A) (x) vec(A_B) (x) registers; as L -> oo the words span A and Gamma determines
    this compression completely. The V2 rows are exactly the process-validity identities for trace-proportional maps
    with Kraus operators in A (incl., in the limit, label-dephasing maps, since block projectors are spectral
    projectors of (O_0O_1 + O_1O_0)/2 when angles are distinct).
(c) The possible gap: validity of W also involves maps OUTSIDE A (label-changing Kraus operators |j><k|, qubit maps
    across blocks); these constrain W's off-sector blocks |jk><jk|, which never enter Gamma. Since W is block diagonal
    across sectors (label twirl), PSD is blockwise, and the off-sector blocks are linked to Gamma only through the
    linear trace-and-replace conditions over A_O (Tr_{l_out} maps |jj><jj| and |jk><jk| to |j><j|).
    CONJECTURE (convergence): every Gamma feasible at all levels admits a PSD, valid completion of the off-sector
    blocks (e.g. of product/marginal form); then beta_oo = q*. A proof would need (i) a C*-algebraic GNS step
    (C*(Z2*Z2) = {f in C([0,1],M_2): f(0),f(1) diagonal} turns Gamma into a matrix-valued positive kernel over pairs of
    angles) and (ii) an explicit completion lemma for the off-sector blocks + finite-J approximation (continuous angle
    distributions are limits of finitely many angles).
(d) Numerical evidence: certified gap after this round = beta_8 - V_3(exact) (see below); both sequences move toward
    each other (upper: 0.62222 (L7) -> 0.62221 (L8); lower: 0.62179 (J2) -> 0.62206 (J3)).

- Sparse vectorised IPM (ipm_sparse.py: Schur complement via stacked sparse A_i S^-1 and batched X(.) products;
  stop when gap < tol, dinf < tol, pinf < 1e-6 -- the W side (y, S > 0) is always exactly feasible): J=3 value
  0.6220597094 in 16 s / 18 iterations (1 thread) vs 200+ s for the dense IPM. Dense J=3 search stopped (by PID)
  and restarted with the sparse solver.

## Step 28 - J=3 optimum and LEVEL 8 certificate
- J=3 gradient search (L-BFGS-B, envelope gradients, sparse IPM ~12-20 s per point): converged (|proj grad| 3e-8) to
  V_3 = 0.6221467127 at angles (0.24046235, 0.70224804, 1.44308731) rad = (13.7775, 40.2358, 82.6828) deg.
- certify3 L=8 (IPM dual + 1e-7 I; LSQR residual 2.1e-12): all four 289x289 dual blocks PD (Bareiss, 921 s);
  beta_8 = 700548845513581/2^50 = 0.622212366531.   ==> RIGOROUS: I_GYNI <= 0.6222124.
- Gap (numerical V_3 vs certified beta_8): 6.6e-5.

## Step 29 - NEW RECORD (exact): I_GYNI >= 0.622146712690
- jexact.py --J 3 at rational angles (0.24046226, 0.70224672, 1.44308839) rad = (13.77747, 40.23577, 82.68287) deg:
  SDP gap 5e-10; rounding 2^-40, mixing 2^-49; all 28 integer sector blocks PD (Bareiss); exact value
  0.622146712690.  (j3_exact_opt.pkl)
- CERTIFIED INTERVAL: 0.6221467127 <= I_GYNI <= 0.6222123665  (width 6.57e-5).

## Step 30 - exact identification (PSLQ): not possible, explained
- The value is only bracketed: [0.6221467127, 0.6222123665] (width 6.6e-5). PSLQ needs a point value; the only
  high-precision point we have is V_3 = 0.6221467127 (J=3 optimum, ~10 digits), which need not equal q*.
- pslq_check.py: PSLQ on V_3 against {1, sqrt2, sqrt3, sqrt5, sqrt6} returns a relation with coefficients up to 42 and
  against {1, pi, pi^2} one with coefficients up to 126 -- both are the expected SPURIOUS hits at 1e-9 precision;
  findpoly (degree <= 4, coefficients <= 30): none. 17 simple quadratic surds (a+b*sqrt(c))/d with small integers lie
  inside the certified interval. => No closed form can be identified; none claimed.

## Step 31 - J=4 family
- JModel(4): 1895 invariant elements, 104 cones (max 136), nnz(A) 2.75M; LMI build 69 s; sparse IPM ~7 s/iteration.
- First guess (0.2, 0.55, 0.95, 1.44): 0.6221532877 > V_3 = 0.6221467127  (dual value converged by iteration ~25;
  the X side stalls at pinf 1.7e-7 -> added a dual-stagnation stop: mu < 1e-12 and b.y stable to 1e-11).
- J=4 L-BFGS-B search running.

- Extrapolation of L1..L8 (heuristic): geometric/Aitken 0.622177; the 'linearly increasing ratio' (0.622102) and
  power-law (0.622109) fits now fall BELOW the rigorous lower bound 0.6221467 and are therefore discarded. The
  geometric estimate is consistent with V_J (J = 2, 3, 4: 0.621790, 0.622147, >= 0.622153) approaching ~0.62216-0.62218,
  i.e. with the hierarchy converging to q* (not proven).

- jverify.py (solver-free re-check of saved strategy certificates; also asserts c^2+s^2=1 exactly for the rational
  instruments): j3_exact_opt.pkl -> all sector blocks PD = True, EXACT value 0.622146712690 (83 s).

- verify3.py cert3_L8.pkl (standalone, no solver): all dual blocks PD = True; VERIFIED BOUND = 0.622212366531
  (= 700548845513581/2^50), 930 s.

=====================================================================================================================
# FINAL REPORT v3 (2026-09-28, round 3)  [J=4 numbers appended below when available]
=====================================================================================================================
RIGOROUS UPPER BOUNDS (dimension-free; exact rational duals; standalone solver-free verification verify3.py):
  L=5 0.6224213 | L=6 0.6222568 | L=7 0.6222199 | L=8 0.622212366531 (= 700548845513581 / 2^50, cert3_L8.pkl)
RIGOROUS LOWER BOUNDS (explicit strategies, exact rational verification; jexact.py / jverify.py):
  J=2 Jordan blocks: 0.621789944842 (A_I = C^4)
  J=3 Jordan blocks: 0.622146712690 (A_I = C^6, A_O = C^12)  -- NEW RECORD (previous best 0.6219, Boghiu-Simonov)
     angles between A_0 and A_1 in the three blocks: 13.77747, 40.23577, 82.68287 deg (rational tan(t/4)); same for
     Bob; Lueders instruments + setting register; coherent qutrit label; W real, invariant under the GYNI group.
CERTIFIED INTERVAL: 0.6221467127 <= I_GYNI <= 0.6222123665  (width 6.57e-5; was 0.137 before this program).
Methods added this round: component-wise sparse null space (L=8 cheap: 220 s, 2.6 GB), general-J Jordan-block
  model in the bisector basis with GYNI-group reduction (J=3: 746 parameters), sparse vectorised IPM, envelope-
  theorem gradients for the angle search, exact integer (Bareiss) certificates for strategies.
PSLQ: not meaningful (interval, not a point value); simple surds in the interval are abundant; nothing claimed.
Convergence: not proven; analysis in Step 27 (hierarchy sees only the label-coherent sector; conjectured valid-
  completion lemma would give convergence). Geometric extrapolation of beta_L (0.622177) and the rising V_J
  sequence are consistent with a common limit ~0.62216-0.62218.

## Step 32 - INDEPENDENT FULL-SPACE CHECK of the J=3 record strategy (full_check_J.py)
- Assembled the full 5184 x 5184 process W' (A_I = C^6, A_O = C^12 per party) directly from the saved integer
  coefficients (no symmetry reduction used): real symmetric; generic validity checker (Araujo et al. trace-and-replace
  conditions) c1 = 3.7e-16, c2 = 1.8e-16, c3 = 5.7e-16; min eigenvalue +3.8e-12; Tr W' exact; random real product
  channels give Tr[W'(C_A (x) C_B)] = 1 to 1e-15; GYNI value with the explicit Lueders instruments on the full space
  = 0.622146712690 = the exact value.  => the record strategy is confirmed by a check independent of the
  symmetry-reduced construction (float; the exact certificate is jexact/jverify).

- J=4 search (in progress): 0.6221649691 at (0.16281, 0.62318, 0.92253, 1.47993) rad (3rd evaluation, |g| 9.6e-5).

- jverify.py --full j3_exact_opt.pkl: ALL 196 register x sector blocks (no use of the GYNI-group reduction; only the
  structural block diagonality of the basis) certified PD exactly; EXACT value 0.622146712690. The J=3 record is thus
  certified without relying on the symmetry-reduction argument.
- Exact value computation accelerated (jexact.exact_value: u = uA (x) uB, <u|a(x)b|u> = (uA^T a uA)(uB^T b uB)):
  identical rational value for the J=3 record in 0.1 s.

## Step 33 - J=4 lower bound (exact)
- jexact.py --J 4 at the intermediate search point, rational angles (0.16280597, 0.62318083, 0.92253201, 1.47993235) rad
  = (9.32809, 35.70563, 52.85719, 84.79388) deg: SDP 0.6221649691; rounding 2^-40, mixing 2^-28; all 91 integer
  sector blocks (register (0,0), cA<=cB) certified PD (Bareiss, 594 s); EXACT value 0.622164967795.
  (A_I = C^8, A_O = C^16 per party.)
- CERTIFIED INTERVAL: 0.622164967795 <= I_GYNI <= 0.622212366531  (width 4.74e-5).
- J=4 search continues: best 0.6221658430 at (0.172304, 0.611135, 0.9131, 1.469877), |g| ~ 9e-6.

- J=4 L-BFGS-B search converged: V_4 = 0.6221659018 at (0.16752428, 0.6008269, 0.89334269, 1.4684856) rad
  = (9.59843, 34.42485, 51.18477, 84.13803) deg (|g| 3e-7). jverify.py j4_exact_a.pkl (earlier point) re-check:
  PD True, exact 0.622164967795 (388 s). Exact certificate for the optimum next (j4_exact_opt.pkl).

## Step 34 - STAND-ALONE, SOLVER-FREE EXACT STRATEGY VERIFIER (verify_strategy.py)
Self-contained certificate (.npz, produced by export_strategy_cert.py): explicit integer party operators R_e
(8J^2 x 8J^2, order (q_in,l_in,q_out,l_out,reg)), imaginary counts m_e, pair list, integer coefficients y_t, D, k,
rational instrument parameters (c_j, s_j). verify_strategy.py uses ONLY numpy + fractions and checks exactly:
 (1) Hermiticity type of each R, every pair real;  (2) PROCESS VALIDITY: each R pattern-pure (exact integer partial
 traces), every product pattern (a(x)b and b(x)a) allowed, Tr W = d_AO d_BO;  (3) block diagonality over
 (register, label-charge) classes;  (4) POSITIVITY of EVERY block of 4J^2 D 2^k W (Sylvester/Bareiss, integers; no
 symmetry assumption);  (5) INSTRUMENT VALIDITY (c^2+s^2=1, symmetric projectors summing to 1, Lueders Choi,
 Tr_AO sum_a M_{a|x} = 1);  (6) EXACT VALUE sum_xy 1/4 Tr[W (M_{y|x} (x) M_{x|y})].
- J=3 record: `python verify_strategy.py GYNI_J3_strategy_cert.npz` -> all 6 checks True (196 blocks, 211 s);
  I_GYNI >= 0.622146712690.

- J=4 optimum, jexact.py: rational angles (0.1675254, 0.60082557, 0.89334139, 1.46848625) rad
  = (9.5985, 34.42477, 51.18469, 84.13806) deg; SDP 0.6221659018; rounding 2^-40, mixing 2^-30; 91 reduced blocks PD;
  EXACT value 0.622165901354 (j4_exact_opt.pkl -> GYNI_J4_strategy_cert.npz). Full stand-alone check running.

=====================================================================================================================
# FINAL REPORT v4 (2026-09-28)
=====================================================================================================================
CERTIFIED INTERVAL (exact arithmetic on both sides):
      0.622165901354  <=  I_GYNI  <=  0.622212366531          (width 4.65e-5; previously [0.6219, 0.7592])
UPPER BOUND: level-8 moment hierarchy (dihedral word basis, GYNI symmetry), certificate cert3_L8.pkl,
  beta_8 = 700548845513581 / 2^50 = 0.622212366531.
  Verify (no solver):  cd iqoqi/programs/gyni ; python verify3.py cert3_L8.pkl
  (rebuilds the level-8 rows with mc3.py, recomputes the four 289x289 dual blocks exactly from the rational multipliers,
   Sylvester/Bareiss PD check, prints beta; ~15 min).  Validity of the relaxation: proof in Step 3 (+ Step 15 basis
   change); every row type tested on genuine strategies (d = 2..4) to ~1e-16.
LOWER BOUND: explicit 4-Jordan-block strategy, certificate GYNI_J4_strategy_cert.npz (self-contained).
  Verify (no solver, numpy + fractions only):  cd iqoqi/programs/gyni ; python verify_strategy.py GYNI_J4_strategy_cert.npz
  (exact: process-validity via pattern-pure Hilbert-Schmidt terms + allowed patterns + trace; block structure;
   PD of ALL 676 blocks; instrument validity; exact value).  J=3 record: GYNI_J3_strategy_cert.npz (0.622146712690).
OPTIMAL STRATEGY FOUND (J=4, Alice = Bob):
  H_A = C^2 (Jordan qubit) (x) C^4 (label):  A_I = C^8, A_O = C^8 (x) C^2 (setting register) = C^16.
  Projective measurements: in label block j, P_{0|0} = |phi_j^-><phi_j^-|, P_{0|1} = |phi_j^+><phi_j^+| with
  phi_j^+- = (cos(t_j/2), +-sin(t_j/2)); angles between the two measurement directions
  t = (9.5985, 34.4248, 51.1847, 84.1381) deg (rational tan(t/4)); Lueders instruments writing the setting to the
  output register; real process matrix W (dim 16384) invariant under register/label twirls and the GYNI group,
  coherent across the 4 label values (the label-coherence is essential: one angle only gives 0.6067).
Monotone lower-bound sequence (exact): J=1 0.606707 (numerical), J=2 0.621789945, J=3 0.622146713, J=4 0.622165901.
Upper sequence (certified): L=5 0.6224213, L=6 0.6222568, L=7 0.6222199, L=8 0.6222124.

- `python verify_strategy.py GYNI_J4_strategy_cert.npz` (stand-alone, exact): (1) Hermiticity True, (2) validity True
  (Tr W = 256 = d_AO d_BO), (3) block structure True (26 classes/party), (4) ALL 676 integer blocks PD (2325 s),
  (5) instruments True, (6) exact value 0.622165901354 = stored claim.  RESULT: all checks passed.
  ==> I_GYNI >= 0.622165901354 (rigorous; independent of the SDP and of the symmetry reduction).
FINAL CERTIFIED INTERVAL: 0.622165901354 <= I_GYNI <= 0.622212366531.

