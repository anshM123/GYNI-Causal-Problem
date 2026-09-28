# Referee report (P-AUDIT, hostile referee), 2026-09-28

**Claim audited:** I_GYNI^max <= 0.622212366531 (`publish/GYNI-Causal-Problem`, certificate `src/cert3_L8.pkl`,
verifier `src/verify3.py`). The exact arithmetic of the certificate was taken as given (weak-duality logic
re-derived; exact PD check re-run). The attack targeted the **mathematical validity of the relaxation that is
actually certified**.

## Verdict: SOUND (with presentation gaps; no error affecting the bound)

The certified program is (V1) PSD of the four real register blocks, (V2) the rows of `v2_rows`, and (S) the rows
of `map_rows(fx)`, `map_rows(fy)` and `swap_rows`, with objective `objective(M, gyni_coef())`. This program
contains every quantum strategy, in every finite dimension, with the same objective value. I found no
counterexample, analytically or numerically. The claimed upper bound stands. The written proof needs the
corrections listed below. A corrected, self-contained proof is in `PROOF_DRAFT.md`.

## What is certified (read from the code, not from PROOF.md)
- `verify3.py` rebuilds `mc3.build(8, sym=True)`: 789,678 rows (V2 287,396; fx 167,620; fy 167,620;
  swap 167,042) on 167,620 variables (the upper triangles of four 289x289 real symmetric blocks, one for each
  pair (r_A, r_B)).
- `certify2.verify_exact`: every variable belongs to exactly one block, and Y_k is defined by stationarity. For
  every feasible z this gives o.z = lambda.b - sum_k <Y_k, G_k(z)> <= lambda.b. Rows are integer-valued and the
  objective uses multiples of 1/64, so the rationalisation is exact. Bareiss leading minors > 0 implies PD. (OK.)
- **V3 is not imposed.** PROOF.md Sec. 2 and the README "Method" section still list it (see E1).

## (i) Steps confirmed correct
1. **Lemma 1, step by step.**
   - V_x = sum K_{akx} (x) |a,k,0> is an isometry because sum_a M_{a|x} is trace-preserving.
   - U_x with U_x J = V_x exists: the orthogonal complements of ran J and ran V_x have equal dimension.
   - P_{a|x} are orthogonal projectors summing to 1. T_x is CPTP, and T_{x,e} P_{a|x} J = delta_{aa'} K_{ak'x}, which gives
     M_{a|x} = T_x o L_{a|x} o J(.)J^dagger.
   - T(w) = sum_x T_x(<x|w|x>) is CPTP.
   - At Choi level, Phi_A(C) = sum (J^T (x) T_{x,e} (x) <x|) C (...)^dagger. The **transpose** J^T is correct; J^dagger would
     be wrong for complex J, and negative control N4 detects this.
   - Phi_A is CP and maps channels to channels. W~ = (Phi_A^dagger (x) Phi_B^dagger)(W) is >= 0 and gives 1 on **all product
     CPTP maps** H_A -> H_A (x) X, not only on product states. By the OCB / Araujo et al. characterisation, W~ is
     therefore a valid process, including extensions by ancillas.
   - Phi_A(C_{M~_{a|x}}) = C_{M_{a|x}}, so the statistics are preserved.
   - The register X is on the **output**, and the instrument is exactly M~_{a|x}(rho) = P rho P (x) |x><x|.
   - No dimension mismatch: input H_A, output H_A (x) X, word vectors in H_A (x) H_A (x) X.
2. **V2.** Lemma 2 of the draft: if Tr_{A_O} C_A = lambda_A 1 and Tr_{B_O} C_B = lambda_B 1, then
   Tr[W~ (C_A (x) C_B)] = lambda_A lambda_B, including for non-Hermitian C.
   - Tr_{out} |k'><k| = delta_{rr'} (w^dagger w')^T holds with the unnormalised |Phi> and (F4). The transpose is irrelevant
     because only "= 0" and "= lambda 1" are used.
   - `v2_rows` groups admissible pairs (r = r') by the reduced group element w^{-1} w' in Z2*Z2. `inv` = reversal
     equals both dagger and inverse because O_x is a Hermitian involution. Same-class differences are TA in
     every realisation, because the realisation is a group homomorphism (universal property of the free product).
     The representative ((),0),((),0) is TP.
   - Rows: TA_A x (TA_B + rep_B), rep_A x TA_B, and rep x rep = 1. Every row is of the form TA x (TA or TP) or
     TP x TA; no row uses a relation that holds only in special realisations.
   - The class partition is also invariant under the reversed word convention, so there is no ordering pitfall.
3. **Register structure.** Every absorbed Kraus operator contains <x|_X, so W~ from Lemma 1 is automatically
   block-diagonal in (r_A, r_B). The twirl is harmless but unnecessary. Verified: twirled = raw to the last digit.
4. **Realness.** Re Gamma of a Hermitian PSD Gamma is real, symmetric and PSD. All rows and the objective have real
   coefficients. The symmetric storage is exact for real Gamma. No conjugate strategy is needed.
5. **Symmetry.**
   - fx: Alice letters swapped and her register flipped; Bob O -> -O. fy is the mirror image, and swap exchanges the
     parties. Each is a genuine map on Lueders-form strategies (local relabelling or local unitary on outputs),
     and I_GYNI is invariant (x -> 1-x substitution).
   - Gamma(f.S) equals the signed permutation implemented by `map_rows` / `swap_rows`. fx^2 = fy^2 = sw^2 = id,
     fx fy = fy fx and sw fx sw = fy, so the group is finite and the orbit average is feasible, invariant, and has
     the same objective.
   - Verified numerically from **explicitly transformed strategies**, not from mc3's maps.
6. **Objective.** P_{a|x} = (1 + (-1)^a O_x)/2 lies in the level-1 span. The GYNI coefficients are c[a=y, b=x, x, y] = 1/4.
7. **Certificate link.** From lambda = lam_int/D and my own row matrix: beta = 0.622212366531, and the float min
   eigenvalue of all four Y_k is 2.5e-8 (the margin). For the J=4 strategy, beta - I = sum <Y_k, G_k> = 4.647e-5
   (identity exact to 1e-16).
   - Independent re-run of `verify3.py cert3_L8.pkl`: all dual blocks PD = True, VERIFIED BOUND = 700548845513581/2^50
     (825 s).
   - Independent cvxpy/SCS solve of the certified program: L=1 0.74626285, L=2 0.64348431, L=3 0.62674992,
     reproducing the log values.

## (ii) Gaps (more detail needed; none affects validity)
- **G1.** State the relaxation exactly as certified: index sets, the four blocks, and the exact row families
  (V2a/b/c), the signed-permutation maps (S) and the objective. See PROOF_DRAFT.md Sec. 1.
- **G2.** Lemma 1:
  - write the Kraus operators of T explicitly (T_{x,e} (x) <x|);
  - state the Choi composition rule with the transpose;
  - cite the characterisation "W >= 0 and normalisation on product CPTP maps <=> valid (incl. ancillas)";
  - note that C^{d'} is superfluous (V_x is already an isometry into A_O (x) C^m (x) C^kappa) and that the register
    block-diagonality is automatic.
- **G3.** V2 proof. The step "Tr_B[W~(1 (x) C_B)] = rho (x) 1" needs:
  - the spanning argument (Hermitian and anti-Hermitian parts; the depolarising channel as an interior point);
  - the annihilator argument.
  The realisation independence should be justified by the universal property of Z2*Z2 (group homomorphism
  g_x -> O_x), not only by "free algebra". See draft Lemmas 2 and 3.
- **G4.** Symmetry:
  - give the explicit signed permutations (register flip for fx on Alice; sign (-1)^{|v|} for Bob);
  - verify objective invariance;
  - prove that the strategy-level maps form a finite group, so averaging is legitimate.
  The phrase "automorphisms of the free idempotent algebra" alone does not cover the register permutation or the
  objective.
- **G5.** Realness: replace the conjugate-strategy argument by the one-line Re Gamma argument, or keep both.
- **G6.** Sec. 3: the "triangular change of basis, same value" argument is not needed. The certified program
  should be proved valid directly in the dihedral basis (draft does this).
- **G7.** Scope: finite-dimensional strategies (ancillas and shared entanglement included). Infinite-dimensional
  processes are not covered by Lemma 1 as written.

## (iii) Errors, by severity
- **E1 (medium; documentation, no effect on the bound).**
  - PROOF.md Sec. 2 lists (V3) as a constraint and the Theorem refers to it; README "Method" lists V3.
  - The certified program (`mc3.build`) contains **no V3**.
  - Since dropping constraints can only raise the optimum, the certificate is valid for the program actually
    solved, and V3 must be moved to a remark.
- **E2 (low).** README: "Level 1 reproduces Liu-Chiribella's 0.7592 bound" is false for the certified program.
  Level 1 gives 0.74626 (independently re-solved), i.e. it already improves on LC.
- **E3 (medium; reproducibility).** README: "Validity of each row type ... was also tested ... (test_mc_validity.py,
  errors <= 1e-15)."
  - `test_mc_validity.py` imports `mc_relax`, which is **not shipped** in publish/src (ImportError), and it tests
    the old MC1 relaxation (idempotent words <= 2 plus canonical images), not the certified `mc3` rows.
  - `test_symmetry.py` tests `mc2`/`symmetry.py`, not `mc3.group_maps`.
  - The actual mc3 test (`gyni/test_mc3.py`: L = 2, 3, Lueders-form W only, no swap rows) is not shipped.
  - **No shipped test exercises the certified level-8 row list.** Ship `gyni_audit/audit_*.py` (or equivalent).
- **E4 (typo).** V2 proof: "Tr[tau^T Tr_{A_O} Choi L_A]" should read Tr[tau Tr_{A_O} C_A]. It is harmless because
  Tr_{A_O} C_A is in {0, lambda 1}.

## Independent numerical containment test (own code; mc3 used only to read rows/objective/basis labels)
Checks: (a) every row of `mc3.build(L, sym=True)`, (b) PSD of every block, (c) objective = I_GYNI, for L = 2..8
(L = 8 is the certified level).

| test | #strategies | max V2 residual | max residual of ALL rows on group average | min eig (blocks / full) | abs(obj - I) max |
|---|---|---|---|---|---|
| random general strategies via Lemma 1 (random J, random unitary completion; 3-4 Kraus/outcome; complex boundary W, OCB+LU, OCB mixtures, separable, real, degenerate; unequal dims) | 40 | 6.9e-15 | 5.6e-15 | -2.4e-14 / -7.3e-14 | 5.0e-16 |
| seesaw strategies (I = 0.5694, 0.6046; Kraus rank <= 9, dim H = 54) | 4 | 1.8e-14 | 1.4e-14 | -4.9e-14 / -8.7e-14 | 2.0e-15 |
| published record strategies J=3 (0.622146712690), J=4 (0.6221659013539…; see the README erratum) | 2 | 6.7e-16 (all rows, raw Gamma) | 1.1e-15 | -2.2e-15 / -2.6e-15 | 1.1e-16 |
| generic Lueders-form W~ drawn directly (complex, not register-diagonal; P pairs generic/equal/commuting/0-1/orthogonal; dim H = 1..4) | 60 (+60 in an earlier run with other draws) | 1.25e-14 (earlier run 2.1e-14) | 6.0e-15 (1.1e-14) | -7.8e-13 / -2.0e-12 (relative -9.4e-15) | 1.1e-16 |
| explicit W~ = (Phi_A^dagger (x) Phi_B^dagger)(W), 1024x1024 | 21 | 4.2e-15 (L=3) | - | W~ min eig -8.9e-16; valid-subspace conditions <= 8.4e-17; channel normalisation 1.6e-15 | p: 1.3e-15 |

The most negative eigenvalue relative to ||Gamma|| is -9.4e-15 (generic Lueders-form draws; -8.5e-15 in the level-8
certificate-link test, `tests/logs/cert_link.log`), below n*eps = 2.5e-13, so it is rounding (Gamma is a Gram matrix).
[Coordinator note, 2026-09-28: the two figures were reconciled; previously only -8.5e-15 was quoted here.]

**Negative controls (the test detects errors):**

| perturbation | residual |
|---|---|
| random PSD non-valid W~ | V2 0.72 |
| forbidden term 1e-6 Z on Alice's output register | 8.0e-6 (linear in epsilon) |
| loop term 1e-4 X_AI X_AO | 7.9e-4 |
| fx without register flip | fx rows 4.6e-2 |
| idempotent words fed to the dihedral rows | 0.96 |
| J^dagger instead of J^T | objective off by 1.0e-2 |

## Recommendation
Accept the upper bound after the text is corrected (E1-E4, G1-G7). Replace PROOF.md Secs. 0-2 by
`PROOF_DRAFT.md` (or equivalent), and ship an mc3-level containment test.
