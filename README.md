# The maximal quantum violation of the GYNI causal inequality

**Result.** Two parties may share an arbitrary process matrix: indefinite causal order is allowed, the local Hilbert spaces may have any finite dimension, and any instruments may be used. (Infinite-dimensional strategies are not covered by the proof.) The best success probability for the *Guess Your Neighbour's Input* (GYNI) causal inequality then satisfies

```
            0.622165901353  <=  I_GYNI^max  <=  0.622183755532
```

The window has width **1.79 × 10⁻⁵** (4.65 × 10⁻⁵ before the tightened level-8 certificate of 2026-09-28, see below). Before this work the best known interval was **[0.6219, 0.7592]**, with lower bound 0.6219 from Boghiu & Simonov (arXiv:2606.20519) and upper bound 0.7592 from Liu & Chiribella (arXiv:2403.02749, Nat. Commun. 2025). The exact value of I_GYNI was stated as an open problem in both works and in the 2026 review arXiv:2606.19438.

Both ends of the interval come with exact certificates, checked in pure integer/rational arithmetic without any numerical solver:

| bound | value | certificate | verifier | what is checked |
|---|---|---|---|---|
| upper | 175129158097837 / 2^48 = 0.6221837555310… (so ≤ 0.622183755532) | `src/cert3_L8_e9.pkl` | `src/verify3.py` | exact positive-definiteness (Bareiss/Sylvester) of the dual blocks of level 8 of a new moment hierarchy |
| upper (earlier, superseded) | 700548845513581 / 2^50 = 0.62221236653099… | `src/cert3_L8.pkl` | `src/verify3.py` | same program, larger margin (ε = 10⁻⁷) |
| lower | 0.6221659013539084… (so ≥ 0.622165901353) | `src/GYNI_J4_strategy_cert.npz` | `src/verify_strategy.py` | an explicit process matrix + instruments: validity of the process, exact PD of all 676 blocks, instruments, exact value |

## Erratum (2026-09-28): decimal rounding
The certificates and all exact checks are unchanged: every verifier compares **exact rationals**. But earlier versions of this README printed several decimals rounded *to nearest*, and some of them went in the unsafe direction. Rigorous decimals must round **down for lower bounds** and **up for upper bounds**.
- The J = 4 strategy has exact value **0.6221659013539084…**, so the lower bound is **≥ 0.622165901353**, not "≥ 0.622165901354" as stated before.
- Level 4 and level 6 upper bounds are 0.6233558 and 0.6222569, not 0.6233557 and 0.6222568.
- The J = 3 lower bound, to 9 digits, is 0.622146712, not 0.622146713.
- The J = 2 entry now refers to the shipped certificate.
- The upper bound 0.622212366531 of `cert3_L8.pkl` was, and is, correct: the exact value is 0.62221236653099…. It has since been superseded by the tighter `cert3_L8_e9.pkl` (see the update below).
- The erratum did not change the width of the interval (4.65 × 10⁻⁵ at that time; 1.79 × 10⁻⁵ after the update below).
- The verifiers in `src/` now print directed-rounded decimals. Logs in `logs/` and `tests/logs/` produced before this fix show round-to-nearest values (e.g. "0.622165901354"); the post-fix run is `logs/verify_strategy_J4_directed_rounding.log`.

## Update (2026-09-28): tightened upper bound
The level-8 certificate was re-derived from the same saved numerical solution (`ipm_L8.pkl`, numerical level-8 value 0.6221834652) with a 100× smaller margin, ε = 10⁻⁹ instead of 10⁻⁷. The margin costs exactly ε·289 in the bound, so the certified bound drops from 0.6222124 to **0.6221838**. The program certified is unchanged (V1 + V2 + GYNI symmetry, PROOF.md), and so are the verifier and the proof. Only the rational multipliers differ.
- All four 289 × 289 dual blocks are positive definite: exact Bareiss check, smallest pivot ≈ 2.6 × 10⁻¹⁰.
- The certification run and an independent re-run of `verify3.py` in a separate process are both in `logs/`.

## Setting
- GYNI (Branciard, Araújo, Feix, Costa, Brukner, New J. Phys. 18, 013008 (2016)): inputs x, y ∈ {0,1} uniform. Each party must output the other's input: I_GYNI = ¼ Σ_{x,y} p(a = y, b = x | x, y). Causally ordered strategies reach at most ½.
- Process matrices (Oreshkov, Costa, Brukner, Nat. Commun. 3, 1092 (2012)): p(a,b|x,y) = Tr[W (M_{a|x} ⊗ N_{b|y})], where W ≥ 0 lies in the valid-process subspace with Tr W = d_{A_O} d_{B_O}.

## Method (details in [PROOF.md](PROOF.md))
1. **Lüders normal form.** Without loss of generality every instrument is the Lüders instrument of a projective measurement, with the setting copied into an output register. This holds in every finite dimension; the proof is in PROOF.md, Lemma 1.
2. **Moment hierarchy.** Γ is the Gram matrix of W on word vectors (1 ⊗ w)|Φ⟩ ⊗ |r⟩, where w runs over words in the projectors of length ≤ L. The constraints are:
   - (V1) Γ ⪰ 0;
   - (V2) word-level process validity, with trace functionals evaluated in the free algebra of two idempotents;
   - the GYNI symmetry group.

   **These are exactly the constraints imposed at the certified levels 4–8 (`src/mc3.py`, dihedral word basis).** Levels 2–3 (marked † below) were certified with the earlier idempotent-word formulation (`src/mc2.py` + `symmetry.py`, certificates `cert2_*`), which PROOF.md Remark 2 covers but the audit's containment tests did not; they are not needed for the headline. An additional constraint, (V3), would require the Liu–Chiribella canonical processes to be valid linear images of Γ. It is *not imposed* and no claim about it is needed: adding constraints can only lower the value (PROOF.md, Remark 1). Numerically, a level-2 ablation gave the same value with and without V3; we do not claim a proof that V3 is implied. The validity of the certified bounds therefore rests on V1, V2 and the symmetry reduction only.

   Every quantum strategy, in any finite dimension, gives a feasible Γ, so each level is a rigorous dimension-independent upper bound. Level 1 already gives 0.7463 (numerical), below Liu–Chiribella's 0.7592, which is recovered by the weaker relaxation 'V2 + canonical images' without Γ ⪰ 0. As numerical sanity checks only (no certificates), the same hierarchy with the corresponding objectives reaches the LGYNI value 0.819401 at level 2 and comes within 4 × 10⁻⁷ of the OCB value (2+√2)/4 ≈ 0.8535534 (0.8535530–0.8535532, `src/ocb_check2.py`).
3. **Exact dual certificates.** A numerical dual solution is computed with a margin, projected onto the exact affine constraints, and rounded to rationals with common denominator 2^50. The dual blocks are then *defined* by stationarity, and their positive-definiteness is checked exactly with fraction-free Bareiss elimination.
4. **Explicit lower-bound strategy (J = 4).** Alice = Bob, with H = C² (Jordan qubit) ⊗ C⁴ (label). In label block j the two projective measurements have directions at angle t_j:

   (t_1, …, t_4) = (9.5985°, 34.4248°, 51.1847°, 84.1381°), all with rational tan(t_j/4).

   The instruments are Lüders instruments that write the setting to an output register. W is a real 16384-dimensional process matrix with rational entries. The label coherence is essential: a single Jordan angle gives only 0.6067.

| hierarchy level L | 2† | 3† | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| certified upper bound (rounded up) | 0.6434871 | 0.6267932 | 0.6233558 | 0.6224213 | 0.6222569 | 0.6222199 | **0.6221838** (ε = 10⁻⁹; 0.6222124 with ε = 10⁻⁷) |

† `cert2_L2_sym.pkl`, `cert2_L3_sym.pkl`: earlier idempotent-word formulation (see above). Levels 4–8: `cert3_L4..L8.pkl` (dihedral formulation, the one proved in PROOF.md and audited).

| strategy family | J=1 | J=2 | J=3 | J=4 |
|---|---|---|---|---|
| exact lower bound (rounded down) | 0.606707 (numerical) | 0.621789802 (`j2_exact2.pkl`; a later unshipped run: 0.621789944) | 0.622146712 | **0.622165901** |

## How to verify (no SDP solver needed)
Requirements: Python ≥ 3.10 with `numpy` and `scipy` (see `requirements.txt`). Run the commands from `src/`:
```bash
cd src
python verify_strategy.py GYNI_J4_strategy_cert.npz   # lower bound: overflow guard + all six exact checks, ~40 min (single core)
python verify3.py cert3_L8_e9.pkl                     # upper bound: level-8 dual certificate (margin 1e-9), ~10-15 min
python verify3.py cert3_L8.pkl                        # (optional) the earlier level-8 certificate (margin 1e-7)
python verify3.py cert3_L7.pkl                        # (optional) lower levels: cert3_L4..L7, cert2_L2..L4_sym via verify2.py
```
Expected output (our runs, kept in `logs/`; the lower-bound line is from `logs/verify_strategy_J4_directed_rounding.log`, 1489 s, re-run after the erratum with the directed-rounding verifier):
```
cert3_L8_e9.pkl: dihedral L=8: all dual blocks PD = True; VERIFIED BOUND <= 0.622183755532 (rounded up) (= 175129158097837/281474976710656)
RESULT: all checks passed = True;  I_GYNI >= 0.622165901353 (rounded down)
```
SHA-256 checksums of all certificate files are in `CHECKSUMS.sha256`. The `.pkl` certificates are Python pickles of integer arrays. As with any pickle, load them only after checking the checksums.

To regenerate the certificates (a numerical solver is needed for this step only): `hier_ipm.py` (with `ipm.py`, `ipm_sparse.py`) and `hier3.py` solve the hierarchy, `certify3.py` produces the exact certificate, and `jexact.py` + `export_strategy_cert.py` build the J-strategies (`lueders_J2.py`, `j2_exact_strategy.py`, `j2_exact2.py` for the J = 2 family). The certified level-L rows, up to the full level-8 list of 789,678 rows, are tested on more than 100 random general strategies with independent code in `tests/`. Every residual is at rounding level (≤ 2.1e-14); see `tests/README.md`.

## Status and what a referee should check
- **Lower bound: rigorous and self-contained.** It is an explicit strategy verified in exact arithmetic, and it does not depend on the hierarchy.
- **Internal adversarial audit: verdict SOUND.** See `AUDIT_REPORT.md`. It found no mathematical error affecting the bound. Its documentation fixes (E1–E4) are applied: PROOF.md §§0–2 are now a complete theorem–proof treatment of the certified relaxation, and `tests/` ships the missing level-8 containment test.
- **Upper bound:** the arithmetic is rigorous (exact certificate). The claim relies on the **validity of the hierarchy as a relaxation of the set of finite-dimensional process-matrix strategies**: Lemma 1 (Lüders normal form), Lemma 2 (V2), and the symmetry reduction in PROOF.md. This proof has been checked internally and by an internal adversarial audit (`AUDIT_REPORT.md`, including numerical containment tests on random general strategies), and an informal external review's comments have been addressed. It has **not yet been refereed by a journal**, and it is the key item for review.
- The remaining gap of 1.79 × 10⁻⁵ is open. The numerical level-8 optimum is 0.6221835, so a tighter certificate at level 8 cannot go below that. Higher levels and larger J are the routes to a narrower interval. The hierarchy values decrease monotonically, and our best strategies (J = 1..4) increase monotonically; see `research-log/` for the full record, including negative results and bugs caught.

## Repository layout
- `README.md`: this file. `PROOF.md`: the certified relaxation stated exactly; Lemma 1 (Lüders normal form), Lemma 2 (scalar-trace factorisation) and Lemmas 3–5 with the soundness theorem; the certification method; and the strategy.
- `src/`: all code and certificates (verifiers, hierarchy builders, solvers, strategy generators).
- `logs/`: independent verification runs of both certificates.
- `tests/`: independent containment tests of the certified relaxation, up to the full level-8 row list (see `tests/README.md`).
- `AUDIT_REPORT.md`: the internal adversarial referee report. Verdict: sound; the documentation fixes it asked for are applied.
- `research-log/`: the complete working log (Steps 1–34) and the literature scout report used for the novelty check.
