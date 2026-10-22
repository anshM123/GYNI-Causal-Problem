# The maximal quantum violation of the GYNI causal inequality

**Ansh Mishra and Aryan Senthilkumar**

This repository accompanies the article *Pinning down the maximal quantum violation of the guess-your-neighbour's-input causal inequality*. The manuscript is prepared for Nature Communications.

- Main text: [`manuscript/main.pdf`](manuscript/main.pdf)
- Supplementary Information: [`manuscript/si.pdf`](manuscript/si.pdf)
- Sources are in `manuscript/`.

It contains everything needed to check the result independently: exact certificates, stand-alone verifiers that need no numerical solver, the complete Lean 4 formalisation, containment tests and verification logs.

## Result

Two parties may share an arbitrary process matrix: indefinite causal order is allowed, the local Hilbert spaces may have any finite dimension, and any instruments may be used. The best success probability in the *guess your neighbour's input* (GYNI) causal inequality then satisfies

```
            0.622165901353  <=  I_GYNI^max  <=  0.622183755532
```

- The interval has width **1.79 × 10⁻⁵**.
- The previously known interval was **[0.6219, 0.7592]**:
  - lower bound from Boghiu & Simonov, arXiv:2606.20519;
  - upper bound from Liu & Chiribella, Nat. Commun. 16, 3314 (2025).
- The exact value was stated as open in these works and in the 2026 review arXiv:2606.19438.
- Both ends are **machine-checked in Lean 4 + Mathlib**, for every finite-dimensional strategy, using only Lean's standard axioms.
- Infinite-dimensional strategies are not covered.

## Claims and where they are checked

| Claim in the article | Evidence | How to check |
|---|---|---|
| Lower bound: an explicit J = 4 strategy has I_GYNI = 0.6221659013539084… | `src/GYNI_J4_strategy_cert.npz` (exact rational process and instruments) | `python verify_strategy.py GYNI_J4_strategy_cert.npz` in `src/`: validity, 676 positive-definite blocks, exact value (~40 min, one core) |
| Upper bound: level 8 of the hierarchy is ≤ 175129158097837/2^48 = 0.6221837555310… | `src/cert3_L8_e9.pkl` (exact rational dual certificate) | `python verify3.py cert3_L8_e9.pkl` in `src/`: rebuilds all 789,678 constraints, exact Bareiss positivity of four 289×289 blocks (~10–15 min) |
| Lüders normal form (Lemma 1), factorisation lemma, soundness of the hierarchy (Theorem 2) | `PROOF.md`; Supplementary Note 3 | Read the proofs. They are also machine-checked (next rows). |
| Both bounds, including Lemma 1, the factorisation lemma, the moment-matrix constraints and weak duality | `lean/` | Lean theorems `GYNIProof.gyni_lower_bound_exact`, `GYNIProof.gyni_lower_bound` and `GYNIUpperBound.gyni_upper_bound`; build instructions below; logs in `logs/lean_*.log` |
| Certified values for levels 2–7 (Table 1 of the article) | `src/cert3_L4..L7.pkl`, `src/cert2_L2..L4_sym.pkl` | `python verify3.py cert3_L7.pkl` (or `verify2.py` for the `cert2_*` files) |
| J = 2 and J = 3 strategies (Table 2) | `src/GYNI_J3_strategy_cert.npz`; `src/j2_exact2.pkl` | J = 3: `python verify_strategy.py GYNI_J3_strategy_cert.npz`. J = 2: earlier, symmetry-reduced exact check (Supplementary Note 5). |
| The certified constraints hold for general strategies (numerical, not part of the proof) | `tests/` | See `tests/README.md`: more than 100 random general strategies, residuals ≤ 2.1 × 10⁻¹⁴ |

## How to verify (no SDP solver needed)

Requirements: Python ≥ 3.10 with `numpy` and `scipy` (see `requirements.txt`). Run the commands from `src/`:

```bash
cd src
python verify_strategy.py GYNI_J4_strategy_cert.npz   # lower bound (~40 min, one core)
python verify3.py cert3_L8_e9.pkl                     # upper bound, level 8 (~10-15 min)
```

Expected output (our runs; see `logs/verify_strategy_J4_directed_rounding.log` and `logs/verify_L8_e9.log`):

```
cert3_L8_e9.pkl: dihedral L=8: all dual blocks PD = True; VERIFIED BOUND <= 0.622183755532 (rounded up) (= 175129158097837/281474976710656)
RESULT: all checks passed = True;  I_GYNI >= 0.622165901353 (rounded down)
```

Independent re-runs of both checks are in `logs/independent_verify_J4.log` and `logs/independent_verify_L8.log`.

Two cautions:
- **Checksums.** SHA-256 checksums of all certificate files are in `CHECKSUMS.sha256`. The `.pkl` certificates are Python pickles of integer arrays; as with any pickle, load them only after checking the checksums.
- **Rounding.** All decimals are rounded in the safe direction: lower bounds down, upper bounds up. The verifiers compare exact rationals.

**Regenerating the certificates** needs a numerical solver for this step only:
- `hier_ipm.py` (with `ipm.py` and `ipm_sparse.py`) and `hier3.py` solve the hierarchy;
- `certify3.py` produces the exact certificate;
- `jexact.py` and `export_strategy_cert.py` build the J-strategies.

## Formal verification (Lean 4 + Mathlib)

`lean/` contains two Lake projects.

**Lower bound: `lean/GYNIProof/`.**
- Theorems: `gyni_lower_bound_exact`, `gyni_lower_bound` and `gyni_lower_bound_beats_previous`.
- To build, run `lake exe cache get`, then `bash GYNIProof/check.sh` and `bash GYNIProof/check_big.sh`.
- The data files are generated from the certificate by `GYNIProof/gen_gyni_lean.py`, with `GYNI_NPZ=../src/GYNI_J4_strategy_cert.npz`.

**Upper bound: `lean/GYNIUpper/`.**
- Theorem: `GYNIUpperBound.gyni_upper_bound`. Its proof formalises:
  - the Lüders normal form (Stinespring dilation and an explicit unitary completion);
  - the factorisation lemma;
  - the moment-matrix constraints;
  - weak duality;
  - the symmetry-averaged level-8 certificate, whose positivity is checked by the Lean kernel.
- To build, run `bash GYNIUpper/check_lueders.sh` and then `bash GYNIUpper/check_upper.sh` (about 35 minutes; the GYNIProof core files must be built first).
- The certificate data is regenerated from `src/` with `GYNIUpper/tools/`.

**Notes.**
- The check scripts use `GYNIProof/tools/lean_step.ps1` (Windows PowerShell) to run one Lean process at a time with a memory check. On other systems, run `lake env lean` on the files in the order listed in the scripts.
- All theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no `native_decide`.
- Logs from clean rebuilds are in `logs/lean_*.log`.

## Repository layout

| Path | Contents |
|---|---|
| `manuscript/` | The Nature Communications manuscript: `main.tex` / `main.pdf`, `si.tex` / `si.pdf` (Supplementary Information), `refs.bib`, and `figures/` (all figures are generated by `figures/make_figures.py`). |
| `src/` | Code and certificates: stand-alone verifiers (`verify3.py`, `verify2.py`, `verify_strategy.py`), hierarchy builders and solvers, certificate generators, strategy generators. |
| `lean/` | The Lean 4 formalisation of both bounds. |
| `logs/` | Verification runs of the certificates and of the Lean builds, including independent re-runs. |
| `tests/` | Containment tests of the certified relaxation, up to the full level-8 constraint list (`tests/README.md`). |
| `PROOF.md` | The certified relaxation stated exactly: Lemma 1 (Lüders normal form), Lemma 2 (scalar-trace factorisation), the soundness theorem, the certification method and the strategy. |
| `AUDIT_REPORT.md` | An internal adversarial review of the proof and the code. Verdict: sound; the documentation fixes it asked for are applied. |
| `CHANGELOG.md` | Release history, including the 2026-09-28 note on decimal rounding. |

**Rebuilding the manuscript.** Run `python make_figures.py` in `manuscript/figures/`. Then compile `main.tex` and `si.tex` with any LaTeX distribution, with BibTeX, natbib and the `naturemag` style.

## Status

- **Lower bound.** Self-contained and independent of the hierarchy. It is verified in exact arithmetic and formally in Lean.
- **Upper bound.** It rests on the soundness of the hierarchy (Supplementary Note 3, `PROOF.md`), which is formalised in Lean, and on the level-8 certificate, which is checked in exact arithmetic and by the Lean kernel.
- **Review.** The results have been checked internally, including an adversarial audit and independent re-runs. They have **not yet been peer reviewed**.
- **Open.** The remaining gap of 1.79 × 10⁻⁵, and whether the hierarchy converges to I_GYNI^max.

## Data and code availability

All certificates, numerical solutions, logs, code and the Lean project are in this repository, under the MIT licence. On publication, a release of this repository will be archived on Zenodo with a DOI.

## License and citation

MIT (see `LICENSE`). Copyright (c) 2026 Ansh Mishra and Aryan Senthilkumar. To cite this work, see `CITATION.cff`.
