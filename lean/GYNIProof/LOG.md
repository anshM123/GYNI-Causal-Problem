# P-LEAN-GYNI log: machine-checked lower bound for the GYNI causal inequality

Goal: Lean 4 + Mathlib proof that some valid bipartite process matrix `W` and valid instruments
reach the new GYNI lower bound of `iqoqi/programs/gyni` (certificate `GYNI_J4_strategy_cert.npz`,
stand-alone exact verifier `verify_strategy.py`). Previous best in the literature: `0.6219`.

Toolchain: `leanprover/lean4:v4.33.1`, Mathlib from the existing `.lake` cache (no rebuild, no
`lake update`). No file outside `formal-conjectures/GYNIProof/` is modified.

## Status

@@STATUS@@

## The value (decimal erratum)

The exact value of the certificate is `valNum / valDen = 0.62216590135390844064599665…`
(`valNum`, `valDen`: the 165-digit integers stored in the npz; the generator re-derives the value
with the Lean formulas and checks equality). The 12-digit figure `0.622165901354` of the earlier
reports is this value rounded **up**; `gyniValue ≥ 0.622165901354` is false for this strategy. Lean
proves the exact value and `0.6221659013539 ≤ gyniValue` (floor decimal `0.622165901353`).

## Reproduction

From `formal-conjectures/` (Windows, Git Bash, toolchain in `%USERPROFILE%\.elan\bin`):

    python GYNIProof/gen_gyni_lean.py            # optional: regenerates all data/certificate files
    bash GYNIProof/check.sh     2>&1 | tee GYNIProof/logs/check_conditional.log
    bash GYNIProof/check_big.sh 2>&1 | tee GYNIProof/logs/check_big.log

`check.sh` builds everything except the three `256 × 256` block certificates and proves the
theorems with the hypothesis `BigBlocksPSD`; `check_big.sh` (after `check.sh`) checks the three
big blocks and builds `Main.lean` (unconditional theorems). Each file is elaborated by
`lake env lean`, one process at a time, through `tools/lean_step.ps1`, which first waits (polling
every 60 s) until no other `lean.exe` runs and `Available MBytes ≥ expected peak working set +
1.5 GB`, retries once after 2 minutes if a process dies without a Lean error, and prints wall time,
peak working set and peak private bytes. Then `#print axioms` and a grep for
`sorry/admit/axiom/native_decide`. `python GYNIProof/gen_gyni_lean.py` reproduces all generated
files byte-for-byte (`GYNI_OUT=<dir>` writes them elsewhere; `--skip-compare` skips the 94 s exact
comparison with the certificate's `W`).

## Definitions (`Defs.lean`)

Choi convention of `verify_strategy.py`: `M = ∑_{ij} |i⟩⟨j| ⊗ 𝓜(|i⟩⟨j|)` on `I × O`.
* `ptraceOut M i j = ∑_o M (i,o) (j,o)`; `IsCPTP M := M.PosSemidef ∧ ptraceOut M = 1`.
* `IsProcess W := W.PosSemidef ∧ ∀ M N, IsCPTP M → IsCPTP N → (W * (M ⊗ₖ N)).trace = 1`
  (`W` on `(AI × AO) × (BI × BO)`, arbitrary finite types); `IsValidProcess` is an alias.
* `IsInstrument M := ∀ x, (∀ a, (M x a).PosSemidef) ∧ ptraceOut (∑ a, M x a) = 1`.
* `prob W M N a b x y := ((W * (M x a ⊗ₖ N y b)).trace).re`,
  `gyniValue W M N := ¼ ∑_{x,y} prob W M N y x x y` (i.e. `p(a = y, b = x | x, y)`).

## The strategy

Party space `Pt = Fin 8 × (Fin 8 × Fin 2)` (`A_I = ℂ^8`, index `4q + l`: Jordan qubit `q`, label `l`;
`A_O = ℂ^8 ⊗ ℂ^2` with the setting register), flat index `16 i + 2 o + r` as in the npz.

* Of the certificate's 520 party operators, 15 are "A_I-only" (`R_s = X_s ⊗ 1_{A_O}`, `Tr X_s = 0`),
  and each of the 1895 terms contains one of them. Hence
  `2^71 W = 2^65 1 + (2^30 - 1)(T_A + T_B)`, `T_A((a,b),(a',b')) = [o_a = o_a'] H(i_a,i_a')(b,b')`,
  `T_B` its party swap, with integer `128 × 128` matrices `H(i,i') = ∑_s X_s(i,i') G_s`:
  `H(i,i') = 0` unless `lab i = lab i'`, `∑_i H(i,i) = 0`, `H(i,i')(b,b') = H(i',i)(b',b)`, and `H`
  maps each of the 26 classes (register × label sector) into itself. The generator checks exactly
  that this `W` equals the certificate's `W` on all 676 blocks.
* Lean: `Wc = formW (1/64) HA HA` over `ℚ` cast to `ℂ` (`Structure.lean`, `Model.lean`),
  `HA i i' = κ H(i,i')`, `κ = (2^30 - 1)/2^71`; `H` is read from `Hdat` (14336 integers).
* Instruments (Alice = Bob): `P_{0|x}` label-block-diagonal, `|φ_l^x⟩⟨φ_l^x|`,
  `φ_l^x = (c_l, (-1)^{x+1} s_l)` rational with `c_l² + s_l² = 1`, `P_{1|x} = 1 - P_{0|x}`; Lüders Choi
  `M_{a|x} = |v⟩⟨v|`, `v[(i,(o,r))] = P_{a|x}[o,i] δ_{r,x}` (`Value.lean`).

## Proof structure

| file | content |
|---|---|
| `Defs.lean` | definitions above |
| `Structure.lean` | `formW` (structured process matrices), `trace_formW`, `trace_formW_of_tp` (normalization: `c·|AI|·|BI| = 1`, `∑_i HA i i = 0`, `∑_j HB j j = 0` ⇒ `Tr[W (M⊗N)] = 1` for all trace-preserving `M`, `N`) |
| `IntLit.lean`, `Data.lean`*, `Core.lean` | Mathlib-free: literals, the data `Hdat`, and every function the kernel evaluates (`embN`, `HintF`, `WintF`, `blockA`, `packL`, `packCols`, `rowsOK`, `shapeOK`, `paramsOK`); kernel checks `embN_spec`, `Hdiag_data` (`∑_i H(i,i) = 0`), `Hdat_bound` |
| `BlockPSD.lean` | `posSemidef_of_blocks` (block-diagonal ⇒ PSD from PSD blocks), `posSemidef_of_diagDom`, `posSemidef_of_gram`, the soundness `posSemidef_of_cert` / `posSemidef_of_chk` of the packed-row certificate checks (`eq_zero_of_sum_pow`: uniqueness of balanced base-`X` digits), `packCols_append`, `packCols_flatten` |
| `Model.lean` | classes and the enumeration `ePt`, `Wq`, `Wc`, `Wc_normalized` (normalization, unconditional), `Wc_isHermitian`, `WintF_zero` (block diagonality), `WintF_swap`, `WintF_bound`, `BlockPSD` |
| `CertSmall0..7`*, `CertMid0..15`* | Mathlib-free kernel checks of the certificates of the 300 blocks `4·4` and 48 blocks `16·4` (`cA ≤ cB`) |
| `BlockCerts.lean`* | `cert_cA_cB : BlockPSD cA cB` for those 348 blocks; `BigBlocksPSD`; `blockPSD_le` |
| `PSD.lean` | `Wc_posSemidef hbig`, `Wc_isProcess hbig` (remaining blocks by the party swap) |
| `ValueData`*, `ValueTabs`*, `ValueCore.lean`, `ValueQ.lean` | Mathlib-free: instrument parameters and vectors (`cS`, `sS`, `Pm`, `vvec`, core `Rat`), integer quadratic forms `hInt`, and all kernel checks of the value (written-out sums `sumR8`, `sumR2`, `sum16`) |
| `Value.lean` | instruments `Mq`/`Mc`, `Mc_instrument` (unconditional), exact value `gyniValue_eq` (unconditional); converts `Finset` sums to the written-out ones |
| `LowerBound.lean` | theorems with the hypothesis `BigBlocksPSD` |
| `Big/D_b_q`*, `Big/P_b`*, `CertBigShape_b`*, `CertBigCols_b_q`*, `CertBigComb_b`*, `CertBigRows_b_q`*, `CertBig_b`* | the three `256 × 256` blocks `b ∈ {0_0, 0_13, 13_13}`: data (16 rows per file), bounds/lengths, packed columns per 16-row chunk and their combination (`packCols_flatten`), row identities (16 rows per file), Mathlib assembly |
| `Main.lean` | `bigBlocksPSD` and the unconditional main theorems |
| `Axioms.lean`, `AxiomsMain.lean` | `#print axioms` |

(* generated by `gen_gyni_lean.py`.)

## Certificates (positive semidefiniteness)

* `W` is block diagonal: 26 classes per party ⇒ 676 blocks (4 of size 256, 96 of size 64, 576 of
  size 16). Only `cA ≤ cB` is certified (351 blocks); the others follow from the party-swap symmetry
  (`WintF_swap`, `blkW_psd`). Block `(cA, cB)` of `2^71 W` is the integer matrix `blockA cA cB`.
* Certificate: `c A = L Lᵀ + E` with `L` the rounded (`2^F`) float Cholesky factor of `A - τ 1`
  (`τ = λ_min / 2`), `c = 2^{2F}`, `E` diagonally dominant (`∑_j |E_ij| ≤ 2 E_ii`). `F = 0` for the 348
  small/mid blocks, `F = 20` for the three big blocks (`λ_min(W) ≈ 8.0e-12` there, condition number
  ~1e10; the other blocks have `λ_min ≥ 2.5e-4`). All certificates are re-verified exactly by the
  generator before emission.
* Kernel check with `O(n²)` work per block: row `i` of the identity is the single integer identity
  `pack(c A_i) = ∑_k L_ik PL_k + pack(E_i)`, `pack(v) = ∑_j v_j X^j`, `X = 2^B` (`B ≤ 117`), `PL_k` the
  packed columns of `L` (`packCols`); the entries are recovered because
  `2 (c α + n λ² + ε) < X` (`eq_zero_of_sum_pow`).

## Memory engineering (2026-09-28, 15:10–17:40)

* The first design ran the certificate checks inside files importing Mathlib; `CertBig_0_0.lean`
  reached 9.7 GB private and was stopped. Causes: (1) the Mathlib import alone is ~3.2–3.5 GB working
  set; (2) `embN` built its `Fin` values with `by omega` proofs, which the kernel re-instantiated at
  each of the ~10⁵ evaluations; (3) the column check `packCols X n L = PL` over all 256 rows is
  evaluated lazily by the kernel (a 256-deep chain of `zipWith` thunks; a standalone attempt ran
  >19 min CPU at 1.9 GB and was stopped). Fixes: `embN` uses `fmod n h x = ⟨x % n, Nat.mod_lt x h⟩`
  (closed, tiny proofs); every kernel-heavy check lives in a Mathlib-free file importing only `Core`
  (baseline ~0.4 GB); Mathlib files only apply the soundness lemmas; the value checks moved from
  `Value.lean` (4.95 GB) to `ValueCore`/`ValueQ` with written-out sums (no `Fintype` enumeration in
  the kernel); the big blocks use one file per 16 rows and chunked column packing
  (`packCols X` per chunk, `packCols (X^16)` for the combination, `packCols_flatten`).

## Measured timings and peak memory (from the final logs)

@@TABLE@@
