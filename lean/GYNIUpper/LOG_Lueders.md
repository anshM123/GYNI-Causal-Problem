# Lüders normal form (Lemma 1 of the GYNI upper-bound proof): Lean log

Goal: a machine-checked proof of Lemma 1, "Lüders normal form with setting registers", of
`publish/GYNI-Causal-Problem/PROOF.md` (Section 2; supplement `iqoqi/manuscripts/GYNI/supplement.tex`,
Section S3, Lemma `lem:S-lueders`). The statement reuses the definitions of `GYNIProof/Defs.lean`
(`ptraceOut`, `IsCPTP`, `IsProcess`, `IsInstrument`, `prob`, `gyniValue`), so that it plugs into the
rest of the upper-bound formalisation.

Toolchain: Lean `v4.33.1`, Mathlib from the existing `.lake` (no rebuild, no `lake update`).
Files: `GYNIUpper/Lueders*.lean`, `GYNIUpper/AxiomsLueders.lean`, `GYNIUpper/check_lueders.sh`,
`GYNIUpper/lueders_step.ps1`, `GYNIUpper/logs_lueders/`. Nothing outside `GYNIUpper/` is modified,
and the other files in `GYNIUpper/` are not touched.

## Status

Complete. All four files compile with exit code 0 and without warnings; no `sorry`, `admit`, new
`axiom` or `native_decide`. `#print axioms` (`AxiomsLueders.lean`, run of 2026-09-29 00:59):

    'GYNIUpper.lueders_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound]
    'GYNIUpper.lueders_normal_form_choi' depends on axioms: [propext, Classical.choice, Quot.sound]
    'GYNIUpper.luedersProcess_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
    'GYNIUpper.isInstrument_luedersInstr' depends on axioms: [propext, Classical.choice, Quot.sound]
    'GYNIUpper.luedersInstr_eq_choiMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
    CStarMatrix constants: []

## Main statements (`GYNIUpper/LuedersNormalForm.lean`, namespace `GYNIUpper`)

Variables: `{AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
[DecidableEq AI] [DecidableEq BI]` (no `DecidableEq` is needed on the output spaces).

```lean
theorem lueders_normal_form
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :
    ∃ (nA nB : ℕ) (P : Fin 2 → Fin 2 → Matrix (Fin nA) (Fin nA) ℂ)
      (Q : Fin 2 → Fin 2 → Matrix (Fin nB) (Fin nB) ℂ)
      (W' : Matrix ((Fin nA × (Fin nA × Fin 2)) × (Fin nB × (Fin nB × Fin 2)))
        ((Fin nA × (Fin nA × Fin 2)) × (Fin nB × (Fin nB × Fin 2))) ℂ),
      IsProjFamily P ∧ IsProjFamily Q ∧ IsProcess W' ∧
      (∀ p q, (p.1.2.2 ≠ q.1.2.2 ∨ p.2.2.2 ≠ q.2.2.2) → W' p q = 0) ∧
      (∀ a b x y, (W' * (luedersInstr P x a ⊗ₖ luedersInstr Q y b)).trace =
        (W * (M x a ⊗ₖ N y b)).trace) ∧
      (∀ a b x y, prob W' (luedersInstr P) (luedersInstr Q) a b x y = prob W M N a b x y) ∧
      gyniValue W' (luedersInstr P) (luedersInstr Q) = gyniValue W M N

theorem lueders_normal_form_choi
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :
    ∃ (nA nB : ℕ) (P : Fin 2 → Fin 2 → Matrix (Fin nA) (Fin nA) ℂ)
      (Q : Fin 2 → Fin 2 → Matrix (Fin nB) (Fin nB) ℂ)
      (W' : Matrix ((Fin nA × (Fin nA × Fin 2)) × (Fin nB × (Fin nB × Fin 2)))
        ((Fin nA × (Fin nA × Fin 2)) × (Fin nB × (Fin nB × Fin 2))) ℂ),
      IsProjFamily P ∧ IsProjFamily Q ∧ IsProcess W' ∧
      W' = ∑ r, ∑ s,
        registerProj (Fin nA) (Fin nB) r s * W' * registerProj (Fin nA) (Fin nB) r s ∧
      ∀ a b x y, prob W'
          (fun x' a' => choiMatrix fun ρ : Matrix (Fin nA) (Fin nA) ℂ =>
            (P x' a' * ρ * P x' a') ⊗ₖ (Matrix.single x' x' 1 : Matrix (Fin 2) (Fin 2) ℂ))
          (fun y' b' => choiMatrix fun σ : Matrix (Fin nB) (Fin nB) ℂ =>
            (Q y' b' * σ * Q y' b') ⊗ₖ (Matrix.single y' y' 1 : Matrix (Fin 2) (Fin 2) ℂ))
          a b x y = prob W M N a b x y
```

`H_A = ℂ^nA`, `H_B = ℂ^nB`; the process `W'` lives on `H_A ⊗ (H_A ⊗ X) ⊗ H_B ⊗ (H_B ⊗ Y)`,
`X = Y = ℂ²`, in the index order of `IsProcess` (`(AI' × AO') × (BI' × BO')` with `AI' = Fin nA`,
`AO' = Fin nA × Fin 2`). The second theorem writes the Lüders Choi matrices out as
`C_{ρ ↦ P_{a|x} ρ P_{a|x} ⊗ |x⟩⟨x|}` and states block diagonality in the projector form of the paper,
`W' = ∑_{r,s} Π_{rs} W' Π_{rs}`.

Further results: `isInstrument_luedersInstr` (`IsProjFamily P → IsInstrument (luedersInstr P)`),
`luedersInstr_eq_choiMatrix`, and `luedersProcess_spec` (the explicit `W'` for given dilations).

## New definitions

| name | file | meaning |
|---|---|---|
| `krausChoi K` | LuedersChoi | `K o i * conj (K o' j)` at `((i,o),(j,o'))`: Choi matrix of `ρ ↦ K ρ Kᴴ` (`krausChoi_eq_choiMatrix`) |
| `choiMatrix F` | LuedersChoi | `F (single i j 1) o o'` at `((i,o),(j,o'))`: `C_F = ∑ |i⟩⟨j| ⊗ F(|i⟩⟨j|)`, convention of `GYNIProof.Defs` |
| `luedersKraus P x` | LuedersChoi | `P ⊗ |x⟩ : ℂ^H → ℂ^H ⊗ ℂ²` |
| `luedersInstr P x a` | LuedersChoi | `krausChoi (luedersKraus (P x a) x)`, the Lüders Choi matrix; entries in `luedersInstr_apply` |
| `IsProjFamily P` | LuedersChoi | `∀ x, (∀ a, IsStarProjection (P x a)) ∧ ∑ a, P x a = 1` (Mathlib `IsStarProjection`: idempotent and self-adjoint) |
| `choiMap A B C` | LuedersChoi | `∑ k, (Aᵀ ⊗ B k) C (Aᵀ ⊗ B k)ᴴ`, Choi-level form of `F ↦ 𝓑 ∘ F ∘ 𝓐` (fact (F3)) |
| `regKraus T` | LuedersChoi | Kraus operators `T x k ⊗ ⟨x|` of a register-controlled post-processing |
| `IsLuedersDilation M J P T` | LuedersDilation | `Jᴴ J = 1`, `IsProjFamily P`, `∑ k (T x k)ᴴ T x k = 1`, `∑ k C_{T x k · P x a · J} = M x a` |
| `DilSpace`, `stine`, `dilU`, `dilJ`, `dilD`, `dilP`, `dilSel`, `dilT` | LuedersDilation | the construction below |
| `liftProcess W XA XB` | LuedersNormalForm | `∑_{i,j} (XA i ⊗ XB j)ᴴ W (XA i ⊗ XB j)` |
| `luedersProcess W JA TA JB TB` | LuedersNormalForm | `W' = (Φ_A† ⊗ Φ_B†)(W)`, Kraus operators `JAᵀ ⊗ TA x k ⊗ ⟨x|` |
| `registerProj HA HB r s` | LuedersNormalForm | the diagonal projector `Π_{rs}` onto the register values `(r, s)` |

## Proof structure

| file | content |
|---|---|
| `LuedersChoi.lean` | definitions above; `krausChoi_posSemidef`, `ptraceOut_krausChoi` (`Tr_O C_K = (Kᴴ K)ᵀ`), `choiMap_krausChoi` ((F3) for Kraus maps), `ptraceOut_choiMap` (`Tr_{O'} choiMap A B C = Aᵀ (Tr_O C) (Aᵀ)ᴴ` if `∑ Bᴴ B = 1`, proved by trace duality `Matrix.ext_iff_trace_mul_left` and `trace_kron_one_mul`), `isCPTP_choiMap`, `regKraus_mul_luedersKraus`, `sum_regKraus`, `isInstrument_luedersInstr`, `luedersInstr_eq_choiMatrix` |
| `LuedersDilation.lean` | `exists_kraus` (Kraus operators indexed by `I × O` from `M = Bᴴ B`, `CStarAlgebra.nonneg_iff_eq_star_mul_self`); the construction; `isLuedersDilation_construction`; `IsLuedersDilation.reindex` (transport along `H ≃ H'`); `exists_luedersDilation_fin` |
| `LuedersNormalForm.lean` | `trace_liftProcess_mul` (duality `Tr[W' (C ⊗ D)] = Tr[W (Φ_A C ⊗ Φ_B D)]`), `posSemidef_liftProcess`, `liftProcess_apply_eq_zero` (block structure), `choiMap_luedersInstr` (`Φ_A (C_{M~_{a|x}}) = M x a`), `luedersProcess_spec`, `nonempty_of_isProcess`, `lueders_normal_form`, `eq_sum_registerProj`, `lueders_normal_form_choi` |
| `AxiomsLueders.lean` | `#print axioms`; a meta check that the statements (and the definitions they use) contain no `CStarMatrix` constant |

## The construction (one party; `I = A_I`, `O = A_O`)

1. Kraus operators: `M x a = Bᴴ B` with `B : Matrix (I × O) (I × O) ℂ`; `K x a k o i = conj (B k (i, o))`,
   `k ∈ κ = I × O`. Trace preservation gives `∑_{a,k} (K x a k)ᴴ K x a k = 1`.
2. Stinespring isometry `V x = ∑_{a,k} K x a k ⊗ |a,k⟩ : ℂ^I → ℂ^O ⊗ ℂ² ⊗ ℂ^κ` (`stine`), `Vᴴ V = 1`.
3. Unitary completion without orthonormal-basis extension: on `H = (O × (Fin 2 × κ)) ⊕ I`
   (`DilSpace`) the block matrix `U x = [[1 - V Vᴴ, V], [Vᴴ, 0]]` (`dilU`) is self-adjoint and
   unitary (`fromBlocks_isometry_mul_self`), and with the inclusion `J = [[0], [1]] : ℂ^I → ℂ^H`
   (`dilJ`, independent of `x`) one has `U x J = [[V x], [0]]`.
4. `P x a = U x D a U x` (`dilP`), `D a` the diagonal projector onto the summand `O ⊗ |a⟩ ⊗ ℂ^κ`;
   the summand `I` is attached to outcome `0`, so `∑_a D a = 1`.
5. Post-processing `T x k = S k U x` (`dilT`) with `S (inl e) = (1_O ⊗ ⟨e|) ∘ (projection on the
   first summand)` and `S (inr i) = |o₀⟩⟨i| ∘ (projection on the second summand)`; `∑_k Sᴴ S = 1`,
   hence `∑_k (T x k)ᴴ T x k = 1`. Then `T x (inl (a', k)) P x a J = [a' = a] K x a k` and
   `T x (inr i) P x a J = 0`, which gives `∑_k C_{T x k P x a J} = M x a`.
6. `o₀ ∈ A_O` exists because `Tr[W (∑_a M 0 a ⊗ ∑_b N 0 b)] = 1` forces the index type to be
   nonempty (`nonempty_of_isProcess`).
7. Transport to `H = Fin n` with `Fintype.equivFin` (`IsLuedersDilation.reindex`), so the final
   statement has no universe bookkeeping.

The two parties are combined by `W' = ∑ (K̂_{x,e} ⊗ K̂'_{y,f})ᴴ W (K̂_{x,e} ⊗ K̂'_{y,f})` with
`K̂_{x,e} = Jᵀ ⊗ T_{x,e} ⊗ ⟨x|` (`luedersProcess`). As in the paper, the pre-processing acts on Choi
matrices through the transpose `Jᵀ` (`choiMap`); here `J` is a real 0/1 matrix, and the proof uses
`Jᵀ` throughout.

## Design notes

* Only standard Mathlib notions are used in the statement: `Matrix`, `Matrix.single`, `⊗ₖ`,
  `IsStarProjection`, and the `GYNIProof` definitions.
* The unitary completion of the paper ("extend `V_x J†` to a unitary") is replaced by the explicit
  block unitary of step 3; this adds the summand `I` to `H_A`, which the post-processing maps to
  `|o₀⟩`. `H_A` has dimension `|A_O| · 2 · |A_I| · |A_O| + |A_I|`.
* Pitfall found on the way: importing all of Mathlib makes the `CStarMatrix` multiplication a
  default instance of `HMul` (priority 100). When an operand of a product has a type with
  metavariables at elaboration time (e.g. `dilSel o₀ (Sum.inl (a', k))` with the second summand
  not yet known), Lean falls back to this default instance, and `Matrix.mul_apply` no longer
  applies. Fix: type ascriptions so that every operand type is known; `AxiomsLueders.lean` checks
  that no `CStarMatrix` constant occurs in the final statements or in the definitions they use.

## Compile times and peak memory (final run, 2026-09-29 00:57-01:00, `check_lueders.sh`)

| file | wall | peak working set | peak private bytes |
|---|---|---|---|
| `LuedersChoi.lean` | 34.8 s | 3,476 MB | 8,009 MB |
| `LuedersDilation.lean` | 35.9 s | 3,504 MB | 8,028 MB |
| `LuedersNormalForm.lean` | 33.4 s | 3,471 MB | 8,011 MB |
| `AxiomsLueders.lean` | 29.3 s | 3,212 MB | 7,949 MB |
| total `check_lueders.sh` | 141 s | | |

About 25 s of each run is the import of Mathlib. One intermediate version of `LuedersChoi.lean`
took 251 s (an 8-case `fin_cases`/`simp` proof of an entrywise identity); it was replaced by a
direct proof (`mul_single_mul_apply`).

## Reproduction

From `formal-conjectures/` (Windows, Git Bash, Lean toolchain in `%USERPROFILE%\.elan\bin`):

    bash GYNIUpper/check_lueders.sh 2>&1 | tee GYNIUpper/logs_lueders/check_lueders.log

The script compiles, one `lake env lean` process at a time,

    lake env lean -o .lake/build/lib/lean/GYNIUpper/LuedersChoi.olean -i .lake/build/lib/lean/GYNIUpper/LuedersChoi.ilean GYNIUpper/LuedersChoi.lean
    lake env lean -o .lake/build/lib/lean/GYNIUpper/LuedersDilation.olean -i .lake/build/lib/lean/GYNIUpper/LuedersDilation.ilean GYNIUpper/LuedersDilation.lean
    lake env lean -o .lake/build/lib/lean/GYNIUpper/LuedersNormalForm.olean -i .lake/build/lib/lean/GYNIUpper/LuedersNormalForm.ilean GYNIUpper/LuedersNormalForm.lean
    lake env lean GYNIUpper/AxiomsLueders.lean

(prerequisite: `.lake/build/lib/lean/GYNIProof/Defs.olean`, present). Before each process,
`GYNIUpper/lueders_step.ps1` (a copy of `GYNIProof/tools/lean_step.ps1` that reads the output as
UTF-8) waits, polling every 60 s, until no other `lean.exe` runs and `Available MBytes ≥` expected
peak working set + 1500 MB; it reports wall time and peak memory and retries once if a process
dies without a Lean error. Then the script greps for `sorry`, `admit`, `axiom`, `native_decide`.

## History

* API checks first (`IsStarProjection`, `CStarAlgebra.nonneg_iff_eq_star_mul_self`,
  `fromBlocks_multiply`, `Matrix.ext_iff_trace_mul_left`, ...), then `LuedersChoi.lean`
  (compiled after one round of fixes).
* `LuedersDilation.lean`: issues fixed on the way were numerals `0` in heterogeneous products
  defaulting to `ℕ`, implicit type arguments of `dilJ`/`dilDiag` that could not be inferred (now
  explicit), and the `CStarMatrix` default-instance pitfall above.
* `LuedersNormalForm.lean` compiled at the first attempt.
* Last additions: the `choiMatrix` form of the Lüders instruments, the projector form of block
  diagonality, the complex trace equality in the main statement, and removal of `DecidableEq` on
  the output spaces from the main statements; then the final run of `check_lueders.sh` (all exit 0).
