import GYNIProof.Defs

/-!
# Lüders normal form, part 1: Choi matrices of Kraus maps and Choi-level channels

Choi convention of `GYNIProof.Defs`: a linear map `𝓜 : L(ℂ^I) → L(ℂ^O)` is represented by the
matrix `M (i, o) (j, o') = ⟨o| 𝓜(|i⟩⟨j|) |o'⟩` on `I × O`.

* `choiMatrix F = ∑_{i,j} |i⟩⟨j| ⊗ F(|i⟩⟨j|)`: the Choi matrix of a map `F`.
* `krausChoi K`: the Choi matrix of `ρ ↦ K ρ Kᴴ` (`K : ℂ^I → ℂ^O`; `krausChoi_eq_choiMatrix`).
* `luedersKraus P x = P ⊗ |x⟩` and `luedersInstr P x a`: the Choi matrix of the Lüders
  instrument with setting register, `ρ ↦ P_{a|x} ρ P_{a|x} ⊗ |x⟩⟨x|`
  (`luedersInstr_eq_choiMatrix`).
* `IsProjFamily P`: for every setting `x` the `P x a` are orthogonal projectors with sum `1`.
* `choiMap A B C = ∑ k, (Aᵀ ⊗ B k) C (Aᵀ ⊗ B k)ᴴ`: the Choi-level form of `F ↦ 𝓑 ∘ F ∘ 𝓐` with
  `𝓐 ρ = A ρ Aᴴ` and `𝓑 ω = ∑ k, B k ω (B k)ᴴ` (fact (F3) of `PROOF.md`; the pre-processing acts
  through the transpose `Aᵀ`).
* `regKraus T`: the Kraus operators `T x k ⊗ ⟨x|` of a post-processing that reads the setting
  register.

Main results: `choiMap_krausChoi` ((F3) for Kraus maps), `ptraceOut_choiMap`, `isCPTP_choiMap`
(an isometric pre-processing and a trace-preserving post-processing map CPTP Choi matrices to CPTP
Choi matrices), `regKraus_mul_luedersKraus`, `sum_regKraus`, `isInstrument_luedersInstr`,
`luedersInstr_eq_choiMatrix`.
-/

set_option linter.unusedSectionVars false

namespace GYNIUpper

open Matrix GYNIProof
open scoped ComplexOrder Kronecker

section Defs

variable {I O H I' O' κ : Type*}

/-- Choi matrix of the completely positive map `ρ ↦ K ρ Kᴴ` for `K : ℂ^I → ℂ^O`:
`krausChoi K (i, o) (j, o') = K o i * conj (K o' j)`. -/
def krausChoi (K : Matrix O I ℂ) : Matrix (I × O) (I × O) ℂ :=
  Matrix.of fun p q => K p.2 p.1 * star (K q.2 q.1)

/-- The Choi matrix `C_F = ∑_{i,j} |i⟩⟨j| ⊗ F(|i⟩⟨j|)` of a map `F : L(ℂ^I) → L(ℂ^O)`, in the
convention of `GYNIProof.Defs`: `choiMatrix F (i, o) (j, o') = ⟨o| F(|i⟩⟨j|) |o'⟩`. -/
def choiMatrix [DecidableEq I] (F : Matrix I I ℂ → Matrix O O ℂ) : Matrix (I × O) (I × O) ℂ :=
  Matrix.of fun p q => F (Matrix.single p.1 q.1 1) p.2 q.2

/-- The operator `P ⊗ |x⟩ : ℂ^H → ℂ^H ⊗ ℂ²` (the setting register is prepared in `|x⟩`). -/
def luedersKraus (P : Matrix H H ℂ) (x : Fin 2) : Matrix (H × Fin 2) H ℂ :=
  Matrix.of fun p h => if p.2 = x then P p.1 h else 0

/-- Choi matrices of the Lüders instruments with setting register: `luedersInstr P x a` is the
Choi matrix, on `H × (H × Fin 2)`, of `ρ ↦ P x a * ρ * (P x a)ᴴ ⊗ |x⟩⟨x|`. -/
def luedersInstr (P : Fin 2 → Fin 2 → Matrix H H ℂ) :
    Fin 2 → Fin 2 → Matrix (H × (H × Fin 2)) (H × (H × Fin 2)) ℂ :=
  fun x a => krausChoi (luedersKraus (P x a) x)

/-- For every setting `x`, the matrices `P x a` are orthogonal projectors (`IsStarProjection`:
`P x a * P x a = P x a` and `(P x a)ᴴ = P x a`) with `∑ a, P x a = 1`. -/
def IsProjFamily [Fintype H] [DecidableEq H] (P : Fin 2 → Fin 2 → Matrix H H ℂ) : Prop :=
  ∀ x, (∀ a, IsStarProjection (P x a)) ∧ ∑ a, P x a = 1

/-- Choi-level form of `F ↦ 𝓑 ∘ F ∘ 𝓐`, where `𝓐 ρ = A ρ Aᴴ` (`A : ℂ^I' → ℂ^I`) and
`𝓑 ω = ∑ k, B k ω (B k)ᴴ` (`B k : ℂ^O → ℂ^O'`): `choiMap A B C = ∑ k, (Aᵀ ⊗ B k) C (Aᵀ ⊗ B k)ᴴ`. -/
def choiMap [Fintype I] [Fintype O] [Fintype κ] (A : Matrix I I' ℂ) (B : κ → Matrix O' O ℂ)
    (C : Matrix (I × O) (I × O) ℂ) : Matrix (I' × O') (I' × O') ℂ :=
  ∑ k, (Aᵀ ⊗ₖ B k) * C * (Aᵀ ⊗ₖ B k)ᴴ

/-- The Kraus operators `T x k ⊗ ⟨x| : ℂ^H ⊗ ℂ² → ℂ^O`, indexed by `(x, k)`, of a post-processing
controlled by the setting register. -/
def regKraus (T : Fin 2 → κ → Matrix O H ℂ) : Fin 2 × κ → Matrix O (H × Fin 2) ℂ :=
  fun j => Matrix.of fun o p => if p.2 = j.1 then T j.1 j.2 o p.1 else 0

/-- The column vector `(i, o) ↦ K o i`, i.e. `(1 ⊗ K)|Φ⟩` with `|Φ⟩ = ∑ i, |i⟩|i⟩`. -/
def kvec (K : Matrix O I ℂ) : Matrix (I × O) Unit ℂ :=
  Matrix.of fun p _ => K p.2 p.1

lemma krausChoi_apply (K : Matrix O I ℂ) (p q : I × O) :
    krausChoi K p q = K p.2 p.1 * star (K q.2 q.1) := rfl

lemma krausChoi_zero : krausChoi (0 : Matrix O I ℂ) = 0 := by
  ext p q; simp [krausChoi]

/-- Entries of the Lüders Choi matrices. -/
lemma luedersInstr_apply (P : Fin 2 → Fin 2 → Matrix H H ℂ) (x a : Fin 2) (h h' g g' : H)
    (r r' : Fin 2) :
    luedersInstr P x a (h, (h', r)) (g, (g', r')) =
      if r = x ∧ r' = x then P x a h' h * star (P x a g' g) else 0 := by
  by_cases hr : r = x <;> by_cases hr' : r' = x <;>
    simp [luedersInstr, krausChoi, luedersKraus, hr, hr']

lemma regKraus_apply (T : Fin 2 → κ → Matrix O H ℂ) (x : Fin 2) (k : κ) (o : O) (h : H)
    (r : Fin 2) : regKraus T (x, k) o (h, r) = if r = x then T x k o h else 0 := rfl

end Defs

section Lemmas

variable {I O H I' O' κ : Type*} [Fintype I] [Fintype O] [Fintype H] [Fintype I'] [Fintype O']
  [Fintype κ]

lemma krausChoi_eq (K : Matrix O I ℂ) : krausChoi K = kvec K * (kvec K)ᴴ := by
  ext p q
  simp [krausChoi, kvec, Matrix.mul_apply]

lemma krausChoi_posSemidef (K : Matrix O I ℂ) : (krausChoi K).PosSemidef := by
  rw [krausChoi_eq]
  exact posSemidef_self_mul_conjTranspose _

lemma ptraceOut_add (C D : Matrix (I × O) (I × O) ℂ) :
    ptraceOut (C + D) = ptraceOut C + ptraceOut D := by
  ext i j
  simp [ptraceOut, Finset.sum_add_distrib]

lemma ptraceOut_sum {ι : Type*} (s : Finset ι) (C : ι → Matrix (I × O) (I × O) ℂ) :
    ptraceOut (∑ k ∈ s, C k) = ∑ k ∈ s, ptraceOut (C k) := by
  ext i j
  simp only [ptraceOut, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

lemma ptraceOut_krausChoi (K : Matrix O I ℂ) : ptraceOut (krausChoi K) = (Kᴴ * K)ᵀ := by
  ext i j
  simp only [ptraceOut, krausChoi, Matrix.of_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- `Tr[(R ⊗ 1) C] = Tr[R Tr_O C]`. -/
lemma trace_kron_one_mul [DecidableEq O] (R : Matrix I I ℂ) (C : Matrix (I × O) (I × O) ℂ) :
    ((R ⊗ₖ (1 : Matrix O O ℂ)) * C).trace = (R * ptraceOut C).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, ptraceOut, Matrix.of_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma kronecker_sum_right {ι : Type*} (s : Finset ι) (A : Matrix I I' ℂ)
    (B : ι → Matrix O O' ℂ) : A ⊗ₖ (∑ k ∈ s, B k) = ∑ k ∈ s, A ⊗ₖ B k := by
  ext ⟨i, o⟩ ⟨j, p⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

lemma kronecker_sum_left {ι : Type*} (s : Finset ι) (A : ι → Matrix I I' ℂ)
    (B : Matrix O O' ℂ) : (∑ k ∈ s, A k) ⊗ₖ B = ∑ k ∈ s, A k ⊗ₖ B := by
  ext ⟨i, o⟩ ⟨j, p⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

/-- `Tr[Y (X C Xᴴ)] = Tr[(Xᴴ Y X) C]`. -/
lemma trace_mul_sandwich {m n : Type*} [Fintype m] [Fintype n] (Y : Matrix m m ℂ)
    (X : Matrix m n ℂ) (C : Matrix n n ℂ) :
    (Y * (X * C * Xᴴ)).trace = (Xᴴ * Y * X * C).trace := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma kron_mul_kvec (A : Matrix I I' ℂ) (B : Matrix O' O ℂ) (K : Matrix O I ℂ) :
    (Aᵀ ⊗ₖ B) * kvec K = kvec (B * K * A) := by
  ext ⟨i', o'⟩ u
  simp only [kvec, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Fact (F3) for Kraus maps: `choiMap A B (C_{K · Kᴴ}) = ∑ k, C_{(B k K A) · (B k K A)ᴴ}`. -/
lemma choiMap_krausChoi (A : Matrix I I' ℂ) (B : κ → Matrix O' O ℂ) (K : Matrix O I ℂ) :
    choiMap A B (krausChoi K) = ∑ k, krausChoi (B k * K * A) := by
  unfold choiMap
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [krausChoi_eq, krausChoi_eq, ← kron_mul_kvec, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma choiMap_posSemidef (A : Matrix I I' ℂ) (B : κ → Matrix O' O ℂ)
    {C : Matrix (I × O) (I × O) ℂ} (hC : C.PosSemidef) : (choiMap A B C).PosSemidef :=
  posSemidef_sum _ fun _ _ => hC.mul_mul_conjTranspose_same _

/-- Partial trace of the Choi-level map: `Tr_{O'} (choiMap A B C) = Aᵀ (Tr_O C) (Aᵀ)ᴴ` when
`∑ k, (B k)ᴴ B k = 1`. -/
lemma ptraceOut_choiMap [DecidableEq O] [DecidableEq O'] (A : Matrix I I' ℂ)
    (B : κ → Matrix O' O ℂ) (hB : ∑ k, (B k)ᴴ * B k = 1) (C : Matrix (I × O) (I × O) ℂ) :
    ptraceOut (choiMap A B C) = Aᵀ * ptraceOut C * (Aᵀ)ᴴ := by
  rw [Matrix.ext_iff_trace_mul_left]
  intro R
  have hsum : ∑ k, (Aᵀ ⊗ₖ B k)ᴴ * (R ⊗ₖ (1 : Matrix O' O' ℂ)) * (Aᵀ ⊗ₖ B k) =
      ((Aᵀ)ᴴ * R * Aᵀ) ⊗ₖ (1 : Matrix O O ℂ) := by
    simp_rw [conjTranspose_kronecker, ← mul_kronecker_mul, Matrix.mul_one]
    rw [← kronecker_sum_right, hB]
  calc (R * ptraceOut (choiMap A B C)).trace
      = ((R ⊗ₖ (1 : Matrix O' O' ℂ)) * choiMap A B C).trace := (trace_kron_one_mul R _).symm
    _ = ∑ k, ((Aᵀ ⊗ₖ B k)ᴴ * (R ⊗ₖ (1 : Matrix O' O' ℂ)) * (Aᵀ ⊗ₖ B k) * C).trace := by
        rw [choiMap, Matrix.mul_sum, Matrix.trace_sum]
        exact Finset.sum_congr rfl fun k _ => trace_mul_sandwich _ _ _
    _ = ((((Aᵀ)ᴴ * R * Aᵀ) ⊗ₖ (1 : Matrix O O ℂ)) * C).trace := by
        rw [← hsum, Matrix.sum_mul, Matrix.trace_sum]
    _ = ((Aᵀ)ᴴ * R * Aᵀ * ptraceOut C).trace := trace_kron_one_mul _ _
    _ = (R * (Aᵀ * ptraceOut C * (Aᵀ)ᴴ)).trace := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]

/-- An isometric pre-processing (`Aᴴ A = 1`) and a trace-preserving post-processing
(`∑ k, (B k)ᴴ B k = 1`) map CPTP Choi matrices to CPTP Choi matrices. -/
lemma isCPTP_choiMap [DecidableEq I] [DecidableEq I'] [DecidableEq O] [DecidableEq O']
    (A : Matrix I I' ℂ) (hA : Aᴴ * A = 1) (B : κ → Matrix O' O ℂ) (hB : ∑ k, (B k)ᴴ * B k = 1)
    {C : Matrix (I × O) (I × O) ℂ} (hC : IsCPTP C) : IsCPTP (choiMap A B C) := by
  refine ⟨choiMap_posSemidef A B hC.1, ?_⟩
  rw [ptraceOut_choiMap A B hB, hC.2, Matrix.mul_one, Matrix.transpose_conjTranspose,
    ← Matrix.conjTranspose_transpose, ← Matrix.transpose_mul, hA, Matrix.transpose_one]

/-- The register-controlled post-processing only sees the branch `x' = x`. -/
lemma regKraus_mul_luedersKraus (T : Fin 2 → κ → Matrix O H ℂ) (P : Matrix H H ℂ)
    (x' x : Fin 2) (k : κ) :
    regKraus T (x', k) * luedersKraus P x = if x' = x then T x k * P else 0 := by
  ext o h
  by_cases hx : x' = x
  · subst hx
    simp [regKraus, luedersKraus, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul]
  · simp only [regKraus, luedersKraus, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
      hx, if_false, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun h' _ => Finset.sum_eq_zero fun r _ => ?_
    by_cases h1 : r = x'
    · have h2 : r ≠ x := h1 ▸ hx
      simp [h2]
    · simp [h1]

/-- The register-controlled post-processing is trace preserving if every branch is. -/
lemma sum_regKraus [DecidableEq H] (T : Fin 2 → κ → Matrix O H ℂ)
    (hT : ∀ x, ∑ k, (T x k)ᴴ * T x k = 1) : ∑ j, (regKraus T j)ᴴ * regKraus T j = 1 := by
  ext ⟨h, r⟩ ⟨h', r'⟩
  have key : ∀ x, ∑ k, ∑ o, star (T x k o h) * T x k o h' = (1 : Matrix H H ℂ) h h' := by
    intro x
    rw [← hT x]
    simp [Matrix.sum_apply, Matrix.mul_apply]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, regKraus,
    Matrix.of_apply, Fintype.sum_prod_type]
  rw [Fin.sum_univ_two]
  fin_cases r <;> fin_cases r' <;> simp [Matrix.one_apply] <;>
    simpa [Matrix.one_apply] using key _

/-- `(P ⊗ |x⟩)ᴴ (P ⊗ |x⟩) = Pᴴ P`. -/
lemma luedersKraus_conjTranspose_mul (P : Matrix H H ℂ) (x : Fin 2) :
    (luedersKraus P x)ᴴ * luedersKraus P x = Pᴴ * P := by
  ext h h'
  simp [luedersKraus, Matrix.mul_apply, Fintype.sum_prod_type]

lemma IsProjFamily.conjTranspose_mul_self [DecidableEq H] {P : Fin 2 → Fin 2 → Matrix H H ℂ}
    (hP : IsProjFamily P) (x a : Fin 2) : (P x a)ᴴ * P x a = P x a := by
  have h1 := ((hP x).1 a).isSelfAdjoint
  have h2 := ((hP x).1 a).isIdempotentElem
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose] at h1
  rw [h1]
  exact h2

/-- The Lüders instruments of a projective family are instruments. -/
lemma isInstrument_luedersInstr [DecidableEq H] {P : Fin 2 → Fin 2 → Matrix H H ℂ}
    (hP : IsProjFamily P) : IsInstrument (luedersInstr P) := by
  intro x
  refine ⟨fun a => krausChoi_posSemidef _, ?_⟩
  simp only [luedersInstr]
  rw [ptraceOut_sum]
  simp only [ptraceOut_krausChoi, luedersKraus_conjTranspose_mul,
    hP.conjTranspose_mul_self]
  rw [← Matrix.transpose_sum, (hP x).2, Matrix.transpose_one]

/-- `(A |i⟩⟨j| B) a b = A a i * B j b`. -/
lemma mul_single_mul_apply {m n p : Type*} [Fintype n] [DecidableEq n] (A : Matrix m n ℂ)
    (B : Matrix n p ℂ) (i j : n) (a : m) (b : p) :
    (A * Matrix.single i j (1 : ℂ) * B) a b = A a i * B j b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- `krausChoi K` is the Choi matrix of `ρ ↦ K ρ Kᴴ`. -/
lemma krausChoi_eq_choiMatrix [DecidableEq I] (K : Matrix O I ℂ) :
    krausChoi K = choiMatrix (fun ρ : Matrix I I ℂ => K * ρ * Kᴴ) := by
  ext ⟨i, o⟩ ⟨j, o'⟩
  simp only [choiMatrix, krausChoi, Matrix.of_apply, mul_single_mul_apply,
    Matrix.conjTranspose_apply]

/-- The Lüders Choi matrices of a projective family are the Choi matrices of the Lüders
instruments `ρ ↦ P x a ρ P x a ⊗ |x⟩⟨x|`. -/
lemma luedersInstr_eq_choiMatrix [DecidableEq H] {P : Fin 2 → Fin 2 → Matrix H H ℂ}
    (hP : IsProjFamily P) (x a : Fin 2) :
    luedersInstr P x a = choiMatrix (fun ρ : Matrix H H ℂ =>
      (P x a * ρ * P x a) ⊗ₖ (Matrix.single x x 1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hH : (P x a)ᴴ = P x a := ((hP x).1 a).isSelfAdjoint.star_eq
  have hstar : ∀ g g', star (P x a g g') = P x a g' g := fun g g' =>
    (Matrix.conjTranspose_apply (P x a) g g').symm.trans (congrFun (congrFun hH g') g)
  ext ⟨i, h, r⟩ ⟨j, h', r'⟩
  rw [luedersInstr_apply]
  simp only [choiMatrix, Matrix.of_apply, Matrix.kroneckerMap_apply, mul_single_mul_apply,
    Matrix.single_apply]
  rw [hstar h' j]
  by_cases hr : r = x <;> by_cases hr' : r' = x
  · subst hr hr'
    simp
  · simp [hr', Ne.symm hr']
  · simp [hr, Ne.symm hr]
  · simp [hr, Ne.symm hr]

end Lemmas

end GYNIUpper
