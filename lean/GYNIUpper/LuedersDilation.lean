import GYNIUpper.LuedersChoi

/-!
# Lüders normal form, part 2: Lüders dilation of one instrument

For an instrument `M` (settings and outcomes in `Fin 2`, Choi matrices on `I × O`) a
*Lüders dilation* (`IsLuedersDilation M J P T`) consists of a space `H`, an isometry
`J : ℂ^I → ℂ^H`, projective measurements `P x a` on `H` (`IsProjFamily P`) and, for every setting
`x`, the Kraus operators `T x k : ℂ^H → ℂ^O` of a trace-preserving post-processing, such that
`M x a` is the Choi matrix of `ρ ↦ ∑ k, T x k P x a J ρ Jᴴ P x a (T x k)ᴴ`.

Construction (Lemma 1 of `PROOF.md`, with an explicit unitary completion):
* Kraus operators `K x a k`, `k ∈ I × O`, of `M x a`, from `M x a = Bᴴ B` (`exists_kraus`);
* the Stinespring isometry `V x = ∑_{a,k} K x a k ⊗ |a, k⟩ : ℂ^I → ℂ^O ⊗ ℂ² ⊗ ℂ^κ` (`stine`);
* the space `H = (O × (Fin 2 × κ)) ⊕ I` (`DilSpace`), the isometry `J` = inclusion of the summand
  `I` (`dilJ`), and the self-adjoint unitary `U x = [[1 - V Vᴴ, V], [Vᴴ, 0]]` (`dilU`), which
  satisfies `U x J = V x` (into the first summand);
* `P x a = U x D a U x` (`dilP`), with the diagonal projector `D a` onto the outcome `a`
  (`dilD`; the summand `I` is attached to the outcome `0`);
* `T x k = S k U x` (`dilT`), where `S (inl e) = 1_O ⊗ ⟨e|` on the first summand and
  `S (inr i) = |o₀⟩⟨i|` on the second summand (`dilSel`).

`IsLuedersDilation.reindex` transports a dilation along an equivalence `H ≃ H'`, and
`exists_luedersDilation_fin` gives a Lüders dilation on `Fin n` for every instrument with a
nonempty output space.
-/

set_option linter.unusedSectionVars false

namespace GYNIUpper

open Matrix GYNIProof
open scoped ComplexOrder Kronecker MatrixOrder

/-! ### Definitions -/

section Defs

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- `J`, `P`, `T` realise the instrument `M` in Lüders form: `J` is an isometry, `P` is a family of
projective measurements, every `T x` is the Kraus family of a trace-preserving map, and
`M x a` is the Choi matrix of `ρ ↦ ∑ k, T x k P x a J ρ Jᴴ P x a (T x k)ᴴ`. -/
structure IsLuedersDilation {H ι : Type*} [Fintype H] [DecidableEq H] [Fintype ι]
    (M : Fin 2 → Fin 2 → Matrix (I × O) (I × O) ℂ) (J : Matrix H I ℂ)
    (P : Fin 2 → Fin 2 → Matrix H H ℂ) (T : Fin 2 → ι → Matrix O H ℂ) : Prop where
  iso : Jᴴ * J = 1
  proj : IsProjFamily P
  tp : ∀ x, ∑ k, (T x k)ᴴ * T x k = 1
  dil : ∀ x a, ∑ k, krausChoi (T x k * P x a * J) = M x a

end Defs

/-- The dilation space `(O × (Fin 2 × κ)) ⊕ I`. -/
abbrev DilSpace (I O κ : Type*) := (O × (Fin 2 × κ)) ⊕ I

/-- The isometry `J : ℂ^I → ℂ^(DilSpace I O κ)`, the inclusion of the summand `I`. -/
def dilJ (I O κ : Type*) [DecidableEq I] : Matrix (DilSpace I O κ) I ℂ := fromRows 0 1

/-- The diagonal of the projector onto the outcome `a`; the summand `I` belongs to outcome `0`. -/
def dilDiag (I O κ : Type*) (a : Fin 2) : DilSpace I O κ → ℂ :=
  Sum.elim (fun p => if p.2.1 = a then 1 else 0) fun _ => if a = 0 then 1 else 0

/-- The diagonal projector `D a` onto the outcome `a`. -/
def dilD (I O κ : Type*) [DecidableEq I] [DecidableEq O] [DecidableEq κ] (a : Fin 2) :
    Matrix (DilSpace I O κ) (DilSpace I O κ) ℂ :=
  diagonal (dilDiag I O κ a)

/-- `[[1 - V Vᴴ, V], [Vᴴ, 0]]` is unitary (and self-adjoint) for an isometry `V`. -/
lemma fromBlocks_isometry_mul_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) :
    fromBlocks (1 - V * Vᴴ) V Vᴴ (0 : Matrix n n ℂ) *
      fromBlocks (1 - V * Vᴴ) V Vᴴ (0 : Matrix n n ℂ) = 1 := by
  have hVV : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  have e1 : (1 - V * Vᴴ) * (1 - V * Vᴴ) + V * Vᴴ = 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hVV]
    abel
  have e2 : (1 - V * Vᴴ) * V + V * (0 : Matrix n n ℂ) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self,
      Matrix.mul_zero, add_zero]
  have e3 : Vᴴ * (1 - V * Vᴴ) + (0 : Matrix n n ℂ) * Vᴴ = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self,
      Matrix.zero_mul, add_zero]
  have e4 : Vᴴ * V + (0 : Matrix n n ℂ) * (0 : Matrix n n ℂ) = 1 := by
    rw [hV, Matrix.zero_mul, add_zero]
  rw [fromBlocks_multiply, e1, e2, e3, e4, fromBlocks_one]

/-! ### Kraus operators of an instrument -/

section Kraus

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- Every instrument has Kraus operators indexed by `I × O`: `M x a = ∑ k, C_{K x a k}` and
`∑_{a,k} (K x a k)ᴴ K x a k = 1`. -/
lemma exists_kraus {M : Fin 2 → Fin 2 → Matrix (I × O) (I × O) ℂ} (hM : IsInstrument M) :
    ∃ K : Fin 2 → Fin 2 → I × O → Matrix O I ℂ,
      (∀ x a, ∑ k, krausChoi (K x a k) = M x a) ∧ ∀ x, ∑ a, ∑ k, (K x a k)ᴴ * K x a k = 1 := by
  have hB : ∀ x a, ∃ B : Matrix (I × O) (I × O) ℂ, M x a = star B * B := fun x a =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ((hM x).1 a).nonneg
  choose B hB using hB
  let K : Fin 2 → Fin 2 → I × O → Matrix O I ℂ := fun x a k =>
    Matrix.of fun o i => star (B x a k (i, o))
  have hdec : ∀ x a, ∑ k, krausChoi (K x a k) = M x a := by
    intro x a
    rw [hB x a]
    ext p q
    simp [K, krausChoi, Matrix.sum_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
  refine ⟨K, hdec, fun x => ?_⟩
  have h := (hM x).2
  simp_rw [← hdec x, ptraceOut_sum, ptraceOut_krausChoi] at h
  rw [← Matrix.transpose_eq_one, Matrix.transpose_sum]
  simp_rw [Matrix.transpose_sum]
  exact h

end Kraus

/-! ### The construction -/

section Construction

variable {I O κ : Type*} [Fintype I] [Fintype O] [Fintype κ] [DecidableEq I] [DecidableEq O]
  [DecidableEq κ]

/-- The Stinespring isometry `V x = ∑_{a,k} K x a k ⊗ |a, k⟩ : ℂ^I → ℂ^O ⊗ ℂ² ⊗ ℂ^κ`. -/
def stine (K : Fin 2 → Fin 2 → κ → Matrix O I ℂ) (x : Fin 2) :
    Matrix (O × (Fin 2 × κ)) I ℂ :=
  Matrix.of fun p i => K x p.2.1 p.2.2 p.1 i

/-- The self-adjoint unitary `U x = [[1 - V Vᴴ, V], [Vᴴ, 0]]` on `DilSpace I O κ`. -/
def dilU (K : Fin 2 → Fin 2 → κ → Matrix O I ℂ) (x : Fin 2) :
    Matrix (DilSpace I O κ) (DilSpace I O κ) ℂ :=
  fromBlocks (1 - stine K x * (stine K x)ᴴ) (stine K x) (stine K x)ᴴ 0

/-- The projectors `P x a = U x D a U x`. -/
def dilP (K : Fin 2 → Fin 2 → κ → Matrix O I ℂ) (x a : Fin 2) :
    Matrix (DilSpace I O κ) (DilSpace I O κ) ℂ :=
  dilU K x * dilD I O κ a * dilU K x

/-- The selection operators of the post-processing: `inl e` applies `1_O ⊗ ⟨e|` to the first
summand; `inr i` maps the basis vector `|i⟩` of the second summand to `|o₀⟩`. -/
def dilSel (o₀ : O) : (Fin 2 × κ) ⊕ I → Matrix O (DilSpace I O κ) ℂ
  | Sum.inl e => fromCols (Matrix.of fun o p => if p = (o, e) then 1 else 0) 0
  | Sum.inr i => fromCols 0 (Matrix.of fun o i' => if o = o₀ ∧ i' = i then 1 else 0)

/-- The Kraus operators `T x k = S k U x` of the post-processing channels. -/
def dilT (K : Fin 2 → Fin 2 → κ → Matrix O I ℂ) (o₀ : O) (x : Fin 2) (k : (Fin 2 × κ) ⊕ I) :
    Matrix O (DilSpace I O κ) ℂ :=
  dilSel o₀ k * dilU K x

variable {K : Fin 2 → Fin 2 → κ → Matrix O I ℂ}

lemma stine_iso (hK : ∀ x, ∑ a, ∑ k, (K x a k)ᴴ * K x a k = 1) (x : Fin 2) :
    (stine K x)ᴴ * stine K x = 1 := by
  rw [← hK x]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stine, Matrix.of_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

lemma dilU_conjTranspose (x : Fin 2) : (dilU K x)ᴴ = dilU K x := by
  simp [dilU, fromBlocks_conjTranspose, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]

lemma dilU_mul_self {x : Fin 2} (hV : (stine K x)ᴴ * stine K x = 1) :
    dilU K x * dilU K x = 1 :=
  fromBlocks_isometry_mul_self _ hV

lemma dilU_mul_dilJ (x : Fin 2) :
    dilU K x * dilJ I O κ = fromRows (stine K x) (0 : Matrix I I ℂ) := by
  simp [dilU, dilJ, fromBlocks_mul_fromRows]

lemma dilJ_iso : (dilJ I O κ)ᴴ * dilJ I O κ = 1 := by
  simp [dilJ, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

lemma dilDiag_mul_self (a : Fin 2) (l : DilSpace I O κ) :
    dilDiag I O κ a l * dilDiag I O κ a l = dilDiag I O κ a l := by
  cases l <;> simp only [dilDiag, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp

lemma star_dilDiag (a : Fin 2) (l : DilSpace I O κ) :
    star (dilDiag I O κ a l) = dilDiag I O κ a l := by
  cases l <;> simp only [dilDiag, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp

lemma sum_dilDiag (l : DilSpace I O κ) : ∑ a, dilDiag I O κ a l = 1 := by
  cases l <;> simp [dilDiag]

lemma dilD_mul_self (a : Fin 2) : dilD I O κ a * dilD I O κ a = dilD I O κ a := by
  rw [dilD, diagonal_mul_diagonal]
  exact congrArg diagonal (funext (dilDiag_mul_self a))

lemma dilD_conjTranspose (a : Fin 2) : (dilD I O κ a)ᴴ = dilD I O κ a := by
  rw [dilD, diagonal_conjTranspose]
  exact congrArg diagonal (funext (star_dilDiag a))

lemma sum_dilD : ∑ a, dilD I O κ a = 1 := by
  rw [Fin.sum_univ_two, dilD, dilD, diagonal_add, ← diagonal_one]
  refine congrArg diagonal (funext fun l => ?_)
  simpa [Fin.sum_univ_two] using sum_dilDiag l

lemma isStarProjection_dilP {x : Fin 2} (hV : (stine K x)ᴴ * stine K x = 1) (a : Fin 2) :
    IsStarProjection (dilP K x a) := by
  constructor
  · show dilP K x a * dilP K x a = dilP K x a
    simp only [dilP, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dilU K x) (dilU K x), dilU_mul_self hV, Matrix.one_mul,
      ← Matrix.mul_assoc (dilD I O κ a) (dilD I O κ a), dilD_mul_self]
  · show star (dilP K x a) = dilP K x a
    rw [Matrix.star_eq_conjTranspose, dilP, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      dilU_conjTranspose, dilD_conjTranspose, Matrix.mul_assoc]

lemma sum_dilP {x : Fin 2} (hV : (stine K x)ᴴ * stine K x = 1) : ∑ a, dilP K x a = 1 := by
  simp only [dilP]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_dilD, Matrix.mul_one, dilU_mul_self hV]

lemma sum_dilSel (o₀ : O) :
    ∑ k, (dilSel o₀ k)ᴴ * dilSel o₀ k = (1 : Matrix (DilSpace I O κ) (DilSpace I O κ) ℂ) := by
  ext l l'
  rw [Matrix.sum_apply, Fintype.sum_sum_type]
  rcases l with ⟨o₁, e₁⟩ | i <;> rcases l' with ⟨o₂, e₂⟩ | i'
  · simp [dilSel, Matrix.mul_apply, Matrix.one_apply, ite_and]
    split_ifs <;> simp
  · simp [dilSel, Matrix.mul_apply]
  · simp [dilSel, Matrix.mul_apply]
  · simp [dilSel, Matrix.mul_apply, Matrix.one_apply, ite_and]

lemma sum_dilT {x : Fin 2} (hV : (stine K x)ᴴ * stine K x = 1) (o₀ : O) :
    ∑ k, (dilT K o₀ x k)ᴴ * dilT K o₀ x k = 1 := by
  simp only [dilT, Matrix.conjTranspose_mul]
  calc ∑ k : (Fin 2 × κ) ⊕ I, (dilU K x)ᴴ * (dilSel o₀ k)ᴴ * (dilSel o₀ k * dilU K x)
      = (dilU K x)ᴴ * (∑ k : (Fin 2 × κ) ⊕ I, (dilSel o₀ k)ᴴ * dilSel o₀ k) * dilU K x := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [sum_dilSel, Matrix.mul_one, dilU_conjTranspose, dilU_mul_self hV]

lemma dilT_mul_dilP_mul_dilJ {x : Fin 2} (hV : (stine K x)ᴴ * stine K x = 1) (o₀ : O)
    (a : Fin 2) (k : (Fin 2 × κ) ⊕ I) :
    dilT K o₀ x k * dilP K x a * dilJ I O κ =
      dilSel o₀ k *
        (dilD I O κ a * fromRows (stine K x) (0 : Matrix I I ℂ) : Matrix (DilSpace I O κ) I ℂ) := by
  simp only [dilT, dilP, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dilU K x) (dilU K x), dilU_mul_self hV, Matrix.one_mul,
    dilU_mul_dilJ]

lemma dilSel_inl_mul (o₀ : O) (x a a' : Fin 2) (k : κ) :
    dilSel o₀ (Sum.inl (a', k) : (Fin 2 × κ) ⊕ I) *
        (dilD I O κ a * fromRows (stine K x) (0 : Matrix I I ℂ) : Matrix (DilSpace I O κ) I ℂ) =
      if a' = a then K x a k else 0 := by
  ext o i
  by_cases ha : a' = a
  · subst ha
    simp [dilSel, dilD, dilDiag, stine, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]
    rw [Finset.sum_eq_single (o, a', k)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · simp [dilSel, dilD, dilDiag, stine, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply,
      ha]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = (o, a', k)
    · subst hb
      simp [ha]
    · simp [hb]

lemma dilSel_inr_mul (o₀ : O) (x a : Fin 2) (i : I) :
    dilSel o₀ (Sum.inr i : (Fin 2 × κ) ⊕ I) *
        (dilD I O κ a * fromRows (stine K x) (0 : Matrix I I ℂ) : Matrix (DilSpace I O κ) I ℂ) =
      (0 : Matrix O I ℂ) := by
  ext o i'
  simp [dilSel, dilD, dilDiag, Matrix.mul_apply, Fintype.sum_sum_type]

lemma dil_sum {x : Fin 2} (hV : (stine K x)ᴴ * stine K x = 1) (o₀ : O) (a : Fin 2) :
    ∑ k, krausChoi (dilT K o₀ x k * dilP K x a * dilJ I O κ) = ∑ k, krausChoi (K x a k) := by
  simp_rw [dilT_mul_dilP_mul_dilJ hV]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [dilSel_inl_mul, dilSel_inr_mul, krausChoi_zero, Finset.sum_const_zero, add_zero]
  have h : ∀ (a' : Fin 2) (k : κ),
      krausChoi (if a' = a then K x a k else 0) = if a' = a then krausChoi (K x a k) else 0 := by
    intro a' k
    split_ifs <;> simp [krausChoi_zero]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp

/-- The construction is a Lüders dilation of `M`. -/
theorem isLuedersDilation_construction {M : Fin 2 → Fin 2 → Matrix (I × O) (I × O) ℂ}
    (hK1 : ∀ x a, ∑ k, krausChoi (K x a k) = M x a)
    (hK2 : ∀ x, ∑ a, ∑ k, (K x a k)ᴴ * K x a k = 1) (o₀ : O) :
    IsLuedersDilation M (dilJ I O κ) (dilP K) (dilT K o₀) where
  iso := dilJ_iso
  proj x := ⟨fun a => isStarProjection_dilP (stine_iso hK2 x) a, sum_dilP (stine_iso hK2 x)⟩
  tp x := sum_dilT (stine_iso hK2 x) o₀
  dil x a := (dil_sum (stine_iso hK2 x) o₀ a).trans (hK1 x a)

end Construction

/-! ### Transport along an equivalence -/

section Reindex

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

lemma submatrix_finsetSum {m n m' n' ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ)
    (f : m' → m) (g : n' → n) :
    (∑ k ∈ s, A k).submatrix f g = ∑ k ∈ s, (A k).submatrix f g := by
  ext i j
  simp [Matrix.sum_apply]

/-- A Lüders dilation can be transported along an equivalence `H ≃ H'`. -/
theorem IsLuedersDilation.reindex {H H' ι : Type*} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] [Fintype ι] {M : Fin 2 → Fin 2 → Matrix (I × O) (I × O) ℂ}
    {J : Matrix H I ℂ} {P : Fin 2 → Fin 2 → Matrix H H ℂ} {T : Fin 2 → ι → Matrix O H ℂ}
    (h : IsLuedersDilation M J P T) (e : H ≃ H') :
    IsLuedersDilation M (J.submatrix e.symm id) (fun x a => (P x a).submatrix e.symm e.symm)
      (fun x k => (T x k).submatrix id e.symm) where
  iso := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv, h.iso, submatrix_id_id]
  proj x := by
    refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
    · show (P x a).submatrix e.symm e.symm * (P x a).submatrix e.symm e.symm =
        (P x a).submatrix e.symm e.symm
      rw [submatrix_mul_equiv, ((h.proj x).1 a).isIdempotentElem.eq]
    · show star ((P x a).submatrix e.symm e.symm) = (P x a).submatrix e.symm e.symm
      rw [Matrix.star_eq_conjTranspose, conjTranspose_submatrix, ← Matrix.star_eq_conjTranspose,
        ((h.proj x).1 a).isSelfAdjoint.star_eq]
    · show ∑ a, (P x a).submatrix e.symm e.symm = 1
      rw [← submatrix_finsetSum, (h.proj x).2, submatrix_one_equiv]
  tp x := by
    show ∑ k, ((T x k).submatrix id e.symm)ᴴ * (T x k).submatrix id e.symm = 1
    simp only [conjTranspose_submatrix]
    simp_rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    rw [← submatrix_finsetSum, h.tp x, submatrix_one_equiv]
  dil x a := by
    show ∑ k, krausChoi ((T x k).submatrix id e.symm * (P x a).submatrix e.symm e.symm *
      J.submatrix e.symm id) = M x a
    simp_rw [submatrix_mul_equiv, submatrix_id_id]
    exact h.dil x a

/-- Every instrument with a nonempty output space has a Lüders dilation on some `Fin n`. -/
theorem exists_luedersDilation_fin {M : Fin 2 → Fin 2 → Matrix (I × O) (I × O) ℂ}
    (hM : IsInstrument M) (o₀ : O) :
    ∃ (n : ℕ) (J : Matrix (Fin n) I ℂ) (P : Fin 2 → Fin 2 → Matrix (Fin n) (Fin n) ℂ)
      (T : Fin 2 → (Fin 2 × (I × O)) ⊕ I → Matrix O (Fin n) ℂ), IsLuedersDilation M J P T := by
  obtain ⟨K, hK1, hK2⟩ := exists_kraus hM
  exact ⟨_, _, _, _, (isLuedersDilation_construction hK1 hK2 o₀).reindex
    (Fintype.equivFin (DilSpace I O (I × O)))⟩

end Reindex

end GYNIUpper
