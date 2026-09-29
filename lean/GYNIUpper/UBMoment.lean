import GYNIUpper.UBScalarTrace

/-!
# Upper bound, part 3: the moment matrix and weak duality

* `sum_smul_of_class`: `∑ᵢ aᵢ • τ (g i) = (∑_{g i = e} aᵢ) • τ e` if the class sums of `a` vanish for all
  classes `≠ e`.
* `v2_identity` (Lemma 3(c) in the form used here): let `C p`, `D q` be matrices whose partial traces
  depend only on a class, `Tr_out C p = τ_A (cls_A p)`, `τ_A e_A = 1` (same for Bob). If `Φ` has
  vanishing class sums, `∑_{cls_A p = t} Φ p q = 0` for `t ≠ e_A` and all `q`, and likewise for Bob,
  then `∑_{p,q} Φ p q Tr[W (C p ⊗ D q)] = ∑_{cls_A p = e_A, cls_B q = e_B} Φ p q` for every process
  `W`. (This is the statement "(V2) holds for all coefficient tensors in `E_A ⊗ E_B`".)
* `gram_psd`, `sum_mul_nonneg_of_psd`: the register blocks of the moment matrix are Gram matrices,
  and `∑ᵢⱼ Yᵢⱼ Gᵢⱼ ≥ 0` for positive semidefinite `Y` and `G` (Schur product theorem).
* `gyni_eq_obj`: `I_GYNI = Re ∑_{p,q} o p q Γ p q` for the objective tensor `objT` (Lemma 3(d)).
* `gyni_le_of_dual`: weak duality. If `Φ` has vanishing class sums and `Φ - objT` is positive
  semidefinite on each register block, then `I_GYNI ≤ ∑_{p, q of class e} Φ p q`.

Index conventions: a pair of Alice is `p = (r, a, a')` (register `r`, bra word `wd a`, ket word
`wd a'`), its class is `clsW (wd a) (wd a')`; the moment matrix entry is
`Γ p q = Tr[W (|wd a', r⟩⟨wd a, r| ⊗ |wd b', s⟩⟨wd b, s|)] = ⟨a r, b s| W |a' r, b' s⟩`.
-/

namespace GYNIUpperBound

open Matrix GYNIProof Finset
open scoped ComplexOrder Kronecker

/-! ## Class sums -/

section ClassSum

variable {ι T M : Type*} [Fintype ι] [DecidableEq T] [AddCommMonoid M] [Module ℂ M]

lemma sum_smul_of_class (g : ι → T) (τ : T → M) (e : T) (a : ι → ℂ)
    (h : ∀ t, t ≠ e → ∑ i ∈ univ.filter (fun i => g i = t), a i = 0) :
    ∑ i, a i • τ (g i) = (∑ i ∈ univ.filter (fun i => g i = e), a i) • τ e := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := univ.image g)
    (fun i _ => Finset.mem_image_of_mem g (Finset.mem_univ i))]
  have hin : ∀ t ∈ univ.image g, ∑ i ∈ univ.filter (fun i => g i = t), a i • τ (g i)
      = (∑ i ∈ univ.filter (fun i => g i = t), a i) • τ t := by
    intro t _
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hin]
  by_cases he : e ∈ univ.image g
  · rw [Finset.sum_eq_single e]
    · intro t _ hte
      rw [h t hte, zero_smul]
    · intro hne; exact absurd he hne
  · rw [Finset.sum_eq_zero]
    · have : univ.filter (fun i => g i = e) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun i _ hi => he ?_
        exact hi ▸ Finset.mem_image_of_mem g (Finset.mem_univ i)
      rw [this, Finset.sum_empty, zero_smul]
    · intro t ht
      have hte : t ≠ e := fun h => he (h ▸ ht)
      rw [h t hte, zero_smul]

end ClassSum

/-! ## The V2 identity -/

section V2

variable {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

lemma trace_mul_kron_sum_right (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (E : Matrix (AI × AO) (AI × AO) ℂ) {κ : Type*} (s : Finset κ) (c : κ → ℂ)
    (D : κ → Matrix (BI × BO) (BI × BO) ℂ) :
    (W * (E ⊗ₖ ∑ k ∈ s, c k • D k)).trace = ∑ k ∈ s, c k * (W * (E ⊗ₖ D k)).trace := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, trace_mul_kron_add_right,
      trace_mul_kron_smul_right, ih]

lemma trace_mul_kron_sum_left (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (E : Matrix (BI × BO) (BI × BO) ℂ) {κ : Type*} (s : Finset κ)
    (D : κ → Matrix (AI × AO) (AI × AO) ℂ) :
    (W * ((∑ k ∈ s, D k) ⊗ₖ E)).trace = ∑ k ∈ s, (W * (D k ⊗ₖ E)).trace := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, trace_mul_kron_add_left, ih]

lemma ptraceOut_finsum {I O κ : Type*} [Fintype I] [Fintype O] (s : Finset κ)
    (C : κ → Matrix (I × O) (I × O) ℂ) : ptraceOut (∑ k ∈ s, C k) = ∑ k ∈ s, ptraceOut (C k) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i j; simp [ptraceOut]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ptraceOut_add, ih]

variable {ιA ιB TA TB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq TA] [DecidableEq TB]

/-- The V2 identity for coefficient tensors with vanishing class sums. -/
theorem v2_identity {W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ}
    (hW : IsProcess W) (C : ιA → Matrix (AI × AO) (AI × AO) ℂ)
    (D : ιB → Matrix (BI × BO) (BI × BO) ℂ) (clsA : ιA → TA) (clsB : ιB → TB)
    (τA : TA → Matrix AI AI ℂ) (τB : TB → Matrix BI BI ℂ) (eA : TA) (eB : TB)
    (hτA : τA eA = 1) (hτB : τB eB = 1)
    (hC : ∀ p, ptraceOut (C p) = τA (clsA p)) (hD : ∀ q, ptraceOut (D q) = τB (clsB q))
    (Φ : ιA → ιB → ℂ)
    (hCA : ∀ t, t ≠ eA → ∀ q, ∑ p ∈ univ.filter (fun p => clsA p = t), Φ p q = 0)
    (hCB : ∀ u, u ≠ eB → ∀ p, ∑ q ∈ univ.filter (fun q => clsB q = u), Φ p q = 0) :
    ∑ p, ∑ q, Φ p q * (W * (C p ⊗ₖ D q)).trace =
      ∑ p ∈ univ.filter (fun p => clsA p = eA), ∑ q ∈ univ.filter (fun q => clsB q = eB),
        Φ p q := by
  -- Bob's side: `Y p = ∑_q Φ p q • D q` has scalar partial trace `ν p`
  set Y : ιA → Matrix (BI × BO) (BI × BO) ℂ := fun p => ∑ q, Φ p q • D q with hY
  set ν : ιA → ℂ := fun p => ∑ q ∈ univ.filter (fun q => clsB q = eB), Φ p q with hν
  have hYtr : ∀ p, ptraceOut (Y p) = ν p • 1 := by
    intro p
    simp only [hY, ptraceOut_finsum, ptraceOut_smul, hD]
    rw [sum_smul_of_class clsB τB eB (Φ p) (fun u hu => hCB u hu p), hτB]
  have hLHS : ∑ p, ∑ q, Φ p q * (W * (C p ⊗ₖ D q)).trace
      = ∑ p, (W * (C p ⊗ₖ Y p)).trace := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hY, trace_mul_kron_sum_right]
  rw [hLHS]
  -- group Alice's pairs by class
  rw [← Finset.sum_fiberwise_of_maps_to (g := clsA) (t := univ.image clsA)
    (fun p _ => Finset.mem_image_of_mem clsA (Finset.mem_univ p))]
  have hclass : ∀ t ∈ univ.image clsA,
      ∑ p ∈ univ.filter (fun p => clsA p = t), (W * (C p ⊗ₖ Y p)).trace
        = if t = eA then ∑ p ∈ univ.filter (fun p => clsA p = eA), ν p else 0 := by
    intro t ht
    obtain ⟨p₀, -, hp₀⟩ := Finset.mem_image.mp ht
    -- replace `C p` by `C p₀` inside the class
    have hrep : ∀ p ∈ univ.filter (fun p => clsA p = t),
        (W * (C p ⊗ₖ Y p)).trace = (W * (C p₀ ⊗ₖ Y p)).trace := by
      intro p hp
      have hpt := (Finset.mem_filter.mp hp).2
      have hdiff : ptraceOut (C p - C p₀) = (0 : ℂ) • 1 := by
        rw [ptraceOut_sub, hC, hC, hpt, hp₀, sub_self, zero_smul]
      have h0 := trace_kron_of_scalar hW hdiff (hYtr p)
      have hsplit : C p = (C p - C p₀) + C p₀ := by abel
      rw [hsplit, trace_mul_kron_add_left, h0, zero_mul, zero_add]
    rw [Finset.sum_congr rfl hrep]
    -- `∑_{p ∈ t} Y p` as a combination of the `D q`
    have hsumY : ∑ p ∈ univ.filter (fun p => clsA p = t), Y p
        = ∑ q, (∑ p ∈ univ.filter (fun p => clsA p = t), Φ p q) • D q := by
      simp only [hY]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_smul]
    have hlin : ∑ p ∈ univ.filter (fun p => clsA p = t), (W * (C p₀ ⊗ₖ Y p)).trace
        = (W * (C p₀ ⊗ₖ ∑ p ∈ univ.filter (fun p => clsA p = t), Y p)).trace := by
      have := trace_mul_kron_sum_right W (C p₀) (univ.filter (fun p => clsA p = t))
        (fun _ => (1 : ℂ)) Y
      simp only [one_smul, one_mul] at this
      exact this.symm
    rw [hlin]
    split_ifs with hte
    · subst hte
      have htr : ptraceOut (∑ p ∈ univ.filter (fun p => clsA p = t), Y p)
          = (∑ p ∈ univ.filter (fun p => clsA p = t), ν p) • 1 := by
        rw [ptraceOut_finsum, Finset.sum_smul]
        exact Finset.sum_congr rfl fun p _ => hYtr p
      have hC0 : ptraceOut (C p₀) = (1 : ℂ) • 1 := by rw [hC, hp₀, hτA, one_smul]
      rw [trace_kron_of_scalar hW hC0 htr, one_mul]
    · rw [hsumY]
      have hz : ∀ q, (∑ p ∈ univ.filter (fun p => clsA p = t), Φ p q) • D q = 0 := by
        intro q; rw [hCA t hte q, zero_smul]
      simp only [hz, Finset.sum_const_zero, kronecker_zero, Matrix.mul_zero, trace_zero]
  rw [Finset.sum_congr rfl hclass]
  rw [Finset.sum_ite_eq' (univ.image clsA) eA]
  split_ifs with he
  · rfl
  · have : univ.filter (fun p => clsA p = eA) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun p _ hp => he ?_
      exact hp ▸ Finset.mem_image_of_mem clsA (Finset.mem_univ p)
    rw [this]; simp

end V2

/-! ## Rank-one Choi matrices and the Gram form -/

section Gram

variable {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]

/-- The product vector `(x ⊗ u) (p, q) = x p * u q`. -/
def kv {α β : Type*} (x : α → ℂ) (u : β → ℂ) : α × β → ℂ := fun p => x p.1 * u p.2

lemma kron_vecMulVec {α β : Type*} (x y : α → ℂ) (u v : β → ℂ) :
    (vecMulVec x (star y) ⊗ₖ vecMulVec u (star v)) = vecMulVec (kv x u) (star (kv y v)) := by
  ext p q
  simp only [kroneckerMap_apply, vecMulVec_apply, kv, Pi.star_apply, star_mul']
  ring

lemma trace_mul_vecMulVec {ι : Type*} [Fintype ι] (W : Matrix ι ι ℂ) (z w : ι → ℂ) :
    (W * vecMulVec z (star w)).trace = star w ⬝ᵥ (W *ᵥ z) := by
  simp only [trace, diag_apply, mul_apply, vecMulVec_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Gram

/-! ## Positive semidefinite pairing -/

section Pairing

variable {ι : Type*} [Fintype ι]

/-- `∑ᵢⱼ Yᵢⱼ Gᵢⱼ ≥ 0` for positive semidefinite `Y`, `G` (Schur product theorem). -/
lemma sum_mul_nonneg_of_psd {Y G : Matrix ι ι ℂ} (hY : Y.PosSemidef) (hG : G.PosSemidef) :
    0 ≤ ∑ i, ∑ j, Y i j * G i j := by
  have h := (hY.hadamard hG).dotProduct_mulVec_nonneg (fun _ => 1)
  have e : star (fun _ : ι => (1 : ℂ)) ⬝ᵥ ((Y ⊙ G) *ᵥ fun _ => 1) = ∑ i, ∑ j, Y i j * G i j := by
    simp [dotProduct, mulVec, hadamard]
  rwa [e] at h

/-- A Gram matrix `(⟨vᵢ| W |vⱼ⟩)ᵢⱼ` of a positive semidefinite `W` is positive semidefinite. -/
lemma gram_psd {κ : Type*} [Fintype κ] {W : Matrix κ κ ℂ} (hW : W.PosSemidef) (v : ι → κ → ℂ) :
    (Matrix.of fun i j => star (v i) ⬝ᵥ (W *ᵥ v j)).PosSemidef := by
  have h := hW.conjTranspose_mul_mul_same (Matrix.of fun (k : κ) (i : ι) => v i k)
  convert h using 1
  ext i j
  simp only [Matrix.of_apply, mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Pairing

end GYNIUpperBound
