import GYNIProof.Defs
import GYNIProof.Core

/-!
# Positive semidefiniteness from block certificates

* `posSemidef_of_blocks`: a Hermitian matrix on `P × P` that is block diagonal with respect to a
  partition of each factor `P` (given by an equivalence `(Σ c, Fin (sz c)) ≃ P`) is positive
  semidefinite if every block is.
* `posSemidef_of_diagDom`: a symmetric integer matrix with `∑_j |E i j| ≤ 2 E i i` for all `i`
  (diagonal dominance) is positive semidefinite (over `ℂ`).
* `posSemidef_of_gram`: if `c A = L Lᵀ + E` with `c > 0` and `E` as above, `A` is positive
  semidefinite.
* The kernel-checkable certificate format (`rowsOK`, `packCols`, `shapeOK`) and its soundness
  `posSemidef_of_cert`. Row `i` of `c A = L Lᵀ + E` is checked as one integer identity between
  packed rows `∑_j v_j X^j` (Kronecker substitution), which determines the row entrywise because
  all entries are bounded by `X / 2` (`eq_zero_of_sum_pow`).
-/

namespace GYNIProof

open Matrix
open scoped ComplexOrder

/-! ## Block decomposition -/

theorem posSemidef_of_blocks {P C : Type*} [Fintype P] [DecidableEq P] [Fintype C]
    [DecidableEq C] {sz : C → ℕ} (e : (Σ c, Fin (sz c)) ≃ P) (W : Matrix (P × P) (P × P) ℂ)
    (hW : W.IsHermitian)
    (hzero : ∀ s t s' t' : Σ c, Fin (sz c), (s.1 ≠ s'.1 ∨ t.1 ≠ t'.1) →
      W (e s, e t) (e s', e t') = 0)
    (hblk : ∀ cA cB, (Matrix.of fun (p q : Fin (sz cA) × Fin (sz cB)) =>
        W (e ⟨cA, p.1⟩, e ⟨cB, p.2⟩) (e ⟨cA, q.1⟩, e ⟨cB, q.2⟩)).PosSemidef) :
    W.PosSemidef := by
  set E2 : (Σ c, Fin (sz c)) × (Σ c, Fin (sz c)) ≃ P × P := Equiv.prodCongr e e with hE2
  rw [← posSemidef_submatrix_equiv E2]
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hW.submatrix _) fun x => ?_
  have hinner : ∀ a : (Σ c, Fin (sz c)) × (Σ c, Fin (sz c)),
      ((W.submatrix E2 E2) *ᵥ x) a = ∑ q1 : Fin (sz a.1.1), ∑ q2 : Fin (sz a.2.1),
        W (e a.1, e a.2) (e ⟨a.1.1, q1⟩, e ⟨a.2.1, q2⟩) * x (⟨a.1.1, q1⟩, ⟨a.2.1, q2⟩) := by
    intro a
    simp only [mulVec, dotProduct, submatrix_apply, hE2, Equiv.prodCongr_apply, Prod.map]
    rw [Fintype.sum_prod_type, Fintype.sum_sigma, Finset.sum_eq_single a.1.1]
    · refine Finset.sum_congr rfl fun q1 _ => ?_
      rw [Fintype.sum_sigma, Finset.sum_eq_single a.2.1]
      · intro c _ hc
        refine Finset.sum_eq_zero fun q2 _ => ?_
        rw [hzero _ _ _ _ (Or.inr (Ne.symm hc)), zero_mul]
      · simp
    · intro c _ hc
      refine Finset.sum_eq_zero fun q1 _ => Finset.sum_eq_zero fun t _ => ?_
      rw [hzero _ _ _ _ (Or.inl (Ne.symm hc)), zero_mul]
    · simp
  have hq : star x ⬝ᵥ ((W.submatrix E2 E2) *ᵥ x) = ∑ cA, ∑ cB,
      star (fun p : Fin (sz cA) × Fin (sz cB) => x (⟨cA, p.1⟩, ⟨cB, p.2⟩)) ⬝ᵥ
        ((Matrix.of fun (p q : Fin (sz cA) × Fin (sz cB)) =>
          W (e ⟨cA, p.1⟩, e ⟨cB, p.2⟩) (e ⟨cA, q.1⟩, e ⟨cB, q.2⟩)) *ᵥ
          (fun p : Fin (sz cA) × Fin (sz cB) => x (⟨cA, p.1⟩, ⟨cB, p.2⟩))) := by
    rw [dotProduct]
    simp_rw [hinner]
    rw [Fintype.sum_prod_type, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun cA _ => ?_
    simp_rw [Fintype.sum_sigma]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun cB _ => ?_
    simp only [dotProduct, mulVec, Fintype.sum_prod_type, Pi.star_apply, Matrix.of_apply]
  rw [hq]
  exact Finset.sum_nonneg fun cA _ => Finset.sum_nonneg fun cB _ =>
    (hblk cA cB).dotProduct_mulVec_nonneg _

/-! ## Diagonal dominance -/

lemma re_bound (e : ℝ) (a b : ℂ) :
    -|e| * (Complex.normSq a + Complex.normSq b) / 2 ≤ e * (star a * b).re := by
  have h1 : |(star a * b).re| ≤ ‖a‖ * ‖b‖ := by
    calc |(star a * b).re| ≤ ‖star a * b‖ := Complex.abs_re_le_norm _
      _ = ‖a‖ * ‖b‖ := by rw [norm_mul, norm_star]
  have h2 : ‖a‖ * ‖b‖ ≤ (Complex.normSq a + Complex.normSq b) / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have h3 : |e * (star a * b).re| ≤ |e| * ((Complex.normSq a + Complex.normSq b) / 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg e)
  have := neg_abs_le (e * (star a * b).re)
  linarith

theorem posSemidef_of_diagDom {n : ℕ} (E : Matrix (Fin n) (Fin n) ℤ)
    (hsym : ∀ i j, E i j = E j i) (hdom : ∀ i, ∑ j, |E i j| ≤ 2 * E i i) :
    (E.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, hsym i j]
  · have hdiag : ∀ i, 0 ≤ E i i := by
      intro i
      have h1 : |E i i| ≤ ∑ j, |E i j| :=
        Finset.single_le_sum (f := fun j => |E i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have := hdom i
      have := abs_nonneg (E i i)
      linarith
    set z := star x ⬝ᵥ ((E.map (Int.cast : ℤ → ℂ)) *ᵥ x) with hz
    have hz' : z = ∑ i, ∑ j, ((E i j : ℝ) : ℂ) * (star (x i) * x j) := by
      rw [hz, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.map_apply, Pi.star_apply]
      push_cast
      ring
    have hre : z.re = ∑ i, ∑ j, (E i j : ℝ) * (star (x i) * x j).re := by
      rw [hz', Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_ofReal_mul]
    have him : z.im = ∑ i, ∑ j, (E i j : ℝ) * (star (x i) * x j).im := by
      rw [hz', Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.im_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.im_ofReal_mul]
    rw [Complex.nonneg_iff]
    constructor
    · rw [hre]
      -- pairwise bound
      have key : ∀ i j, -|(E i j : ℝ)| * (Complex.normSq (x i) + Complex.normSq (x j)) / 2
          + (if i = j then 2 * (E i i : ℝ) * Complex.normSq (x i) else 0)
          ≤ (E i j : ℝ) * (star (x i) * x j).re := by
        intro i j
        by_cases hij : i = j
        · subst hij
          have hn : (star (x i) * x i).re = Complex.normSq (x i) := by
            rw [Complex.normSq_apply]
            simp [Complex.mul_re]
          rw [if_pos rfl, hn, abs_of_nonneg (by exact_mod_cast hdiag i)]
          ring_nf
          exact le_refl _
        · rw [if_neg hij, add_zero]
          exact re_bound _ _ _
      have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key i j
      refine le_trans ?_ hsum
      -- evaluate the lower bound
      have hswap : ∑ i, ∑ j, |(E i j : ℝ)| * Complex.normSq (x j)
          = ∑ i, ∑ j, |(E i j : ℝ)| * Complex.normSq (x i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsym j i]
      have hlow : ∑ i, ∑ j, (-|(E i j : ℝ)| * (Complex.normSq (x i) + Complex.normSq (x j)) / 2
          + (if i = j then 2 * (E i i : ℝ) * Complex.normSq (x i) else 0))
          = ∑ i, (2 * (E i i : ℝ) - ∑ j, |(E i j : ℝ)|) * Complex.normSq (x i) := by
        have e1 : ∀ i, ∑ j, (-|(E i j : ℝ)| * (Complex.normSq (x i) + Complex.normSq (x j)) / 2
            + (if i = j then 2 * (E i i : ℝ) * Complex.normSq (x i) else 0))
            = -(1 / 2) * ∑ j, |(E i j : ℝ)| * Complex.normSq (x i)
              - (1 / 2) * ∑ j, |(E i j : ℝ)| * Complex.normSq (x j)
              + 2 * (E i i : ℝ) * Complex.normSq (x i) := by
          intro i
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
            Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        simp_rw [e1]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hswap]
        have h3 : ∑ i, (2 * (E i i : ℝ) - ∑ j, |(E i j : ℝ)|) * Complex.normSq (x i)
            = ∑ i, 2 * (E i i : ℝ) * Complex.normSq (x i)
              - ∑ i, ∑ j, |(E i j : ℝ)| * Complex.normSq (x i) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sub_mul, Finset.sum_mul]
        rw [h3]
        ring
      rw [hlow]
      refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (Complex.normSq_nonneg _)
      have := hdom i
      have h' : ((∑ j, |E i j| : ℤ) : ℝ) ≤ ((2 * E i i : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    · rw [him]
      have hanti : ∑ i, ∑ j, (E i j : ℝ) * (star (x i) * x j).im
          = -∑ i, ∑ j, (E i j : ℝ) * (star (x i) * x j).im := by
        conv_lhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsym j i]
        simp [Complex.mul_im]
        ring
      linarith

/-- `c A = L Lᵀ + E` with `c > 0` and `E` diagonally dominant implies `A ≥ 0`. -/
theorem posSemidef_of_gram {n : ℕ} (A L E : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (hc : 0 < c)
    (hEsym : ∀ i j, E i j = E j i) (hdom : ∀ i, ∑ j, |E i j| ≤ 2 * E i i)
    (hid : ∀ i j, c * A i j = ∑ k, L i k * L j k + E i j) :
    (A.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  have hsplit : (c : ℂ) • A.map (Int.cast : ℤ → ℂ)
      = L.map (Int.cast : ℤ → ℂ) * (L.map (Int.cast : ℤ → ℂ))ᴴ + E.map (Int.cast : ℤ → ℂ) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, smul_eq_mul]
    have := congrArg (Int.cast : ℤ → ℂ) (hid i j)
    push_cast at this
    rw [this]
    simp
  have hpsd : ((c : ℂ) • A.map (Int.cast : ℤ → ℂ)).PosSemidef := by
    rw [hsplit]
    exact (posSemidef_self_mul_conjTranspose _).add (posSemidef_of_diagDom E hEsym hdom)
  have hc' : (0 : ℂ) < (c : ℂ)⁻¹ := by
    have : (0 : ℂ) < (c : ℂ) := by exact_mod_cast hc
    exact inv_pos.mpr this
  have := hpsd.smul hc'.le
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_smul] at this

/-! ## Packed rows -/

/-- The check functions `packL`, `dotL`, `packCols`, `sumAbs`, `rowOK`, `rowsOK`, `rowsBoundOK`,
`shapeOK`, `paramsOK` are defined in `Core.lean` (no Mathlib). -/

lemma iabs_eq_abs (a : ℤ) : iabs a = |a| := by
  unfold iabs
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.mp h)).symm

lemma packL_append (X : ℤ) (l m : List ℤ) :
    packL X (l ++ m) = packL X l + X ^ l.length * packL X m := by
  induction l with
  | nil => simp [packL]
  | cons a l ih => simp only [List.cons_append, packL, ih, List.length_cons, pow_succ]; ring

lemma packL_range (X : ℤ) (g : ℕ → ℤ) (n : ℕ) :
    packL X ((List.range n).map g) = ∑ j ∈ Finset.range n, g j * X ^ j := by
  induction n with
  | zero => simp [packL]
  | succ n ih =>
    rw [List.range_succ, List.map_append, packL_append, ih, Finset.sum_range_succ]
    simp [packL]
    ring

lemma packL_eq_sum (X : ℤ) (l : List ℤ) :
    packL X l = ∑ j ∈ Finset.range l.length, l.getD j 0 * X ^ j := by
  induction l with
  | nil => simp [packL]
  | cons a l ih =>
    rw [packL, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

lemma dotL_eq_sum : ∀ (l m : List ℤ), l.length = m.length →
    dotL l m = ∑ k ∈ Finset.range l.length, l.getD k 0 * m.getD k 0
  | [], [], _ => by simp [dotL]
  | a :: l, b :: m, h => by
    rw [dotL, dotL_eq_sum l m (by simpa using h), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

lemma sumAbs_eq_sum (l : List ℤ) : sumAbs l = ∑ k ∈ Finset.range l.length, |l.getD k 0| := by
  induction l with
  | nil => simp [sumAbs]
  | cons a l ih =>
    rw [sumAbs, ih, List.length_cons, Finset.sum_range_succ', iabs_eq_abs]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

lemma packCols_spec (X : ℤ) (m : ℕ) : ∀ (rs : List (List ℤ)), (∀ r ∈ rs, r.length = m) →
    (packCols X m rs).length = m ∧ ∀ k < m,
      (packCols X m rs).getD k 0 = ∑ j ∈ Finset.range rs.length, (rs.getD j []).getD k 0 * X ^ j
  | [], _ => by
    refine ⟨by simp [packCols], fun k hk => ?_⟩
    simp [packCols, List.getD_eq_getElem?_getD, hk]
  | r :: rs, h => by
    obtain ⟨hl, hs⟩ := packCols_spec X m rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    have hr : r.length = m := h r List.mem_cons_self
    refine ⟨by simp [packCols, hl, hr], fun k hk => ?_⟩
    have hk1 : k < r.length := by rw [hr]; exact hk
    have hk2 : k < (packCols X m rs).length := by rw [hl]; exact hk
    rw [packCols, List.getD_eq_getElem _ _ (by simp [hl, hr, hk]), List.getElem_zipWith,
      List.length_cons, Finset.sum_range_succ']
    rw [← List.getD_eq_getElem _ 0 hk1, ← List.getD_eq_getElem _ 0 hk2, hs k hk, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

lemma length_packCols (X : ℤ) (m : ℕ) (rs : List (List ℤ)) (h : ∀ r ∈ rs, r.length = m) :
    (packCols X m rs).length = m :=
  (packCols_spec X m rs h).1

/-- Packing the columns of stacked rows. -/
lemma packCols_append (X : ℤ) (m : ℕ) : ∀ (l1 l2 : List (List ℤ)), (∀ r ∈ l1, r.length = m) →
    (∀ r ∈ l2, r.length = m) →
    packCols X m (l1 ++ l2)
      = List.zipWith (fun a b => a + X ^ l1.length * b) (packCols X m l1) (packCols X m l2)
  | [], l2, _, h2 => by
    rw [List.nil_append]
    apply List.ext_getElem
    · simp [packCols, length_packCols X m l2 h2]
    · intro k hk1 hk2
      simp [packCols]
  | r :: l1, l2, h1, h2 => by
    have hr : r.length = m := h1 r List.mem_cons_self
    have h1' : ∀ r ∈ l1, r.length = m := fun r' hr' => h1 r' (List.mem_cons_of_mem _ hr')
    have ih := packCols_append X m l1 l2 h1' h2
    rw [List.cons_append]
    simp only [packCols]
    rw [ih]
    apply List.ext_getElem
    · simp [hr, length_packCols X m l1 h1', length_packCols X m l2 h2]
    · intro k hk1 hk2
      simp only [List.getElem_zipWith, List.length_cons, pow_succ]
      ring

/-- Packing the columns chunk by chunk (`k` rows per chunk). -/
lemma packCols_flatten (X : ℤ) (m k : ℕ) : ∀ (chunks : List (List (List ℤ))),
    (∀ l ∈ chunks, l.length = k ∧ ∀ r ∈ l, r.length = m) →
    packCols X m chunks.flatten = packCols (X ^ k) m (chunks.map (packCols X m))
  | [], _ => by simp [packCols]
  | l :: rest, h => by
    have hl := h l List.mem_cons_self
    have hrest : ∀ l' ∈ rest, l'.length = k ∧ ∀ r ∈ l', r.length = m :=
      fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hflat : ∀ r ∈ rest.flatten, r.length = m := by
      intro r hr
      obtain ⟨l', hl', hr'⟩ := List.mem_flatten.mp hr
      exact (hrest l' hl').2 r hr'
    rw [List.flatten_cons, packCols_append X m l rest.flatten hl.2 hflat,
      packCols_flatten X m k rest hrest, hl.1]
    simp only [List.map_cons, packCols]

/-- Uniqueness of balanced base-`X` digits. -/
lemma eq_zero_of_sum_pow {X : ℤ} (hX : 0 < X) : ∀ (n : ℕ) (f : ℕ → ℤ),
    (∀ j < n, 2 * |f j| < X) → ∑ j ∈ Finset.range n, f j * X ^ j = 0 → ∀ j < n, f j = 0
  | 0, _, _, _ => fun j hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, hb, hs => by
    rw [Finset.sum_range_succ'] at hs
    simp only [pow_zero, mul_one] at hs
    have hrest : ∑ j ∈ Finset.range n, f (j + 1) * X ^ (j + 1)
        = X * ∑ j ∈ Finset.range n, f (j + 1) * X ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hrest] at hs
    have hf0 : f 0 = 0 := by
      have hdvd : X ∣ f 0 := ⟨-(∑ j ∈ Finset.range n, f (j + 1) * X ^ j), by linarith⟩
      obtain ⟨q, hq⟩ := hdvd
      have hb0 := hb 0 (Nat.succ_pos _)
      rw [hq, abs_mul, abs_of_pos hX] at hb0
      have : |q| < 1 := by nlinarith [abs_nonneg q]
      have : q = 0 := by
        rcases abs_lt.mp this with ⟨h1, h2⟩
        omega
      rw [hq, this, mul_zero]
    have hs' : ∑ j ∈ Finset.range n, f (j + 1) * X ^ j = 0 := by
      rw [hf0, add_zero] at hs
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd h hX.ne'
      · exact h
    have ih := eq_zero_of_sum_pow hX n (fun j => f (j + 1))
      (fun j hj => hb (j + 1) (Nat.succ_lt_succ hj)) hs'
    intro j hj
    cases j with
    | zero => exact hf0
    | succ j => exact ih j (Nat.lt_of_succ_lt_succ hj)

lemma rowsOK_spec (n : ℕ) (A : ℕ → ℕ → ℤ) (c X : ℤ) (PL : List ℤ) :
    ∀ (i : ℕ) (Ls Es : List (List ℤ)), rowsOK n A c X PL i Ls Es = true →
      Ls.length = Es.length ∧ ∀ k < Ls.length,
        rowOK n A c X PL (i + k) (Ls.getD k []) (Es.getD k []) = true
  | i, l :: ls, e :: es, h => by
    simp only [rowsOK, Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := rowsOK_spec n A c X PL (i + 1) ls es h.2
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := hr k (by simpa using hk)
      rw [show i + (k + 1) = i + 1 + k by omega, List.getD_cons_succ, List.getD_cons_succ]
      exact this
  | _, [], [], _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | _, [], _ :: _, h => by simp [rowsOK] at h
  | _, _ :: _, [], h => by simp [rowsOK] at h

lemma rowsBound_spec {n : ℕ} {b : ℤ} {Ls : List (List ℤ)} (h : rowsBoundOK n b Ls = true) :
    ∀ r ∈ Ls, r.length = n ∧ ∀ a ∈ r, |a| ≤ b := by
  intro r hr
  unfold rowsBoundOK at h
  have h' := List.all_eq_true.mp h r hr
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h'
  exact ⟨h'.1, fun a ha => by rw [← iabs_eq_abs]; exact of_decide_eq_true (h'.2 a ha)⟩

lemma shapeOK_spec {n : ℕ} {lam eps : ℤ} {Ls Es : List (List ℤ)} {PL : List ℤ}
    (h : shapeOK n lam eps Ls Es PL = true) :
    Ls.length = n ∧ Es.length = n ∧ PL.length = n ∧
      (∀ r ∈ Ls, r.length = n ∧ ∀ a ∈ r, |a| ≤ lam) ∧
      (∀ r ∈ Es, r.length = n ∧ ∀ a ∈ r, |a| ≤ eps) := by
  unfold shapeOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3, rowsBound_spec h4,
    rowsBound_spec h5⟩

lemma paramsOK_spec {n : ℕ} {c X lam eps alpha : ℤ} (h : paramsOK n c X lam eps alpha = true) :
    0 < c ∧ 0 ≤ alpha ∧ 0 ≤ eps ∧ 2 * (c * alpha + n * lam ^ 2 + eps) < X := by
  unfold paramsOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, ?_⟩
  have := of_decide_eq_true h4
  rw [sq]
  exact this

/-- Soundness of the block certificate. -/
theorem posSemidef_of_cert (n : ℕ) (A : ℕ → ℕ → ℤ) (hA : ∀ i j, A i j = A j i)
    (c X lam eps alpha : ℤ) (hAb : ∀ i < n, ∀ j < n, |A i j| ≤ alpha)
    (Ls Es : List (List ℤ)) (PL : List ℤ)
    (hpar : paramsOK n c X lam eps alpha = true)
    (hshape : shapeOK n lam eps Ls Es PL = true)
    (hcols : packCols X n Ls = PL)
    (hrows : rowsOK n A c X PL 0 Ls Es = true) :
    ((Matrix.of fun i j : Fin n => A i j).map (Int.cast : ℤ → ℂ)).PosSemidef := by
  obtain ⟨hc, halpha, heps, hX⟩ := paramsOK_spec hpar
  obtain ⟨hLl, hEl, hPl, hLr, hEr⟩ := shapeOK_spec hshape
  set Lm : ℕ → ℕ → ℤ := fun i k => (Ls.getD i []).getD k 0 with hLm
  set Em : ℕ → ℕ → ℤ := fun i j => (Es.getD i []).getD j 0 with hEm
  have hrowL : ∀ i < n, (Ls.getD i []).length = n ∧ ∀ a ∈ Ls.getD i [], |a| ≤ lam := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hLr _ (List.getElem_mem _)
  have hrowE : ∀ i < n, (Es.getD i []).length = n ∧ ∀ a ∈ Es.getD i [], |a| ≤ eps := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hEr _ (List.getElem_mem _)
  have hLb : ∀ i < n, ∀ k < n, |Lm i k| ≤ lam := by
    intro i hi k hk
    obtain ⟨hlen, hb⟩ := hrowL i hi
    simp only [hLm]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hb _ (List.getElem_mem _)
  have hEb : ∀ i < n, ∀ j < n, |Em i j| ≤ eps := by
    intro i hi j hj
    obtain ⟨hlen, hb⟩ := hrowE i hi
    simp only [hEm]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hb _ (List.getElem_mem _)
  have hlam : 0 ≤ lam ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inr h
    · exact Or.inl ((abs_nonneg _).trans (hLb 0 h 0 h))
  have hX0 : 0 < X := by
    have h1 : 0 ≤ c * alpha := mul_nonneg hc.le halpha
    have h2 : 0 ≤ (n : ℤ) * lam ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  -- columns
  obtain ⟨-, hPLk⟩ := packCols_spec X n Ls (fun r hr => (hLr r hr).1)
  rw [hcols, hLl] at hPLk
  -- rows
  obtain ⟨-, hrow⟩ := rowsOK_spec n A c X PL 0 Ls Es hrows
  rw [hLl] at hrow
  have hid : ∀ i < n, ∀ j < n, c * A i j = ∑ k ∈ Finset.range n, Lm i k * Lm j k + Em i j := by
    intro i hi
    have h := hrow i hi
    simp only [rowOK, Nat.zero_add, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hpk, -⟩ := h
    rw [packL_range, dotL_eq_sum _ _ (by rw [(hrowL i hi).1, hPl]), packL_eq_sum,
      (hrowL i hi).1, (hrowE i hi).1] at hpk
    have hpk' : ∑ j ∈ Finset.range n,
        (c * A i j - ∑ k ∈ Finset.range n, Lm i k * Lm j k - Em i j) * X ^ j = 0 := by
      have e1 : ∑ k ∈ Finset.range n, Lm i k * PL.getD k 0
          = ∑ j ∈ Finset.range n, (∑ k ∈ Finset.range n, Lm i k * Lm j k) * X ^ j := by
        rw [Finset.sum_congr rfl fun k hk => by rw [hPLk k (Finset.mem_range.mp hk)]]
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        simp only [hLm]
        ring
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [← e1]
      simp only [hLm, hEm] at hpk ⊢
      linarith
    intro j hj
    have hz := eq_zero_of_sum_pow hX0 n _ (fun j hj => by
      have b1 : |c * A i j| ≤ c * alpha := by
        rw [abs_mul, abs_of_pos hc]
        exact mul_le_mul_of_nonneg_left (hAb i hi j hj) hc.le
      have b2 : |∑ k ∈ Finset.range n, Lm i k * Lm j k| ≤ n * lam ^ 2 := by
        calc |∑ k ∈ Finset.range n, Lm i k * Lm j k|
            ≤ ∑ k ∈ Finset.range n, |Lm i k * Lm j k| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range n, lam ^ 2 := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk' := Finset.mem_range.mp hk
              rw [abs_mul, sq]
              exact mul_le_mul (hLb i hi k hk') (hLb j hj k hk') (abs_nonneg _)
                ((abs_nonneg _).trans (hLb i hi k hk'))
          _ = n * lam ^ 2 := by simp
      have b3 := hEb i hi j hj
      have := abs_sub (c * A i j - ∑ k ∈ Finset.range n, Lm i k * Lm j k) (Em i j)
      have := abs_sub (c * A i j) (∑ k ∈ Finset.range n, Lm i k * Lm j k)
      linarith) hpk' j hj
    linarith
  -- assemble
  have hsym : ∀ i < n, ∀ j < n, Em i j = Em j i := by
    intro i hi j hj
    have h1 := hid i hi j hj
    have h2 := hid j hj i hi
    rw [hA j i] at h2
    have : ∑ k ∈ Finset.range n, Lm i k * Lm j k = ∑ k ∈ Finset.range n, Lm j k * Lm i k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  have hdom : ∀ i < n, ∑ j ∈ Finset.range n, |Em i j| ≤ 2 * Em i i := by
    intro i hi
    have h := hrow i hi
    simp only [rowOK, Nat.zero_add, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨-, hd⟩ := h
    rw [sumAbs_eq_sum, (hrowE i hi).1] at hd
    simpa only [hEm] using hd
  refine posSemidef_of_gram (Matrix.of fun i j : Fin n => A i j)
    (Matrix.of fun i k : Fin n => Lm i k) (Matrix.of fun i j : Fin n => Em i j) c hc
    (fun i j => hsym i i.2 j j.2) (fun i => ?_) (fun i j => ?_)
  · simp only [Matrix.of_apply]
    rw [← Finset.sum_range (fun j => |Em i j|)]
    exact hdom i i.2
  · simp only [Matrix.of_apply]
    rw [← Finset.sum_range (fun k => Lm i k * Lm j k)]
    exact hid i i.2 j j.2

/-- The certificate soundness with the three checks combined into one kernel-checked Boolean. -/
theorem posSemidef_of_chk (n : ℕ) (A : ℕ → ℕ → ℤ) (hA : ∀ i j, A i j = A j i)
    (c X lam eps alpha : ℤ) (hAb : ∀ i < n, ∀ j < n, |A i j| ≤ alpha)
    (Ls Es : List (List ℤ)) (PL : List ℤ) (hcols : packCols X n Ls = PL)
    (h : (paramsOK n c X lam eps alpha && shapeOK n lam eps Ls Es PL && rowsOK n A c X PL 0 Ls Es)
      = true) :
    ((Matrix.of fun i j : Fin n => A i j).map (Int.cast : ℤ → ℂ)).PosSemidef := by
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact posSemidef_of_cert n A hA c X lam eps alpha hAb Ls Es PL h.1.1 h.1.2 hcols h.2

end GYNIProof
