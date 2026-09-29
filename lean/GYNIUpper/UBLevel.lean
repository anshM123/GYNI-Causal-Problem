import GYNIUpper.UBDuality
import GYNIUpper.UBClass

/-!
# Upper bound, part 8: the bound of one level from the kernel-checked data

`gyni_le_level`: suppose the packed data of a level (`blk r s` = rows of `Φ` of block `(r, s)`,
`fac r s`, `col r s` = factor rows and packed columns) pass all kernel checks of `UBCheck`. Then
every Lüders-form strategy satisfies `I_GYNI ≤ betaNum / den`.

The data define `Φ (r, a, a') (s, b, b') = (dig bA R (a n + b ↦ row) (a' n + b') - oA) / den` and the
objective tensor `objE / den = objT`; the class checks give the vanishing class sums, the row checks
give positive semidefiniteness of `Φ - objT` on each register block, and the trace check gives
`∑_{p, q of class []} Φ p q = betaNum / den`. Then `gyni_le_of_dual` applies.
-/

namespace GYNIUpperBound

open Matrix GYNIProof Finset
open scoped ComplexOrder Kronecker

/-! ## Small lemmas about the data -/

theorem uSgn_abs_le (i0 i1x : ℕ) (sgn : ℤ) (hs : sgn = 1 ∨ sgn = -1) (a : ℕ) :
    |uSgn i0 i1x sgn a| ≤ 1 := by
  unfold uSgn
  split_ifs <;> rcases hs with rfl | rfl <;> simp

theorem objE_abs_le (n i0 : ℕ) (i1 : ℕ → ℕ) {od : ℤ} (hod : 0 ≤ od) (r s i j : ℕ) :
    |objE n i0 i1 od r s i j| ≤ od := by
  unfold objE
  have hsA : (if s = 0 then (1 : ℤ) else -1) = 1 ∨ (if s = 0 then (1 : ℤ) else -1) = -1 := by
    split_ifs <;> simp
  have hsB : (if r = 0 then (1 : ℤ) else -1) = 1 ∨ (if r = 0 then (1 : ℤ) else -1) = -1 := by
    split_ifs <;> simp
  rw [abs_mul, abs_of_nonneg hod]
  have h1 := uSgn_abs_le i0 (i1 r) _ hsA (i / n)
  have h2 := uSgn_abs_le i0 (i1 r) _ hsA (j / n)
  have h3 := uSgn_abs_le i0 (i1 s) _ hsB (i % n)
  have h4 := uSgn_abs_le i0 (i1 s) _ hsB (j % n)
  have hp : |uSgn i0 (i1 r) (if s = 0 then 1 else -1) (i / n) *
      uSgn i0 (i1 r) (if s = 0 then 1 else -1) (j / n) *
      uSgn i0 (i1 s) (if r = 0 then 1 else -1) (i % n) *
      uSgn i0 (i1 s) (if r = 0 then 1 else -1) (j % n)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_mul]
    have := mul_le_one₀ (mul_le_one₀ (mul_le_one₀ h1 (abs_nonneg _) h2) (abs_nonneg _) h3)
      (abs_nonneg _) h4
    exact this
  nlinarith [abs_nonneg (uSgn i0 (i1 r) (if s = 0 then 1 else -1) (i / n) *
      uSgn i0 (i1 r) (if s = 0 then 1 else -1) (j / n) *
      uSgn i0 (i1 s) (if r = 0 then 1 else -1) (i % n) *
      uSgn i0 (i1 s) (if r = 0 then 1 else -1) (j % n))]

theorem objE_symm (n i0 : ℕ) (i1 : ℕ → ℕ) (od : ℤ) (r s i j : ℕ) :
    objE n i0 i1 od r s i j = objE n i0 i1 od r s j i := by
  unfold objE; ring

/-- `∑_{a, b < n} g (a n + b) = ∑_{i < n n} g i`. -/
theorem sum_pair_eq {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ x : Fin n × Fin n, g (x.1 * n + x.2) = ∑ i ∈ range (n * n), g i := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv finProdFinEquiv _ _ fun x => ?_
  simp only [finProdFinEquiv_apply_val]
  congr 1; ring

/-- The sum over pairs of class `[]` is the diagonal sum. -/
theorem sum_filter_nil {n nc te L : ℕ} {cw : List (List (Fin 2))} {tab : List (List ℕ)}
    (htab : tabOK (wordAt L) n cw tab = true) (hlen : cw.length = nc)
    (hte : cw.getD te [] = []) (hsh : tabShapeOK n nc te tab = true) (hte' : te < nc)
    {M : Type*} [AddCommMonoid M] (f : Fin 2 × Fin n × Fin n → M) :
    ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n =>
        clsW (wordAt L p.2.1) (wordAt L p.2.2) = []), f p =
      ∑ r : Fin 2, ∑ a : Fin n, f (r, a, a) := by
  rw [Finset.sum_filter]
  have e : ∀ p : Fin 2 × Fin n × Fin n,
      (if clsW (wordAt L p.2.1) (wordAt L p.2.2) = [] then f p else 0) =
        if p.2.1 = p.2.2 then f p else 0 := by
    intro p
    have := cls_nil_iff htab hlen hte hsh hte' p.2.1.2 p.2.2.2
    simp only [this, Fin.val_inj]
  rw [Finset.sum_congr rfl fun p _ => e p]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp

end GYNIUpperBound
