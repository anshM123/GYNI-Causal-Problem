import GYNIUpper.UBMoment

/-!
# Upper bound, part 4: weak duality for Lüders-form strategies

For a Lüders-form strategy `(W, P, Q)` and a word table `wd : Fin n → List (Fin 2)` containing `[]`
(index `i0`) and `[x]` (index `i1 x`):

* `gam W P Q wd p q = Tr[W (|wd a', r⟩⟨wd a, r| ⊗ |wd b', s⟩⟨wd b, s|)]` for `p = (r, a, a')`,
  `q = (s, b, b')` (the moment matrix `Γ⁰` of `PROOF.md`, Lemma 3); `gam_gram`: it is the Gram
  matrix `⟨a r, b s| W |a' r, b' s⟩`, so each register block is positive semidefinite
  (`gam_block_psd`).
* `objT`: the objective tensor, `gyni_eq_obj`: `I_GYNI = Re ∑ objT p q Γ p q` (Lemma 3(d)).
* `gyni_le_of_dual`: if `Φ` has vanishing class sums for all classes `≠ []` (Alice and Bob) and
  every register block of `Φ - objT` is positive semidefinite, then
  `I_GYNI ≤ ∑_{p, q of class []} Φ p q`.
-/

namespace GYNIUpperBound

open Matrix GYNIProof Finset
open scoped ComplexOrder Kronecker

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- The moment matrix entry `Γ⁰ p q`. -/
noncomputable def gam (W : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
    ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ) (P : Fin 2 → Fin 2 → Matrix HA HA ℂ)
    (Q : Fin 2 → Fin 2 → Matrix HB HB ℂ) {n : ℕ} (wd : Fin n → List (Fin 2))
    (p q : Fin 2 × Fin n × Fin n) : ℂ :=
  (W * (pairChoi P (wd p.2.1) p.1 (wd p.2.2) p.1 ⊗ₖ pairChoi Q (wd q.2.1) q.1 (wd q.2.2) q.1)).trace

lemma gam_gram (W : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
    ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ) (P : Fin 2 → Fin 2 → Matrix HA HA ℂ)
    (Q : Fin 2 → Fin 2 → Matrix HB HB ℂ) {n : ℕ} (wd : Fin n → List (Fin 2))
    (p q : Fin 2 × Fin n × Fin n) :
    gam W P Q wd p q = star (kv (wvec P (wd p.2.1) p.1) (wvec Q (wd q.2.1) q.1)) ⬝ᵥ
      (W *ᵥ kv (wvec P (wd p.2.2) p.1) (wvec Q (wd q.2.2) q.1)) := by
  rw [gam, pairChoi, pairChoi, kron_vecMulVec, trace_mul_vecMulVec]

lemma gam_block_psd {W : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
    ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ} (hW : IsProcess W)
    (P : Fin 2 → Fin 2 → Matrix HA HA ℂ) (Q : Fin 2 → Fin 2 → Matrix HB HB ℂ) {n : ℕ}
    (wd : Fin n → List (Fin 2)) (r s : Fin 2) :
    (Matrix.of fun (i j : Fin n × Fin n) => gam W P Q wd (r, i.1, j.1) (s, i.2, j.2)).PosSemidef := by
  have h := gram_psd hW.1 (fun i : Fin n × Fin n => kv (wvec P (wd i.1) r) (wvec Q (wd i.2) s))
  have e : (Matrix.of fun (i j : Fin n × Fin n) => gam W P Q wd (r, i.1, j.1) (s, i.2, j.2)) =
      Matrix.of fun (i j : Fin n × Fin n) => star (kv (wvec P (wd i.1) r) (wvec Q (wd i.2) s)) ⬝ᵥ
        (W *ᵥ kv (wvec P (wd j.1) r) (wvec Q (wd j.2) s)) := by
    ext i j
    simp only [Matrix.of_apply]
    exact gam_gram W P Q wd _ _
  rw [e]
  exact h

/-! ## The objective -/

/-- Coefficient pattern: `1` at `i0`, `sgn` at `i1x`, `0` elsewhere. -/
def uC {n : ℕ} (i0 i1x : Fin n) (sgn : ℝ) (a : Fin n) : ℝ :=
  if a = i0 then 1 else if a = i1x then sgn else 0

/-- `(-1)^c`. -/
def sgn2 (c : Fin 2) : ℝ := if c = 0 then 1 else -1

/-- The GYNI objective tensor: `objT (r, a, a') (s, b, b') = ¼ u(a) u(a') v(b) v(b')` with
`u = u_{s|r}` (Alice, setting `r`, outcome `s`) and `v = u_{r|s}` (Bob, setting `s`, outcome `r`),
`u_{c|x} = ½ e_[] + ½ (-1)^c e_[x]`. -/
noncomputable def objT {n : ℕ} (i0 : Fin n) (i1 : Fin 2 → Fin n) (p q : Fin 2 × Fin n × Fin n) : ℝ :=
  (1 / 64) * (uC i0 (i1 p.1) (sgn2 q.1) p.2.1 * uC i0 (i1 p.1) (sgn2 q.1) p.2.2 *
    uC i0 (i1 q.1) (sgn2 p.1) q.2.1 * uC i0 (i1 q.1) (sgn2 p.1) q.2.2)

section Objective

variable {H : Type*} [Fintype H] [DecidableEq H]

lemma lvec_eq_sum {P : Fin 2 → Fin 2 → Matrix H H ℂ} (hP : IsProjMeas P) {n : ℕ}
    (wd : Fin n → List (Fin 2)) (i0 : Fin n) (i1 : Fin 2 → Fin n) (hi0 : wd i0 = [])
    (hi1 : ∀ x, wd (i1 x) = [x]) (x a : Fin 2) :
    lvec (P x a) x = ∑ α, (((1 / 2 : ℝ) * uC i0 (i1 x) (sgn2 a) α : ℝ) : ℂ) • wvec P (wd α) x := by
  have hne : i0 ≠ i1 x := by
    intro h
    have := hi1 x
    rw [← h, hi0] at this
    simp at this
  rw [Fintype.sum_eq_add i0 (i1 x) hne]
  · rw [lvec_eq hP, hi0, hi1]
    funext p
    simp only [uC, if_neg hne.symm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases a <;> simp [sgn2]
  · intro α hα
    simp [uC, hα.1, hα.2]

lemma lChoi_eq_sum {P : Fin 2 → Fin 2 → Matrix H H ℂ} (hP : IsProjMeas P) {n : ℕ}
    (wd : Fin n → List (Fin 2)) (i0 : Fin n) (i1 : Fin 2 → Fin n) (hi0 : wd i0 = [])
    (hi1 : ∀ x, wd (i1 x) = [x]) (x a : Fin 2) :
    lChoi P x a = ∑ α : Fin n × Fin n,
      ((((1 / 2 : ℝ) * uC i0 (i1 x) (sgn2 a) α.1) * ((1 / 2 : ℝ) * uC i0 (i1 x) (sgn2 a) α.2) : ℝ)
        : ℂ) • pairChoi P (wd α.1) x (wd α.2) x := by
  rw [lChoi, lvec_eq_sum hP wd i0 i1 hi0 hi1 x a]
  ext p q
  simp only [vecMulVec_apply, pairChoi, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_apply, Pi.smul_apply, Pi.star_apply, star_sum, star_smul, Finset.sum_mul,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  simp only [Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

end Objective

lemma trace_mul_kron_sum_sum {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI]
    [Fintype BO] [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO] (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    {κ κ' : Type*} [Fintype κ] [Fintype κ'] (c : κ → ℂ) (d : κ' → ℂ)
    (C : κ → Matrix (AI × AO) (AI × AO) ℂ) (D : κ' → Matrix (BI × BO) (BI × BO) ℂ) :
    (W * ((∑ k, c k • C k) ⊗ₖ (∑ l, d l • D l))).trace =
      ∑ k, ∑ l, c k * d l * (W * (C k ⊗ₖ D l)).trace := by
  rw [trace_mul_kron_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [trace_mul_kron_smul_left, trace_mul_kron_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Reindexing: registers first, then Alice's pair, then Bob's pair. -/
lemma sum_pq {n : ℕ} (f : Fin 2 × Fin n × Fin n → Fin 2 × Fin n × Fin n → ℂ) :
    ∑ p, ∑ q, f p q =
      ∑ x : Fin 2, ∑ y : Fin 2, ∑ α : Fin n × Fin n, ∑ β : Fin n × Fin n,
        f (x, α.1, α.2) (y, β.1, β.2) := by
  let e : (Fin 2 × Fin 2) × ((Fin n × Fin n) × (Fin n × Fin n)) ≃
      (Fin 2 × Fin n × Fin n) × (Fin 2 × Fin n × Fin n) :=
    { toFun := fun z => ((z.1.1, z.2.1.1, z.2.1.2), (z.1.2, z.2.2.1, z.2.2.2))
      invFun := fun w => ((w.1.1, w.2.1), ((w.1.2.1, w.1.2.2), (w.2.2.1, w.2.2.2)))
      left_inv := fun z => rfl
      right_inv := fun w => rfl }
  have h := Fintype.sum_equiv e (fun z => f (e z).1 (e z).2) (fun w => f w.1 w.2) (fun z => rfl)
  rw [Fintype.sum_prod_type' (f := f)] at h
  rw [← h]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Reindexing into the register blocks: rows `(a, b)`, columns `(a', b')`. -/
lemma sum_blocks {n : ℕ} (f : Fin 2 × Fin n × Fin n → Fin 2 × Fin n × Fin n → ℂ) :
    ∑ p, ∑ q, f p q =
      ∑ r : Fin 2, ∑ s : Fin 2, ∑ i : Fin n × Fin n, ∑ j : Fin n × Fin n,
        f (r, i.1, j.1) (s, i.2, j.2) := by
  let e : (Fin 2 × Fin 2) × ((Fin n × Fin n) × (Fin n × Fin n)) ≃
      (Fin 2 × Fin n × Fin n) × (Fin 2 × Fin n × Fin n) :=
    { toFun := fun z => ((z.1.1, z.2.1.1, z.2.2.1), (z.1.2, z.2.1.2, z.2.2.2))
      invFun := fun w => ((w.1.1, w.2.1), ((w.1.2.1, w.2.2.1), (w.1.2.2, w.2.2.2)))
      left_inv := fun z => rfl
      right_inv := fun w => rfl }
  have h := Fintype.sum_equiv e (fun z => f (e z).1 (e z).2) (fun w => f w.1 w.2) (fun z => rfl)
  rw [Fintype.sum_prod_type' (f := f)] at h
  rw [← h]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Lemma 3(d): the GYNI value is the objective of the moment matrix. -/
theorem gyni_eq_obj {W : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
    ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ}
    {P : Fin 2 → Fin 2 → Matrix HA HA ℂ} {Q : Fin 2 → Fin 2 → Matrix HB HB ℂ}
    (hP : IsProjMeas P) (hQ : IsProjMeas Q) {n : ℕ} (wd : Fin n → List (Fin 2)) (i0 : Fin n)
    (i1 : Fin 2 → Fin n) (hi0 : wd i0 = []) (hi1 : ∀ x, wd (i1 x) = [x]) :
    gyniValue W (lChoi P) (lChoi Q) =
      (∑ p, ∑ q, ((objT i0 i1 p q : ℝ) : ℂ) * gam W P Q wd p q).re := by
  have hxy : ∀ x y : Fin 2,
      ∑ α : Fin n × Fin n, ∑ β : Fin n × Fin n,
        ((objT i0 i1 (x, α.1, α.2) (y, β.1, β.2) : ℝ) : ℂ) * gam W P Q wd (x, α.1, α.2) (y, β.1, β.2)
      = (1 / 4 : ℂ) * (W * (lChoi P x y ⊗ₖ lChoi Q y x)).trace := by
    intro x y
    rw [lChoi_eq_sum hP wd i0 i1 hi0 hi1, lChoi_eq_sum hQ wd i0 i1 hi0 hi1,
      trace_mul_kron_sum_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [objT, gam]
    push_cast
    ring
  rw [sum_pq, Complex.re_sum, gyniValue, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hxy, prob, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]

/-! ## Weak duality -/

/-- **Weak duality** for Lüders-form strategies: a coefficient tensor `Φ` with vanishing class
sums (classes `≠ []`, both parties) such that `Φ - objT` is positive semidefinite on every register
block bounds the GYNI value by `∑_{p, q of class []} Φ p q`. -/
theorem gyni_le_of_dual {W : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
    ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ} (hW : IsProcess W)
    {P : Fin 2 → Fin 2 → Matrix HA HA ℂ} {Q : Fin 2 → Fin 2 → Matrix HB HB ℂ}
    (hP : IsProjMeas P) (hQ : IsProjMeas Q) {n : ℕ} (wd : Fin n → List (Fin 2)) (i0 : Fin n)
    (i1 : Fin 2 → Fin n) (hi0 : wd i0 = []) (hi1 : ∀ x, wd (i1 x) = [x])
    (Φ : Fin 2 × Fin n × Fin n → Fin 2 × Fin n × Fin n → ℝ)
    (hCA : ∀ t : List (Fin 2), t ≠ [] → ∀ q,
      ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n => clsW (wd p.2.1) (wd p.2.2) = t),
        Φ p q = 0)
    (hCB : ∀ u : List (Fin 2), u ≠ [] → ∀ p,
      ∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n => clsW (wd q.2.1) (wd q.2.2) = u),
        Φ p q = 0)
    (hPSD : ∀ r s : Fin 2, (Matrix.of fun (i j : Fin n × Fin n) =>
      (((Φ (r, i.1, j.1) (s, i.2, j.2) - objT i0 i1 (r, i.1, j.1) (s, i.2, j.2) : ℝ) : ℂ))).PosSemidef) :
    gyniValue W (lChoi P) (lChoi Q) ≤
      ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n => clsW (wd p.2.1) (wd p.2.2) = []),
        ∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n => clsW (wd q.2.1) (wd q.2.2) = []),
          Φ p q := by
  set β := ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n => clsW (wd p.2.1) (wd p.2.2) = []),
    ∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n => clsW (wd q.2.1) (wd q.2.2) = []),
      Φ p q with hβ
  have hv2 : ∑ p, ∑ q, ((Φ p q : ℝ) : ℂ) * gam W P Q wd p q = (β : ℂ) := by
    have h := v2_identity hW (fun p : Fin 2 × Fin n × Fin n => pairChoi P (wd p.2.1) p.1 (wd p.2.2) p.1)
      (fun q : Fin 2 × Fin n × Fin n => pairChoi Q (wd q.2.1) q.1 (wd q.2.2) q.1)
      (fun p => clsW (wd p.2.1) (wd p.2.2)) (fun q => clsW (wd q.2.1) (wd q.2.2))
      (fun t => (wordOp P t)ᵀ) (fun t => (wordOp Q t)ᵀ) [] [] (by simp [wordOp])
      (by simp [wordOp])
      (fun p => by rw [ptraceOut_pairChoi hP, if_pos rfl]; rfl)
      (fun q => by rw [ptraceOut_pairChoi hQ, if_pos rfl]; rfl)
      (fun p q => ((Φ p q : ℝ) : ℂ))
      (fun t ht q => by rw [← Complex.ofReal_sum, hCA t ht q, Complex.ofReal_zero])
      (fun u hu p => by rw [← Complex.ofReal_sum, hCB u hu p, Complex.ofReal_zero])
    rw [hβ]
    push_cast
    exact h
  have hpsd : 0 ≤ ∑ p, ∑ q, (((Φ p q - objT i0 i1 p q : ℝ)) : ℂ) * gam W P Q wd p q := by
    rw [sum_blocks]
    refine Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ => ?_
    have h := sum_mul_nonneg_of_psd (hPSD r s) (gam_block_psd hW P Q wd r s)
    simpa only [Matrix.of_apply] using h
  have hsplit : ∑ p, ∑ q, ((objT i0 i1 p q : ℝ) : ℂ) * gam W P Q wd p q =
      (β : ℂ) - ∑ p, ∑ q, (((Φ p q - objT i0 i1 p q : ℝ)) : ℂ) * gam W P Q wd p q := by
    rw [← hv2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    ring
  rw [gyni_eq_obj hP hQ wd i0 i1 hi0 hi1, hsplit, Complex.sub_re, Complex.ofReal_re]
  have := (Complex.nonneg_iff.mp hpsd).1
  linarith

end GYNIUpperBound
