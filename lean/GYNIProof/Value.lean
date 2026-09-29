import GYNIProof.Model
import GYNIProof.ValueQ

/-!
# The instruments and the exact GYNI value

Instruments (Alice = Bob): in label block `l`, `P_{0|x} = |φ_l^x⟩⟨φ_l^x|` with
`φ_l^x = (c_l, (-1)^{x+1} s_l)` (rational, `c_l² + s_l² = 1`), `P_{1|x} = 1 - P_{0|x}`; Lüders
instrument writing the setting into the register: Choi matrix `M_{a|x} = |v⟩⟨v|`,
`v[(i, (o, r))] = P_{a|x}[o, i] δ_{r,x}` (`vvec`, `Mq`, `Mc`).

The value `Tr[W (M_{y|x} ⊗ M_{x|y})]` is computed from the general trace formula
`trace_formW`; the quadratic forms `⟨v| H(i,i') |v⟩` only involve the class `13 x` of `v`
(`vvec_support`, `sum_class`) and are evaluated with integer vectors `vtab = LAM · v`.
The definitions `cS`, `sS`, `phi`, `P0`, `Pm`, `vvec` and all kernel checks are in the
Mathlib-free files `ValueQ.lean` and `ValueCore.lean`; this file converts `Finset` sums to their
written-out forms (`sumR8_eq`, `sumR2_eq`).
-/

namespace GYNIProof

open Matrix
open scoped ComplexOrder Kronecker

lemma sumR8_eq (f : Fin 8 → ℚ) : ∑ i, f i = sumR8 f := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

lemma sumR2_eq (f : Fin 2 → ℚ) : ∑ i, f i = sumR2 f := by
  simp only [Fin.sum_univ_two, sumR2]

/-- Choi matrix `|v_{a,x}⟩⟨v_{a,x}|` over `ℚ` (setting `x`, outcome `a`). -/
def Mq (x a : Fin 2) : Matrix Pt Pt ℚ := vecMulVec (vvec a x) (vvec a x)

/-- The instrument (setting `x`, outcome `a`). -/
noncomputable def Mc (x a : Fin 2) : Matrix Pt Pt ℂ := (Mq x a).map (Rat.castHom ℂ)

lemma ptrace_vvec' (x : Fin 2) (i j : Fin 8) :
    (∑ a : Fin 2, ∑ o : Fin 8 × Fin 2, vvec a x (i, o) * vvec a x (j, o))
      = if i = j then 1 else 0 := by
  rw [← ptrace_vvec x i j]
  simp only [Fintype.sum_prod_type, sumR8_eq, sumR2_eq]

theorem Mc_instrument : IsInstrument Mc := by
  intro x
  refine ⟨fun a => ?_, ?_⟩
  · have : Mc x a = vecMulVec (fun b => ((vvec a x b : ℚ) : ℂ))
        (star fun b => ((vvec a x b : ℚ) : ℂ)) := by
      ext b b'
      simp [Mc, Mq, vecMulVec_apply]
    rw [this]
    exact posSemidef_vecMulVec_self_star _
  · ext i j
    have h := congrArg (Rat.cast : ℚ → ℂ) (ptrace_vvec' x i j)
    push_cast at h
    simp only [ptraceOut, Matrix.of_apply, Matrix.sum_apply, Mc, Mq, Matrix.map_apply,
      vecMulVec_apply, Rat.coe_castHom]
    rw [Finset.sum_comm, Matrix.one_apply]
    push_cast
    rw [h]
    split_ifs <;> simp

/-! ## Reduction of the quadratic forms to one class -/

lemma sum_class (c : ℕ) (hc : c < 26) (g : Pt → ℚ) (hg : ∀ b, clsN b ≠ c → g b = 0) :
    ∑ b, g b = ∑ p ∈ Finset.range (szN c), g (embN c p) := by
  rw [← Equiv.sum_comp ePt g, Fintype.sum_sigma, Finset.sum_eq_single (⟨c, hc⟩ : Fin 26)]
  · exact Fin.sum_univ_eq_sum_range (fun p => g (embN c p)) (szN c)
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun p _ => hg _ ?_
    rw [clsN_ePt]
    exact fun e => hc' (Fin.ext e)
  · simp

lemma vvec_support' (a x : Fin 2) (b : Pt) (h : clsN b ≠ 13 * x.val) : vvec a x b = 0 := by
  obtain ⟨i, o, r⟩ := b
  exact vvec_support a x i o r h

/-- `vtab`, `hInt`, `Htab`, `sum16` and the kernel checks `hInt_tab_s_a` are in `ValueCore.lean`. -/
lemma sum16_eq (f : ℕ → ℤ) : sum16 f = ∑ p ∈ Finset.range 16, f p := by
  simp only [sum16, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

lemma trace_HA_Mq (i i' : Fin 8) (s a : Fin 2) :
    (HA i i' * Mq s a).trace = kappa * (hInt i i' s a : ℚ) / (LAM : ℚ) ^ 2 := by
  have hc : 13 * s.val < 26 := by omega
  have hsz : szN (13 * s.val) = 16 := by fin_cases s <;> rfl
  have e1 : (HA i i' * Mq s a).trace
      = ∑ b, (∑ b', kappa * (HintF i i' b b' : ℚ) * vvec a s b') * vvec a s b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, HA, Mq, Matrix.of_apply,
      vecMulVec_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [e1, sum_class _ hc _ (fun b hb => by rw [vvec_support' a s b hb, mul_zero]), hsz]
  have e2 : ∀ p, (∑ b', kappa * (HintF i i' (embN (13 * s.val) p) b' : ℚ) * vvec a s b')
      = ∑ p' ∈ Finset.range 16, kappa * (HintF i i' (embN (13 * s.val) p)
          (embN (13 * s.val) p') : ℚ) * vvec a s (embN (13 * s.val) p') := by
    intro p
    rw [sum_class _ hc _ (fun b hb => by rw [vvec_support' a s b hb, mul_zero]), hsz]
  simp_rw [e2]
  unfold hInt
  by_cases hl : lab i = lab i'
  · rw [if_pos hl]
    simp only [sum16_eq]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    rw [vvec_tab a s p (Finset.mem_range.mp hp), vvec_tab a s p' (Finset.mem_range.mp hp')]
    have hL : (LAM : ℚ) ≠ 0 := by norm_num [LAM]
    field_simp
  · rw [if_neg hl]
    simp [HintF_zero' hl]

/-- The value of one term `Tr[W (M_{y|x} ⊗ M_{x|y})]` (over `ℚ`), reduced. -/
def trRed (x y : Fin 2) : ℚ :=
  1 / 64 * (Mq x y).trace * (Mq y x).trace
    + (∑ i : Fin 8, ∑ i' : Fin 8, ptraceOut (Mq x y) i' i * (kappa * (hInt i i' y x : ℚ) / (LAM : ℚ) ^ 2)
      + ∑ j : Fin 8, ∑ j' : Fin 8, kappa * (hInt j j' x y : ℚ) / (LAM : ℚ) ^ 2 * ptraceOut (Mq y x) j' j)

lemma trace_Wq (x y : Fin 2) : (Wq * (Mq x y ⊗ₖ Mq y x)).trace = trRed x y := by
  rw [Wq, trace_formW]
  simp only [trRed, trace_HA_Mq]

/-- The reduced value `¼ ∑_{x,y} Tr[W (M_{y|x} ⊗ M_{x|y})]`. -/
def valRed : ℚ := 1 / 4 * ∑ x : Fin 2, ∑ y : Fin 2, trRed x y

/-! ## Exact evaluation (kernel checks in `ValueQ.lean` / `ValueCore.lean`) -/

lemma trace_Mq (x a : Fin 2) : (Mq x a).trace = traceQ x a := by
  simp only [Matrix.trace, Matrix.diag, Mq, vecMulVec_apply, Fintype.sum_prod_type, sumR8_eq,
    sumR2_eq, traceQ]

lemma ptrace_Mq (x a : Fin 2) (i' i : Fin 8) : ptraceOut (Mq x a) i' i = ptraceQ x a i' i := by
  simp only [ptraceOut, Matrix.of_apply, Mq, vecMulVec_apply, Fintype.sum_prod_type, sumR8_eq,
    sumR2_eq, ptraceQ]

lemma ptraceQ_tab : ∀ x a : Fin 2, ∀ i' i : Fin 8, ptraceQ x a i' i = Ktab x a i' i :=
  Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨ptraceQ_tab_0_0, ptraceQ_tab_0_1⟩,
    Fin.forall_fin_two.mpr ⟨ptraceQ_tab_1_0, ptraceQ_tab_1_1⟩⟩

lemma hInt_tab : ∀ s a : Fin 2, ∀ i i' : Fin 8, hInt i i' s a = Htab s a i i' :=
  Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨hInt_tab_0_0, hInt_tab_0_1⟩,
    Fin.forall_fin_two.mpr ⟨hInt_tab_1_0, hInt_tab_1_1⟩⟩

lemma kappa_eq : kappa = kappaQ := by
  norm_num [kappa, kappaQ]

lemma trRed_eq_tab (x y : Fin 2) : trRed x y = trTabQ x y := by
  simp only [trRed, trTabQ, trace_Mq, traceQ_tab, ptrace_Mq, ptraceQ_tab, hInt_tab, kappa_eq,
    sumR8_eq, sq]

theorem valRed_eq : valRed = (valNum : ℚ) / valDen := by
  rw [valRed, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, trRed_eq_tab, trRed_eq_tab,
    trRed_eq_tab, trRed_eq_tab, trTabQ_0_0, trTabQ_0_1, trTabQ_1_0, trTabQ_1_1, trTab_sum]

lemma kron_map {m n : Type*} (f : ℚ →+* ℂ) (A : Matrix m m ℚ) (B : Matrix n n ℚ) :
    (A ⊗ₖ B).map f = A.map f ⊗ₖ B.map f := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.map_apply, Matrix.kroneckerMap_apply, map_mul]

lemma trace_map' {n : Type*} [Fintype n] (f : ℚ →+* ℂ) (A : Matrix n n ℚ) :
    (A.map f).trace = f A.trace := by
  simp [Matrix.trace, map_sum]

lemma trace_Wc (x y : Fin 2) :
    (Wc * (Mc x y ⊗ₖ Mc y x)).trace = (Rat.castHom ℂ) (trRed x y) := by
  rw [← trace_Wq, ← trace_map', Matrix.map_mul, kron_map]
  rfl

lemma prob_eq (x y : Fin 2) : prob Wc Mc Mc y x x y = (trRed x y : ℝ) := by
  unfold prob
  rw [trace_Wc, Rat.coe_castHom, Complex.ratCast_re]

theorem gyniValue_eq : gyniValue Wc Mc Mc = ((valNum : ℚ) / valDen : ℚ) := by
  unfold gyniValue
  simp only [prob_eq]
  rw [← valRed_eq, valRed]
  push_cast
  ring

end GYNIProof
