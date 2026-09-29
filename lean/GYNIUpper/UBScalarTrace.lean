import GYNIUpper.UBBasic

/-!
# Upper bound, part 2: scalar-trace factorisation (Lemma 2 of `PROOF.md`)

`trace_kron_of_scalar`: if `W` is a process, `Tr_out C_A = λ_A 1` and `Tr_out C_B = λ_B 1`
(`C_A`, `C_B` need not be Hermitian), then `Tr[W (C_A ⊗ C_B)] = λ_A λ_B`.

Proof. `eq_of_cptp`: a function `f` that is additive, homogeneous and equal to `κ` on all CPTP Choi
matrices satisfies `f C = λ κ` whenever `Tr_out C = λ 1`. Indeed `D = |O|⁻¹ 1` (completely
depolarising channel) is CPTP; for Hermitian `K` with `Tr_out K = 0` the matrix `D + s K` is CPTP for
small `s > 0` (`exists_psd_perturb`, a crude bound on `xᴴ K x`), so `f K = 0`; a general `K` with
`Tr_out K = 0` is `H₁ + i H₂` with such Hermitian `H₁`, `H₂`; finally `C - λ D` has `Tr_out = 0`.
Apply this to `C ↦ Tr[W (C ⊗ N)]` (CPTP `N`, `κ = 1`) and then to `C ↦ Tr[W (C_A ⊗ C)]`
(`κ = λ_A`).
-/

namespace GYNIUpperBound

open Matrix GYNIProof
open scoped ComplexOrder Kronecker

section Ptrace

variable {I O : Type*} [Fintype O]

lemma ptraceOut_add (C D : Matrix (I × O) (I × O) ℂ) :
    ptraceOut (C + D) = ptraceOut C + ptraceOut D := by
  ext i j; simp [ptraceOut, Finset.sum_add_distrib]

lemma ptraceOut_smul (a : ℂ) (C : Matrix (I × O) (I × O) ℂ) :
    ptraceOut (a • C) = a • ptraceOut C := by
  ext i j; simp [ptraceOut, Finset.mul_sum]

lemma ptraceOut_sub (C D : Matrix (I × O) (I × O) ℂ) :
    ptraceOut (C - D) = ptraceOut C - ptraceOut D := by
  ext i j; simp [ptraceOut, Finset.sum_sub_distrib]

lemma ptraceOut_conjTranspose (C : Matrix (I × O) (I × O) ℂ) :
    ptraceOut Cᴴ = (ptraceOut C)ᴴ := by
  ext i j; simp [ptraceOut, conjTranspose_apply]

lemma ptraceOut_one [DecidableEq I] [DecidableEq O] :
    ptraceOut (1 : Matrix (I × O) (I × O) ℂ) = (Fintype.card O : ℂ) • 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ptraceOut, one_apply]
  · simp [ptraceOut, one_apply, h]

end Ptrace

section Perturb

variable {ι : Type*} [Fintype ι]

lemma norm_mul_norm_le_sum (x : ι → ℂ) (u v : ι) : ‖x u‖ * ‖x v‖ ≤ ∑ w, ‖x w‖ ^ 2 := by
  have hu : ‖x u‖ ^ 2 ≤ ∑ w, ‖x w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖x w‖ ^ 2) (fun w _ => sq_nonneg _) (Finset.mem_univ u)
  have hv : ‖x v‖ ^ 2 ≤ ∑ w, ‖x w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖x w‖ ^ 2) (fun w _ => sq_nonneg _) (Finset.mem_univ v)
  nlinarith [sq_nonneg (‖x u‖ - ‖x v‖), norm_nonneg (x u), norm_nonneg (x v)]

/-- `|xᴴ K x| ≤ (∑ ‖K u v‖) ∑ ‖xᵤ‖²`. -/
lemma norm_quad_le (K : Matrix ι ι ℂ) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (K *ᵥ x)‖ ≤ (∑ u, ∑ v, ‖K u v‖) * ∑ w, ‖x w‖ ^ 2 := by
  have e : star x ⬝ᵥ (K *ᵥ x) = ∑ u, ∑ v, star (x u) * K u v * x v := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have h := norm_mul_norm_le_sum x u v
  have hK := norm_nonneg (K u v)
  nlinarith [norm_nonneg (x u), norm_nonneg (x v)]

lemma re_dotProduct_self (x : ι → ℂ) : (star x ⬝ᵥ x).re = ∑ w, ‖x w‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

lemma im_dotProduct_self (x : ι → ℂ) : (star x ⬝ᵥ x).im = 0 := by
  simp only [dotProduct, Pi.star_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun w _ => ?_
  simp [Complex.mul_im]
  ring

/-- For Hermitian `K` and `d > 0`, `d⁻¹ 1 + s K` is positive semidefinite for some `s > 0`. -/
lemma exists_psd_perturb [DecidableEq ι] (K : Matrix ι ι ℂ) (hK : K.IsHermitian) {d : ℝ}
    (hd : 0 < d) : ∃ s : ℝ, 0 < s ∧ (((d⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) + (s : ℂ) • K).PosSemidef := by
  set c : ℝ := ∑ u, ∑ v, ‖K u v‖ with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => norm_nonneg _
  refine ⟨(d * (c + 1))⁻¹, by positivity, ?_⟩
  set s : ℝ := (d * (c + 1))⁻¹ with hs
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.add ?_ ?_
    · simp [IsHermitian, conjTranspose_smul]
    · simp [IsHermitian, conjTranspose_smul, hK.eq]
  · have hsplit : star x ⬝ᵥ ((((d⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) + (s : ℂ) • K) *ᵥ x)
        = ((d⁻¹ : ℝ) : ℂ) * (star x ⬝ᵥ x) + (s : ℂ) * (star x ⬝ᵥ (K *ᵥ x)) := by
      rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
        dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [hsplit, Complex.nonneg_iff]
    have him : (star x ⬝ᵥ (K *ᵥ x)).im = 0 := hK.im_star_dotProduct_mulVec_self x
    constructor
    · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, re_dotProduct_self]
      have hq := norm_quad_le K x
      have hre : -(c * ∑ w, ‖x w‖ ^ 2) ≤ (star x ⬝ᵥ (K *ᵥ x)).re := by
        have := Complex.abs_re_le_norm (star x ⬝ᵥ (K *ᵥ x))
        have := neg_abs_le (star x ⬝ᵥ (K *ᵥ x)).re
        linarith
      have hS : 0 ≤ ∑ w, ‖x w‖ ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
      have hs0 : 0 < s := by positivity
      have key : s * (c * ∑ w, ‖x w‖ ^ 2) ≤ d⁻¹ * ∑ w, ‖x w‖ ^ 2 := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hS
        rw [hs, mul_inv, mul_assoc]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [inv_mul_le_one₀ (by positivity)]
        linarith
      nlinarith
    · rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, im_dotProduct_self, him]
      ring

end Perturb

section Spanning

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- The completely depolarising channel `|O|⁻¹ 1`. -/
noncomputable def depol : Matrix (I × O) (I × O) ℂ := (((Fintype.card O : ℝ)⁻¹ : ℝ) : ℂ) • 1

omit [Fintype I] in
lemma ptraceOut_depol [Nonempty O] : ptraceOut (depol : Matrix (I × O) (I × O) ℂ) = 1 := by
  rw [depol, ptraceOut_smul, ptraceOut_one, smul_smul]
  have h : (Fintype.card O : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  rw [inv_mul_cancel₀ h, one_smul]

/-- A function that is additive, homogeneous and equal to `κ` on all CPTP Choi matrices takes the
value `λ κ` at every `C` with `Tr_out C = λ 1`. -/
theorem eq_of_cptp {f : Matrix (I × O) (I × O) ℂ → ℂ}
    (hadd : ∀ C D, f (C + D) = f C + f D) (hsmul : ∀ (a : ℂ) C, f (a • C) = a * f C)
    {κ : ℂ} (hf : ∀ M, IsCPTP M → f M = κ) {C : Matrix (I × O) (I × O) ℂ} {l : ℂ}
    (hC : ptraceOut C = l • 1) : f C = l * κ := by
  have hf0 : f 0 = 0 := by simpa using hsmul 0 0
  have hsub : ∀ C D, f (C - D) = f C - f D := by
    intro C D
    have := hadd (C - D) D
    rw [sub_add_cancel] at this
    rw [this]; ring
  rcases isEmpty_or_nonempty O with hO | hO
  · -- degenerate case: no output
    have hC0 : C = 0 := by ext p; exact (IsEmpty.false p.2).elim
    rw [hC0, hf0]
    rcases isEmpty_or_nonempty I with hI | hI
    · have h0 : IsCPTP (0 : Matrix (I × O) (I × O) ℂ) :=
        ⟨PosSemidef.zero, by ext i; exact (IsEmpty.false i).elim⟩
      rw [← hf 0 h0, hf0, mul_zero]
    · obtain ⟨i⟩ := hI
      have := congrFun (congrFun hC i) i
      simp [ptraceOut] at this
      rw [← this, zero_mul]
  · -- the trace-annihilating Hermitian case
    have hcard : (0 : ℝ) < Fintype.card O := by exact_mod_cast Fintype.card_pos
    have hD : IsCPTP (depol : Matrix (I × O) (I × O) ℂ) := by
      refine ⟨?_, ptraceOut_depol⟩
      exact PosSemidef.one.smul (by positivity)
    have hherm : ∀ K : Matrix (I × O) (I × O) ℂ, K.IsHermitian → ptraceOut K = 0 → f K = 0 := by
      intro K hK hKt
      obtain ⟨s, hs, hpsd⟩ := exists_psd_perturb K hK (d := (Fintype.card O : ℝ)) hcard
      have hM : IsCPTP (depol + (s : ℂ) • K) := by
        refine ⟨by simpa [depol] using hpsd, ?_⟩
        rw [ptraceOut_add, ptraceOut_smul, hKt, smul_zero, add_zero, ptraceOut_depol]
      have h1 := hf _ hM
      rw [hadd, hsmul, hf _ hD] at h1
      have : (s : ℂ) * f K = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast h) hs.ne'
      · exact h
    have hta : ∀ K : Matrix (I × O) (I × O) ℂ, ptraceOut K = 0 → f K = 0 := by
      intro K hK
      have hKh : ptraceOut Kᴴ = 0 := by rw [ptraceOut_conjTranspose, hK, conjTranspose_zero]
      have hc : star (-Complex.I / 2) = Complex.I / 2 := by
        rw [star_div₀, star_neg, Complex.star_def, Complex.conj_I, neg_neg, map_ofNat]
      have h1 : f ((1 / 2 : ℂ) • (K + Kᴴ)) = 0 := by
        refine hherm _ ?_ ?_
        · ext p q
          simp only [conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
            star_mul', star_add, star_star]
          norm_num
          ring
        · rw [ptraceOut_smul, ptraceOut_add, hK, hKh, add_zero, smul_zero]
      have h2 : f ((-Complex.I / 2) • (K - Kᴴ)) = 0 := by
        refine hherm _ ?_ ?_
        · ext p q
          simp only [conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
            star_mul', star_sub, star_star, hc]
          ring
        · rw [ptraceOut_smul, ptraceOut_sub, hK, hKh, sub_zero, smul_zero]
      have hsplit : K = (1 / 2 : ℂ) • (K + Kᴴ) + Complex.I • ((-Complex.I / 2) • (K - Kᴴ)) := by
        ext p q
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        have : Complex.I * (-Complex.I / 2 * (K p q - Kᴴ p q)) = (1 / 2) * (K p q - Kᴴ p q) := by
          rw [← mul_assoc, mul_div_assoc', mul_neg, Complex.I_mul_I]; ring
        rw [this]; ring
      rw [hsplit, hadd, hsmul Complex.I, h1, h2]; ring
    have hmain : ptraceOut (C - l • depol) = 0 := by
      rw [ptraceOut_sub, ptraceOut_smul, ptraceOut_depol, hC, sub_self]
    have := hta _ hmain
    rw [hsub, hsmul, hf _ hD] at this
    linear_combination this

end Spanning

section Factor

variable {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]

lemma trace_mul_kron_add_left (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (C D : Matrix (AI × AO) (AI × AO) ℂ) (E : Matrix (BI × BO) (BI × BO) ℂ) :
    (W * ((C + D) ⊗ₖ E)).trace = (W * (C ⊗ₖ E)).trace + (W * (D ⊗ₖ E)).trace := by
  rw [add_kronecker, Matrix.mul_add, trace_add]

lemma trace_mul_kron_smul_left (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (a : ℂ) (C : Matrix (AI × AO) (AI × AO) ℂ) (E : Matrix (BI × BO) (BI × BO) ℂ) :
    (W * ((a • C) ⊗ₖ E)).trace = a * (W * (C ⊗ₖ E)).trace := by
  rw [smul_kronecker, Matrix.mul_smul, trace_smul, smul_eq_mul]

lemma trace_mul_kron_add_right (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (E : Matrix (AI × AO) (AI × AO) ℂ) (C D : Matrix (BI × BO) (BI × BO) ℂ) :
    (W * (E ⊗ₖ (C + D))).trace = (W * (E ⊗ₖ C)).trace + (W * (E ⊗ₖ D)).trace := by
  rw [kronecker_add, Matrix.mul_add, trace_add]

lemma trace_mul_kron_smul_right (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (a : ℂ) (E : Matrix (AI × AO) (AI × AO) ℂ) (C : Matrix (BI × BO) (BI × BO) ℂ) :
    (W * (E ⊗ₖ (a • C))).trace = a * (W * (E ⊗ₖ C)).trace := by
  rw [kronecker_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

variable [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

/-- **Lemma 2** (scalar-trace factorisation). -/
theorem trace_kron_of_scalar {W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ}
    (hW : IsProcess W) {CA : Matrix (AI × AO) (AI × AO) ℂ} {CB : Matrix (BI × BO) (BI × BO) ℂ}
    {lA lB : ℂ} (hA : ptraceOut CA = lA • 1) (hB : ptraceOut CB = lB • 1) :
    (W * (CA ⊗ₖ CB)).trace = lA * lB := by
  have step1 : ∀ N : Matrix (BI × BO) (BI × BO) ℂ, IsCPTP N → (W * (CA ⊗ₖ N)).trace = lA := by
    intro N hN
    have := eq_of_cptp (f := fun C => (W * (C ⊗ₖ N)).trace)
      (fun C D => trace_mul_kron_add_left W C D N) (fun a C => trace_mul_kron_smul_left W a C N)
      (κ := 1) (fun M hM => hW.2 M N hM hN) hA
    simpa using this
  have := eq_of_cptp (f := fun C => (W * (CA ⊗ₖ C)).trace)
    (fun C D => trace_mul_kron_add_right W CA C D) (fun a C => trace_mul_kron_smul_right W a CA C)
    (κ := lA) step1 hB
  rw [this, mul_comm]

end Factor

end GYNIUpperBound
