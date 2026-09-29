import GYNIUpper.LuedersDilation

/-!
# Lüders normal form, part 3: the lifted process and the main theorem

Lemma 1 of `PROOF.md` ("Lüders normal form with setting registers"): for every process `W` and
instruments `M`, `N` (settings and outcomes in `Fin 2`) there are projective measurements `P`, `Q`
on some `ℂ^nA`, `ℂ^nB` and a process `W'` on
`(ℂ^nA ⊗ (ℂ^nA ⊗ ℂ²)) ⊗ (ℂ^nB ⊗ (ℂ^nB ⊗ ℂ²))`, block diagonal in the two setting registers, such
that `W'` with the Lüders instruments `ρ ↦ P_{a|x} ρ P_{a|x} ⊗ |x⟩⟨x|` and
`σ ↦ Q_{b|y} σ Q_{b|y} ⊗ |y⟩⟨y|` has the same correlations as `W` with `M`, `N`
(`lueders_normal_form`). `lueders_normal_form_choi`
states the same with the Lüders instruments written out as Choi matrices (`choiMatrix`) and with
the block diagonality in the projector form `W' = ∑_{r,s} Π_{rs} W' Π_{rs}` (`eq_sum_registerProj`).

Proof. `LuedersDilation.lean` gives Lüders dilations `(J_A, P, T_A)` of `M` and `(J_B, Q, T_B)`
of `N`. Let `Φ_A = choiMap J_A (regKraus T_A)` be the Choi-level form of `F ↦ 𝓣_A ∘ F ∘ 𝓙_A`
(and likewise `Φ_B`), and `W' = (Φ_A† ⊗ Φ_B†)(W)` (`luedersProcess`). Then
`Tr[W' (C ⊗ D)] = Tr[W (Φ_A C ⊗ Φ_B D)]` (`trace_liftProcess_mul`), `Φ_A` maps CPTP Choi matrices to
CPTP Choi matrices (`isCPTP_choiMap`), and `Φ_A` maps the Lüders Choi matrices to `M x a`
(`choiMap_luedersInstr`). Every Kraus operator of `Φ_A` contains the factor `⟨x|` on the register,
which gives the block diagonality (`liftProcess_apply_eq_zero`).
-/

set_option linter.unusedSectionVars false

namespace GYNIUpper

open Matrix GYNIProof
open scoped ComplexOrder Kronecker

/-! ### The lifted process `(Φ_A† ⊗ Φ_B†)(W)` -/

section Lift

variable {SA SB UA UB ιA ιB : Type*} [Fintype SA] [Fintype SB] [Fintype UA] [Fintype UB]
  [Fintype ιA] [Fintype ιB]

/-- `∑_{i,j} (XA i ⊗ XB j)ᴴ W (XA i ⊗ XB j)`: the Hilbert–Schmidt adjoint of
`C ⊗ D ↦ (∑ i, XA i C (XA i)ᴴ) ⊗ (∑ j, XB j D (XB j)ᴴ)`, applied to `W`. -/
def liftProcess (W : Matrix (SA × SB) (SA × SB) ℂ) (XA : ιA → Matrix SA UA ℂ)
    (XB : ιB → Matrix SB UB ℂ) : Matrix (UA × UB) (UA × UB) ℂ :=
  ∑ i, ∑ j, (XA i ⊗ₖ XB j)ᴴ * W * (XA i ⊗ₖ XB j)

lemma posSemidef_liftProcess {W : Matrix (SA × SB) (SA × SB) ℂ} (hW : W.PosSemidef)
    (XA : ιA → Matrix SA UA ℂ) (XB : ιB → Matrix SB UB ℂ) : (liftProcess W XA XB).PosSemidef :=
  posSemidef_sum _ fun _ _ => posSemidef_sum _ fun _ _ => hW.conjTranspose_mul_mul_same _

/-- Duality: `Tr[W' (C ⊗ D)] = Tr[W ((∑ i, XA i C (XA i)ᴴ) ⊗ (∑ j, XB j D (XB j)ᴴ))]`. -/
lemma trace_liftProcess_mul (W : Matrix (SA × SB) (SA × SB) ℂ) (XA : ιA → Matrix SA UA ℂ)
    (XB : ιB → Matrix SB UB ℂ) (C : Matrix UA UA ℂ) (D : Matrix UB UB ℂ) :
    (liftProcess W XA XB * (C ⊗ₖ D)).trace =
      (W * ((∑ i, XA i * C * (XA i)ᴴ) ⊗ₖ (∑ j, XB j * D * (XB j)ᴴ))).trace := by
  rw [kronecker_sum_left, Matrix.mul_sum, Matrix.trace_sum, liftProcess, Matrix.sum_mul,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kronecker_sum_right, Matrix.mul_sum, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_kronecker_mul, mul_kronecker_mul, ← conjTranspose_kronecker, trace_mul_sandwich]

/-- Block structure: if every column `t` of `XA i` (resp. `XB j`) with label `fA t ≠ rA i`
(resp. `fB t ≠ rB j`) vanishes, the lifted process vanishes between different labels. -/
lemma liftProcess_apply_eq_zero (W : Matrix (SA × SB) (SA × SB) ℂ) (XA : ιA → Matrix SA UA ℂ)
    (XB : ιB → Matrix SB UB ℂ) (fA : UA → Fin 2) (fB : UB → Fin 2) (rA : ιA → Fin 2)
    (rB : ιB → Fin 2) (hA : ∀ i u t, fA t ≠ rA i → XA i u t = 0)
    (hB : ∀ j u t, fB t ≠ rB j → XB j u t = 0) (p q : UA × UB)
    (hpq : fA p.1 ≠ fA q.1 ∨ fB p.2 ≠ fB q.2) : liftProcess W XA XB p q = 0 := by
  simp only [liftProcess, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hcol : (∀ u, (XA i ⊗ₖ XB j) u p = 0) ∨ (∀ v, (XA i ⊗ₖ XB j) v q = 0) := by
    rcases hpq with h | h
    · by_cases h1 : fA p.1 = rA i
      · right
        intro v
        simp [hA i v.1 q.1 (fun h2 => h (h1.trans h2.symm))]
      · left
        intro u
        simp [hA i u.1 p.1 h1]
    · by_cases h1 : fB p.2 = rB j
      · right
        intro v
        simp [hB j v.2 q.2 (fun h2 => h (h1.trans h2.symm))]
      · left
        intro u
        simp [hB j u.2 p.2 h1]
  rcases hcol with h | h
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h, star_zero, zero_mul,
      Finset.sum_const_zero]
  · simp only [Matrix.mul_apply, h, mul_zero, Finset.sum_const_zero]

end Lift

/-! ### Assembly -/

section Assembly

variable {AI AO BI BO HA HB ιA ιB : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]
  [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] [Fintype ιA] [Fintype ιB]

/-- The process `W' = (Φ_A† ⊗ Φ_B†)(W)` of the Lüders normal form, with the Choi-level maps
`Φ_A = choiMap JA (regKraus TA)` and `Φ_B = choiMap JB (regKraus TB)`; its Kraus operators are
`JAᵀ ⊗ TA x k ⊗ ⟨x|` (the transpose of `JA` acts on Choi matrices). -/
def luedersProcess (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (JA : Matrix HA AI ℂ) (TA : Fin 2 → ιA → Matrix AO HA ℂ) (JB : Matrix HB BI ℂ)
    (TB : Fin 2 → ιB → Matrix BO HB ℂ) :
    Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
      ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ :=
  liftProcess W (fun j => JAᵀ ⊗ₖ regKraus TA j) (fun j => JBᵀ ⊗ₖ regKraus TB j)

lemma trace_luedersProcess_mul (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (JA : Matrix HA AI ℂ) (TA : Fin 2 → ιA → Matrix AO HA ℂ) (JB : Matrix HB BI ℂ)
    (TB : Fin 2 → ιB → Matrix BO HB ℂ) (C : Matrix (HA × (HA × Fin 2)) (HA × (HA × Fin 2)) ℂ)
    (D : Matrix (HB × (HB × Fin 2)) (HB × (HB × Fin 2)) ℂ) :
    (luedersProcess W JA TA JB TB * (C ⊗ₖ D)).trace =
      (W * (choiMap JA (regKraus TA) C ⊗ₖ choiMap JB (regKraus TB) D)).trace :=
  trace_liftProcess_mul _ _ _ _ _

/-- `Φ_A` maps the Lüders Choi matrices to the Choi matrices of the original instrument. -/
lemma choiMap_luedersInstr {M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ}
    {J : Matrix HA AI ℂ} {P : Fin 2 → Fin 2 → Matrix HA HA ℂ} {T : Fin 2 → ιA → Matrix AO HA ℂ}
    (h : IsLuedersDilation M J P T) (x a : Fin 2) :
    choiMap J (regKraus T) (luedersInstr P x a) = M x a := by
  show choiMap J (regKraus T) (krausChoi (luedersKraus (P x a) x)) = M x a
  rw [choiMap_krausChoi, Fintype.sum_prod_type]
  simp_rw [regKraus_mul_luedersKraus]
  have e : ∀ (x' : Fin 2) (k : ιA), krausChoi ((if x' = x then T x k * P x a else 0) * J) =
      if x' = x then krausChoi (T x k * P x a * J) else 0 := by
    intro x' k
    split_ifs <;> simp [krausChoi_zero]
  simp_rw [e]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact h.dil x a

/-- The lifted process of two Lüders dilations: it is a process, it is block diagonal in the
setting registers, and it reproduces the correlations. -/
theorem luedersProcess_spec
    {W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ} (hW : IsProcess W)
    {M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ}
    {N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ} {JA : Matrix HA AI ℂ}
    {P : Fin 2 → Fin 2 → Matrix HA HA ℂ} {TA : Fin 2 → ιA → Matrix AO HA ℂ}
    {JB : Matrix HB BI ℂ} {Q : Fin 2 → Fin 2 → Matrix HB HB ℂ}
    {TB : Fin 2 → ιB → Matrix BO HB ℂ}
    (hA : IsLuedersDilation M JA P TA) (hB : IsLuedersDilation N JB Q TB) :
    IsProcess (luedersProcess W JA TA JB TB) ∧
      (∀ p q, (p.1.2.2 ≠ q.1.2.2 ∨ p.2.2.2 ≠ q.2.2.2) →
        luedersProcess W JA TA JB TB p q = 0) ∧
      ∀ a b x y, (luedersProcess W JA TA JB TB *
        (luedersInstr P x a ⊗ₖ luedersInstr Q y b)).trace = (W * (M x a ⊗ₖ N y b)).trace := by
  refine ⟨⟨posSemidef_liftProcess hW.1 _ _, fun C D hC hD => ?_⟩, fun p q hpq => ?_,
    fun a b x y => ?_⟩
  · rw [trace_luedersProcess_mul]
    exact hW.2 _ _ (isCPTP_choiMap JA hA.iso _ (sum_regKraus TA hA.tp) hC)
      (isCPTP_choiMap JB hB.iso _ (sum_regKraus TB hB.tp) hD)
  · refine liftProcess_apply_eq_zero W _ _ (fun t => t.2.2) (fun t => t.2.2) (fun j => j.1)
      (fun j => j.1) ?_ ?_ p q hpq
    · intro j u t ht
      have ht' : t.2.2 ≠ j.1 := ht
      simp [regKraus, ht']
    · intro j u t ht
      have ht' : t.2.2 ≠ j.1 := ht
      simp [regKraus, ht']
  · rw [trace_luedersProcess_mul, choiMap_luedersInstr hA, choiMap_luedersInstr hB]

end Assembly

/-! ### The main theorem -/

section Main

variable {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq BI]

lemma isCPTP_sum_of_isInstrument {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    {M : Fin 2 → Fin 2 → Matrix (I × O) (I × O) ℂ} (hM : IsInstrument M) (x : Fin 2) :
    IsCPTP (∑ a, M x a) :=
  ⟨posSemidef_sum _ fun a _ => (hM x).1 a, (hM x).2⟩

/-- A process with instruments lives on a nonempty index type (the normalisation
`Tr[W (M ⊗ N)] = 1` excludes the empty case). -/
lemma nonempty_of_isProcess {W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ}
    (hW : IsProcess W) {M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ} (hM : IsInstrument M)
    {N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ} (hN : IsInstrument N) :
    Nonempty ((AI × AO) × (BI × BO)) := by
  by_contra hne
  have : IsEmpty ((AI × AO) × (BI × BO)) := not_nonempty_iff.mp hne
  have h := hW.2 _ _ (isCPTP_sum_of_isInstrument hM 0) (isCPTP_sum_of_isInstrument hN 0)
  rw [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty] at h
  exact zero_ne_one h

/-- **Lemma 1 (Lüders normal form with setting registers).** For every process `W` and
instruments `M`, `N` there are `nA`, `nB`, projective measurements `P` on `ℂ^nA` and `Q` on `ℂ^nB`
(for each setting, orthogonal projectors summing to `1`), and a process `W'` on
`(ℂ^nA ⊗ (ℂ^nA ⊗ ℂ²)) ⊗ (ℂ^nB ⊗ (ℂ^nB ⊗ ℂ²))`, block diagonal in the two setting registers, such
that the Lüders instruments `luedersInstr P`, `luedersInstr Q`
(`ρ ↦ P x a ρ P x a ⊗ |x⟩⟨x|`, `σ ↦ Q y b σ Q y b ⊗ |y⟩⟨y|`) with `W'` give the same correlations
`p(a, b | x, y)` as `M`, `N` with `W`; in particular the same GYNI value. -/
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
      gyniValue W' (luedersInstr P) (luedersInstr Q) = gyniValue W M N := by
  classical
  obtain ⟨⟨⟨-, o₀⟩, ⟨-, q₀⟩⟩⟩ := nonempty_of_isProcess hW hM hN
  obtain ⟨nA, JA, P, TA, hA⟩ := exists_luedersDilation_fin hM o₀
  obtain ⟨nB, JB, Q, TB, hB⟩ := exists_luedersDilation_fin hN q₀
  obtain ⟨hproc, hblock, htr⟩ := luedersProcess_spec hW hA hB
  have hprob : ∀ a b x y, prob (luedersProcess W JA TA JB TB) (luedersInstr P) (luedersInstr Q)
      a b x y = prob W M N a b x y := by
    intro a b x y
    simp only [prob, htr]
  refine ⟨nA, nB, P, Q, luedersProcess W JA TA JB TB, hA.proj, hB.proj, hproc, hblock, htr,
    hprob, ?_⟩
  simp only [gyniValue, hprob]

/-- The projector `Π_{rs}` onto the value `r` of Alice's register and `s` of Bob's register. -/
def registerProj (HA HB : Type*) [DecidableEq HA] [DecidableEq HB] (r s : Fin 2) :
    Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
      ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ :=
  diagonal fun p => if p.1.2.2 = r ∧ p.2.2.2 = s then 1 else 0

/-- Entrywise block diagonality gives the projector form `W' = ∑_{r,s} Π_{rs} W' Π_{rs}`. -/
lemma eq_sum_registerProj {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB]
    [DecidableEq HB]
    {W' : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
      ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ}
    (h : ∀ p q, (p.1.2.2 ≠ q.1.2.2 ∨ p.2.2.2 ≠ q.2.2.2) → W' p q = 0) :
    W' = ∑ r, ∑ s, registerProj HA HB r s * W' * registerProj HA HB r s := by
  ext ⟨⟨h₁, h₂, r₀⟩, ⟨g₁, g₂, s₀⟩⟩ ⟨⟨h₃, h₄, r₁⟩, ⟨g₃, g₄, s₁⟩⟩
  simp only [Matrix.sum_apply, registerProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hrs : r₀ = r₁ ∧ s₀ = s₁
  · obtain ⟨rfl, rfl⟩ := hrs
    fin_cases r₀ <;> fin_cases s₀ <;> simp [Fin.sum_univ_two]
  · rw [h _ _ (not_and_or.mp hrs)]
    simp

/-- `lueders_normal_form` with the Lüders instruments written out as Choi matrices,
`C_{ρ ↦ P x a ρ P x a ⊗ |x⟩⟨x|}` and `C_{σ ↦ Q y b σ Q y b ⊗ |y⟩⟨y|}` (`choiMatrix`), and with
the block diagonality in the projector form `W' = ∑_{r,s} Π_{rs} W' Π_{rs}`. -/
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
          a b x y = prob W M N a b x y := by
  obtain ⟨nA, nB, P, Q, W', hP, hQ, hW', hblock, -, hprob, -⟩ :=
    lueders_normal_form W hW M hM N hN
  refine ⟨nA, nB, P, Q, W', hP, hQ, hW', eq_sum_registerProj hblock, fun a b x y => ?_⟩
  have hM' : (fun x' a' => choiMatrix fun ρ : Matrix (Fin nA) (Fin nA) ℂ =>
      (P x' a' * ρ * P x' a') ⊗ₖ (Matrix.single x' x' 1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      luedersInstr P := by
    funext x' a'
    exact (luedersInstr_eq_choiMatrix hP x' a').symm
  have hN' : (fun y' b' => choiMatrix fun σ : Matrix (Fin nB) (Fin nB) ℂ =>
      (Q y' b' * σ * Q y' b') ⊗ₖ (Matrix.single y' y' 1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      luedersInstr Q := by
    funext y' b'
    exact (luedersInstr_eq_choiMatrix hQ y' b').symm
  have h := hprob a b x y
  rw [← hM', ← hN'] at h
  exact h

end Main

end GYNIUpper
