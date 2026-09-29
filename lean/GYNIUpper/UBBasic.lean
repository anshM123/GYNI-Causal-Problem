import GYNIProof.Defs
import GYNIUpper.UBCheck

/-!
# Upper bound, part 1: Lüders-form strategies, word operators and word vectors

Conventions of `GYNIProof.Defs`: a linear map `L(ℂ^I) → L(ℂ^O)` is represented by its Choi matrix
`M (i, o) (j, o') = ⟨o| 𝓜(|i⟩⟨j|) |o'⟩` on `I × O`.

A *Lüders-form strategy* consists of a process on `(H_A × (H_A × Fin 2)) × (H_B × (H_B × Fin 2))`
and two families of projective measurements `P x a` (Alice) and `Q y b` (Bob). The instruments are
the Lüders instruments with setting register, `ρ ↦ P ρ P ⊗ |x⟩⟨x|`, with Choi matrix
`lChoi P x a = |v⟩⟨v|`, `v (i, (o, r)) = [r = x] (P x a) o i` (`lvec`).

* `obs P x = P x 0 - P x 1` (a unitary involution), `wordOp P w` the product of the `obs P x` along
  the word `w : List (Fin 2)`; `red` (in `UBCheck`) is the free reduction in `ℤ₂ * ℤ₂`, and
  `wordOp P (red w) = wordOp P w` (`wordOp_red`).
* `wvec P w r (i, (o, s)) = [s = r] (wordOp P w) o i`: the word vector `(1 ⊗ π(w))|Φ⟩ ⊗ |r⟩`.
* `pairChoi P w r w' r' = |w', r'⟩⟨w, r|`, and (fact (F4) of `PROOF.md`)
  `ptraceOut (pairChoi P w r w' r') = [r = r'] (wordOp P (red (w.reverse ++ w')))ᵀ`
  (`ptraceOut_pairChoi`).
-/

namespace GYNIUpperBound

open Matrix GYNIProof
open scoped ComplexOrder Kronecker

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Two projective two-outcome measurements (settings `x`, outcomes `a`): every `P x a` is an
orthogonal projector and `∑ a, P x a = 1`. -/
def IsProjMeas (P : Fin 2 → Fin 2 → Matrix H H ℂ) : Prop :=
  ∀ x, (∀ a, IsStarProjection (P x a)) ∧ ∑ a, P x a = 1

/-- The vector `(1 ⊗ P)|Φ⟩ ⊗ |x⟩`: `lvec P x (i, (o, r)) = [r = x] P o i`. -/
def lvec (P : Matrix H H ℂ) (x : Fin 2) : H × (H × Fin 2) → ℂ :=
  fun p => if p.2.2 = x then P p.2.1 p.1 else 0

/-- Choi matrix of the Lüders instrument with setting register, `ρ ↦ P x a ρ P x a ⊗ |x⟩⟨x|`. -/
def lChoi (P : Fin 2 → Fin 2 → Matrix H H ℂ) (x a : Fin 2) :
    Matrix (H × (H × Fin 2)) (H × (H × Fin 2)) ℂ :=
  vecMulVec (lvec (P x a) x) (star (lvec (P x a) x))

/-- The observable `P x 0 - P x 1`. -/
def obs (P : Fin 2 → Fin 2 → Matrix H H ℂ) (x : Fin 2) : Matrix H H ℂ := P x 0 - P x 1

/-- The operator of a word: `wordOp P [x₁, …, xₖ] = obs P x₁ * ⋯ * obs P xₖ`. -/
def wordOp (P : Fin 2 → Fin 2 → Matrix H H ℂ) : List (Fin 2) → Matrix H H ℂ
  | [] => 1
  | x :: w => obs P x * wordOp P w

/-- The word vector `(1 ⊗ wordOp P w)|Φ⟩ ⊗ |r⟩`. -/
def wvec (P : Fin 2 → Fin 2 → Matrix H H ℂ) (w : List (Fin 2)) (r : Fin 2) :
    H × (H × Fin 2) → ℂ :=
  fun p => if p.2.2 = r then wordOp P w p.2.1 p.1 else 0

/-- `|w', r'⟩⟨w, r|`, the Choi matrix of `ρ ↦ π(w') ρ π(w)ᴴ ⊗ |r'⟩⟨r|`. -/
def pairChoi (P : Fin 2 → Fin 2 → Matrix H H ℂ) (w : List (Fin 2)) (r : Fin 2)
    (w' : List (Fin 2)) (r' : Fin 2) : Matrix (H × (H × Fin 2)) (H × (H × Fin 2)) ℂ :=
  vecMulVec (wvec P w' r') (star (wvec P w r))

section Words

variable {P : Fin 2 → Fin 2 → Matrix H H ℂ}

lemma wordOp_append (u v : List (Fin 2)) : wordOp P (u ++ v) = wordOp P u * wordOp P v := by
  induction u with
  | nil => simp [wordOp]
  | cons x u ih => simp [wordOp, ih, Matrix.mul_assoc]

lemma wordOp_singleton (x : Fin 2) : wordOp P [x] = obs P x := by simp [wordOp]

lemma proj_one_eq (hP : IsProjMeas P) (x : Fin 2) : P x 1 = 1 - P x 0 := by
  have h := (hP x).2
  rw [Fin.sum_univ_two] at h
  rw [← h]; abel

lemma proj_idem (hP : IsProjMeas P) (x a : Fin 2) : P x a * P x a = P x a :=
  ((hP x).1 a).isIdempotentElem.eq

lemma proj_herm (hP : IsProjMeas P) (x a : Fin 2) : (P x a)ᴴ = P x a :=
  ((hP x).1 a).isSelfAdjoint.star_eq

lemma obs_eq (hP : IsProjMeas P) (x : Fin 2) : obs P x = (2 : ℂ) • P x 0 - 1 := by
  rw [obs, proj_one_eq hP x, two_smul]; abel

lemma obs_mul_self (hP : IsProjMeas P) (x : Fin 2) : obs P x * obs P x = 1 := by
  have h01 : P x 0 * P x 1 = 0 := by
    rw [proj_one_eq hP x, Matrix.mul_sub, Matrix.mul_one, proj_idem hP, sub_self]
  have h10 : P x 1 * P x 0 = 0 := by
    rw [proj_one_eq hP x, Matrix.sub_mul, Matrix.one_mul, proj_idem hP, sub_self]
  have hs : P x 0 + P x 1 = 1 := by
    have h := (hP x).2
    rwa [Fin.sum_univ_two] at h
  rw [obs, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h01, h10, proj_idem hP, proj_idem hP,
    sub_zero, zero_sub, sub_neg_eq_add, hs]

lemma obs_conjTranspose (hP : IsProjMeas P) (x : Fin 2) : (obs P x)ᴴ = obs P x := by
  rw [obs, conjTranspose_sub, proj_herm hP, proj_herm hP]

lemma wordOp_conjTranspose (hP : IsProjMeas P) (w : List (Fin 2)) :
    (wordOp P w)ᴴ = wordOp P w.reverse := by
  induction w with
  | nil => simp [wordOp]
  | cons x w ih =>
    rw [wordOp, conjTranspose_mul, ih, obs_conjTranspose hP, List.reverse_cons, wordOp_append,
      wordOp_singleton]

lemma wordOp_pushRed (hP : IsProjMeas P) (s : List (Fin 2)) (x : Fin 2) :
    wordOp P (pushRed s x).reverse = wordOp P (s.reverse ++ [x]) := by
  cases s with
  | nil => simp [pushRed]
  | cons c s =>
    by_cases h : c = x
    · subst h
      have e1 : pushRed (c :: s) c = s := by simp [pushRed]
      have e2 : (c :: s).reverse ++ [c] = s.reverse ++ [c, c] := by simp
      rw [e1, e2, wordOp_append]
      simp only [wordOp, Matrix.mul_one]
      rw [obs_mul_self hP, Matrix.mul_one]
    · simp [pushRed, h]

lemma wordOp_foldl (hP : IsProjMeas P) (w s : List (Fin 2)) :
    wordOp P (w.foldl pushRed s).reverse = wordOp P (s.reverse ++ w) := by
  induction w generalizing s with
  | nil => simp
  | cons x w ih =>
    rw [List.foldl_cons, ih, wordOp_append, wordOp_pushRed hP, ← wordOp_append,
      List.append_assoc, List.singleton_append]

lemma wordOp_red (hP : IsProjMeas P) (w : List (Fin 2)) : wordOp P (red w) = wordOp P w := by
  rw [red, wordOp_foldl hP]; simp

end Words

section F4

variable {P : Fin 2 → Fin 2 → Matrix H H ℂ}

/-- Fact (F4): `Tr_out |w', r'⟩⟨w, r| = [r = r'] (π(w)ᴴ π(w'))ᵀ`. -/
lemma ptraceOut_pairChoi (hP : IsProjMeas P) (w : List (Fin 2)) (r : Fin 2)
    (w' : List (Fin 2)) (r' : Fin 2) :
    ptraceOut (pairChoi P w r w' r') =
      if r = r' then (wordOp P (red (w.reverse ++ w')))ᵀ else 0 := by
  rw [wordOp_red hP, wordOp_append, ← wordOp_conjTranspose hP]
  ext i j
  simp only [ptraceOut, pairChoi, wvec, Matrix.of_apply, vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases hr : r = r'
  · subst hr
    rw [if_pos rfl]
    simp only [transpose_apply, mul_apply, conjTranspose_apply]
    refine Finset.sum_congr rfl fun o _ => ?_
    fin_cases r <;> simp [mul_comm]
  · rw [if_neg hr, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun o _ => ?_
    fin_cases r <;> fin_cases r' <;> simp_all

/-- The Lüders vector in terms of word vectors: `P x a = ½ (1 + (-1)^a obs P x)`. -/
lemma lvec_eq (hP : IsProjMeas P) (x a : Fin 2) :
    lvec (P x a) x = fun p => (1 / 2 : ℂ) * wvec P [] x p +
      (if a = 0 then (1 / 2 : ℂ) else -(1 / 2 : ℂ)) * wvec P [x] x p := by
  funext p
  have h1 := proj_one_eq hP x
  simp only [lvec, wvec, wordOp, Matrix.mul_one, obs]
  by_cases hr : p.2.2 = x
  · simp only [hr, if_true]
    fin_cases a
    · simp only [h1, Matrix.sub_apply, one_apply, Fin.zero_eta, if_true]
      ring
    · simp only [h1, Matrix.sub_apply, one_apply, Fin.mk_one, one_ne_zero, if_false]
      ring
  · simp [hr]

end F4

end GYNIUpperBound
