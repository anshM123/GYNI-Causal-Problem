import GYNIProof.Structure
import GYNIProof.BlockPSD

/-!
# The explicit process matrix

Party space (both parties): `A_I = ℂ^8` (index `i = q * 4 + l`: Jordan qubit `q`, label `l`) and
`A_O = A_I ⊗ ℂ^2` (setting register), i.e. `Pt = Fin 8 × (Fin 8 × Fin 2)`; the flat index of
`(i, (o, r))` in `verify_strategy.py` is `16 i + 2 o + r`.

`W = (1/64) 1 + κ ∑_{i,i'} (|i⟩⟨i'| ⊗ 1_{A_O}) ⊗ H(i,i') + κ ∑_{j,j'} H(j,j') ⊗ (|j⟩⟨j'| ⊗ 1_{B_O})`
with `κ = (2^30 - 1) / 2^71` and integer matrices `H(i,i')` (`HintF`), i.e.
`2^71 W = 2^65 1 + (2^30 - 1) (T_A + T_B)` (`WintF`). This is the process matrix of the certificate
`GYNI_J4_strategy_cert.npz`: the generator `gen_gyni_lean.py` checks exactly that `WintF` agrees
with `4J²·D·2^k·W / 32` of `verify_strategy.py` on all 676 blocks.

Each party space splits into 26 classes (register `r`, and the sector of the pair (input label,
output label): `0` if equal, else one of 12 ordered pairs), `clsN = 13 r + sector`; classes of
sector `0` have 16 elements, the others 4 (`embN`, `posN`). `H(i,i')` vanishes unless
`lab i = lab i'`, maps each class into itself, and `∑_i H(i,i) = 0`.
The data `Hdat[c][pair][x][y] = H(i,i')(embN c x, embN c y)` is stored for classes `c` and pairs
`pair = 4 l + 2 q + q'` (`i = 4 q + l`, `i' = 4 q' + l`); `HintF` reads only the entries with
`(i, x) ≤ (i', y)` (lexicographically) and uses `H(i,i')(b,b') = H(i',i)(b',b)` for the others, so
`W` is symmetric by construction.
-/

namespace GYNIProof

open Matrix
open scoped ComplexOrder Kronecker

/-! `Pt`, `lab`, `secL`, `clsN`, `posN`, `szN`, `embN`, `Hval`, `HintF`, `WintF`, `blockA`,
`HdatBound`, `alphaW` are defined in `Core.lean` (no Mathlib). -/

lemma clsN_lt : ∀ a : Pt, clsN a < 26 := by decide +kernel
lemma posN_lt : ∀ a : Pt, posN a < szN (clsN a) := by decide +kernel
lemma posN_lt16 : ∀ a : Pt, posN a < 16 := by decide +kernel
lemma embN_clsN_posN : ∀ a : Pt, embN (clsN a) (posN a) = a := by decide +kernel

lemma clsN_eq_of_out {a a' : Pt} (ho : a.2 = a'.2) (hl : lab a.1 = lab a'.1) :
    clsN a = clsN a' := by
  unfold clsN
  rw [ho, hl]

/-- Class sizes as a function of `Fin 26`. -/
abbrev sz (c : Fin 26) : ℕ := szN c.val

/-- Enumeration of the party space by classes. -/
def ePt : (Σ c : Fin 26, Fin (sz c)) ≃ Pt where
  toFun s := embN s.1.val s.2.val
  invFun a := ⟨⟨clsN a, clsN_lt a⟩, ⟨posN a, posN_lt a⟩⟩
  left_inv s := by
    obtain ⟨c, p⟩ := s
    have h := embN_spec c.val c.2 p.val p.2
    have hc : (⟨clsN (embN c.val p.val), clsN_lt _⟩ : Fin 26) = c := Fin.ext h.1
    refine Sigma.ext hc ?_
    exact (Fin.heq_ext_iff (congrArg sz hc)).mpr h.2
  right_inv a := embN_clsN_posN a

lemma ePt_apply (s : Σ c : Fin 26, Fin (sz c)) : ePt s = embN s.1.val s.2.val := rfl

lemma clsN_ePt (s : Σ c : Fin 26, Fin (sz c)) : clsN (ePt s) = s.1.val :=
  (embN_spec s.1.val s.1.2 s.2.val s.2.2).1

/-- `κ = (1 - 2^{-30}) / 2^41`. -/
def kappa : ℚ := (2 ^ 30 - 1) / 2 ^ 71

/-- `κ H(i,i')` over `ℚ`. -/
def HA (i i' : Fin 8) : Matrix Pt Pt ℚ := Matrix.of fun b b' => kappa * (HintF i i' b b' : ℚ)

/-- The process matrix over `ℚ`. -/
def Wq : Matrix (Pt × Pt) (Pt × Pt) ℚ := formW (1 / 64) HA HA

/-- The process matrix. -/
noncomputable def Wc : Matrix (Pt × Pt) (Pt × Pt) ℂ := Wq.map (Rat.castHom ℂ)

lemma Wq_apply (u v : Pt × Pt) : Wq u v = (WintF u v : ℚ) / 2 ^ 71 := by
  simp only [Wq, formW, HA, Matrix.of_apply, WintF, kappa]
  split_ifs <;> push_cast <;> ring

lemma Wc_apply (u v : Pt × Pt) : Wc u v = ((WintF u v : ℚ) / 2 ^ 71 : ℚ) := by
  simp [Wc, Wq_apply]

/-! ## Symmetry and block structure -/

lemma HintF_symm (i i' : Fin 8) (b b' : Pt) : HintF i i' b b' = HintF i' i b' b := by
  unfold HintF
  have hb := posN_lt16 b
  have hb' := posN_lt16 b'
  by_cases h : lab i = lab i' ∧ clsN b = clsN b'
  · have h' : lab i' = lab i ∧ clsN b' = clsN b := ⟨h.1.symm, h.2.symm⟩
    rw [if_pos h, if_pos h', h.2]
    by_cases k1 : i.val * 16 + posN b ≤ i'.val * 16 + posN b'
    · by_cases k2 : i'.val * 16 + posN b' ≤ i.val * 16 + posN b
      · have hi : i = i' := Fin.ext (by omega)
        have hx : posN b = posN b' := by omega
        rw [if_pos k1, if_pos k2, hi, hx]
      · rw [if_pos k1, if_neg k2]
    · have k2 : i'.val * 16 + posN b' ≤ i.val * 16 + posN b := by omega
      rw [if_neg k1, if_pos k2]
  · have h' : ¬(lab i' = lab i ∧ clsN b' = clsN b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    rw [if_neg h, if_neg h']

lemma WintF_symm (u v : Pt × Pt) : WintF u v = WintF v u := by
  unfold WintF
  rw [HintF_symm u.1.1 v.1.1 u.2 v.2, HintF_symm u.2.1 v.2.1 u.1 v.1]
  have e0 : (u = v) = (v = u) := propext eq_comm
  have e1 : (u.1.2 = v.1.2) = (v.1.2 = u.1.2) := propext eq_comm
  have e2 : (u.2.2 = v.2.2) = (v.2.2 = u.2.2) := propext eq_comm
  simp only [e0, e1, e2]

lemma WintF_swap (a b a' b' : Pt) : WintF (b, a) (b', a') = WintF (a, b) (a', b') := by
  unfold WintF
  have : ((b, a) = (b', a')) ↔ ((a, b) = (a', b')) := by
    constructor <;> intro h <;> simp only [Prod.mk.injEq] at h ⊢ <;> exact ⟨h.2, h.1⟩
  by_cases h : (a, b) = (a', b')
  · rw [if_pos h, if_pos (this.mpr h)]
    ring
  · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]
    ring

lemma HintF_zero {i i' : Fin 8} {b b' : Pt} (h : clsN b ≠ clsN b') : HintF i i' b b' = 0 := by
  unfold HintF
  rw [if_neg (fun h' => h h'.2)]

lemma HintF_zero' {i i' : Fin 8} {b b' : Pt} (h : lab i ≠ lab i') : HintF i i' b b' = 0 := by
  unfold HintF
  rw [if_neg (fun h' => h h'.1)]

lemma WintF_zero (u v : Pt × Pt) (h : clsN u.1 ≠ clsN v.1 ∨ clsN u.2 ≠ clsN v.2) :
    WintF u v = 0 := by
  unfold WintF
  have hne : u ≠ v := by
    rintro rfl
    rcases h with h | h <;> exact h rfl
  rw [if_neg hne]
  have hA : (if u.1.2 = v.1.2 then HintF u.1.1 v.1.1 u.2 v.2 else 0) = 0 := by
    by_cases ho : u.1.2 = v.1.2
    · rw [if_pos ho]
      by_cases hl : lab u.1.1 = lab v.1.1
      · have hc := clsN_eq_of_out ho hl
        rcases h with h | h
        · exact absurd hc h
        · exact HintF_zero h
      · exact HintF_zero' hl
    · rw [if_neg ho]
  have hB : (if u.2.2 = v.2.2 then HintF u.2.1 v.2.1 u.1 v.1 else 0) = 0 := by
    by_cases ho : u.2.2 = v.2.2
    · rw [if_pos ho]
      by_cases hl : lab u.2.1 = lab v.2.1
      · have hc := clsN_eq_of_out ho hl
        rcases h with h | h
        · exact HintF_zero h
        · exact absurd hc h
      · exact HintF_zero' hl
    · rw [if_neg ho]
  rw [hA, hB]
  ring

/-! ## Normalization (valid-process condition) -/

lemma sum_fin8 (f : Fin 8 → ℤ) : ∑ i : Fin 8, f i = sum8 f := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

lemma sum_HintF_diag (b b' : Pt) : ∑ i : Fin 8, HintF i i b b' = 0 := by
  unfold HintF
  by_cases h : clsN b = clsN b'
  · have key := Hdiag_data (clsN b) (clsN_lt b) (posN b) (posN_lt16 b) (posN b') (posN_lt16 b')
    rw [← sum_fin8] at key
    beta_reduce at key
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos ⟨rfl, h⟩]
    by_cases hxy : posN b ≤ posN b'
    · rw [if_pos (by omega), if_pos hxy]
    · rw [if_neg (by omega), if_neg hxy]
  · exact Finset.sum_eq_zero fun i _ => by rw [if_neg (fun h' => h h'.2)]

lemma sum_HA_diag : ∑ i : Fin 8, HA i i = 0 := by
  ext b b'
  simp only [Matrix.sum_apply, HA, Matrix.of_apply, Matrix.zero_apply]
  rw [← Finset.mul_sum]
  have := congrArg (Int.cast : ℤ → ℚ) (sum_HintF_diag b b')
  push_cast at this
  rw [this, mul_zero]

theorem Wc_eq_formW : Wc = formW ((1 / 64 : ℚ) : ℂ) (fun i i' => (HA i i').map (Rat.castHom ℂ))
    (fun i i' => (HA i i').map (Rat.castHom ℂ)) := by
  rw [Wc, Wq, formW_map]
  rfl

theorem Wc_normalized (M N : Matrix Pt Pt ℂ) (hM : ptraceOut M = 1) (hN : ptraceOut N = 1) :
    (Wc * (M ⊗ₖ N)).trace = 1 := by
  rw [Wc_eq_formW]
  have hA : ∑ i : Fin 8, (HA i i).map (Rat.castHom ℂ) = 0 := by
    ext b b'
    simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.zero_apply]
    rw [← map_sum, ← Matrix.sum_apply, sum_HA_diag, Matrix.zero_apply, map_zero]
  refine trace_formW_of_tp _ _ _ ?_ hA hA M N hM hN
  simp only [Fintype.card_fin]
  push_cast
  norm_num

lemma Wc_isHermitian : Wc.IsHermitian := by
  ext u v
  rw [Matrix.conjTranspose_apply, Wc_apply, Wc_apply, WintF_symm]
  simp

/-! ## Blocks -/

lemma blockA_symm (cA cB : ℕ) (i j : ℕ) : blockA cA cB i j = blockA cA cB j i := by
  unfold blockA
  rw [WintF_symm]

lemma getD_bound {l : List ℤ} {b : ℤ} (hb : 0 ≤ b) (h : l.all (fun a => decide (iabs a ≤ b)) = true)
    (k : ℕ) : |l.getD k 0| ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hb
  | some a =>
    simp only [Option.getD_some]
    have hm : a ∈ l := List.mem_of_getElem? hk
    rw [← iabs_eq_abs]
    exact of_decide_eq_true (List.all_eq_true.mp h a hm)

lemma getD_all {α : Type*} {l : List α} {P : α → Bool} (h : l.all P = true) (d : α) (hd : P d = true)
    (k : ℕ) : P (l.getD k d) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hd
  | some a =>
    simp only [Option.getD_some]
    exact List.all_eq_true.mp h a (List.mem_of_getElem? hk)

lemma Hval_bound (c : ℕ) (i i' : Fin 8) (x y : ℕ) : |Hval c i i' x y| ≤ 30000000000 := by
  unfold Hval
  have hb : (0 : ℤ) ≤ HdatBound := by norm_num [HdatBound]
  have h1 := getD_all Hdat_bound [] (by rfl) c
  have h2 := getD_all h1 [] (by rfl) (pairIdx i i')
  have h3 := getD_all h2 [] (by rfl) x
  exact getD_bound hb h3 y

lemma HintF_bound (i i' : Fin 8) (b b' : Pt) : |HintF i i' b b'| ≤ 30000000000 := by
  unfold HintF
  split_ifs
  · exact Hval_bound _ _ _ _ _
  · exact Hval_bound _ _ _ _ _
  · simp

lemma WintF_bound (u v : Pt × Pt) : |WintF u v| ≤ alphaW := by
  unfold WintF alphaW
  have h1 : |(if u = v then (36893488147419103232 : ℤ) else 0)| ≤ 36893488147419103232 := by
    split_ifs <;> simp
  have h2 : |(if u.1.2 = v.1.2 then HintF u.1.1 v.1.1 u.2 v.2 else 0)| ≤ 30000000000 := by
    split_ifs
    · exact HintF_bound _ _ _ _
    · simp
  have h3 : |(if u.2.2 = v.2.2 then HintF u.2.1 v.2.1 u.1 v.1 else 0)| ≤ 30000000000 := by
    split_ifs
    · exact HintF_bound _ _ _ _
    · simp
  calc |(if u = v then (36893488147419103232 : ℤ) else 0) + 1073741823 *
        ((if u.1.2 = v.1.2 then HintF u.1.1 v.1.1 u.2 v.2 else 0)
          + (if u.2.2 = v.2.2 then HintF u.2.1 v.2.1 u.1 v.1 else 0))|
      ≤ |(if u = v then (36893488147419103232 : ℤ) else 0)| + |(1073741823 : ℤ)| *
        (|(if u.1.2 = v.1.2 then HintF u.1.1 v.1.1 u.2 v.2 else 0)|
          + |(if u.2.2 = v.2.2 then HintF u.2.1 v.2.1 u.1 v.1 else 0)|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        gcongr
        exact abs_add_le _ _
    _ ≤ 36893488147419103232 + 1073741823 * (30000000000 + 30000000000) := by
        rw [show |(1073741823 : ℤ)| = 1073741823 by norm_num]
        gcongr
    _ = 36893488147419103232 + 2 * 1073741823 * 30000000000 := by norm_num

lemma blockA_bound (cA cB : ℕ) : ∀ i < szN cA * szN cB, ∀ j < szN cA * szN cB,
    |blockA cA cB i j| ≤ alphaW := fun _ _ _ _ => WintF_bound _ _

/-- The statement certified for every block. -/
def BlockPSD (cA cB : ℕ) : Prop :=
  ((Matrix.of fun i j : Fin (szN cA * szN cB) => blockA cA cB i j).map
    (Int.cast : ℤ → ℂ)).PosSemidef

lemma rowsOK_append (n : ℕ) (A : ℕ → ℕ → ℤ) (c X : ℤ) (PL : List ℤ) :
    ∀ (i : ℕ) (l1 e1 l2 e2 : List (List ℤ)), l1.length = e1.length →
      rowsOK n A c X PL i l1 e1 = true → rowsOK n A c X PL (i + l1.length) l2 e2 = true →
      rowsOK n A c X PL i (l1 ++ l2) (e1 ++ e2) = true
  | i, [], [], l2, e2, _, _, h2 => by simpa using h2
  | i, a :: l1, b :: e1, l2, e2, hl, h1, h2 => by
    simp only [rowsOK, Bool.and_eq_true, List.cons_append] at h1 ⊢
    refine ⟨h1.1, rowsOK_append n A c X PL (i + 1) l1 e1 l2 e2 (by simpa using hl) h1.2 ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm 1] using h2
  | _, [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _, _ :: _, [], _, _, hl, _, _ => by simp at hl

lemma rowsOK_append' (n : ℕ) (A : ℕ → ℕ → ℤ) (c X : ℤ) (PL : List ℤ) (i j : ℕ)
    (l1 e1 l2 e2 : List (List ℤ)) (hj : j = i + l1.length) (hl : l1.length = e1.length)
    (h1 : rowsOK n A c X PL i l1 e1 = true) (h2 : rowsOK n A c X PL j l2 e2 = true) :
    rowsOK n A c X PL i (l1 ++ l2) (e1 ++ e2) = true :=
  rowsOK_append n A c X PL i l1 e1 l2 e2 hl h1 (hj ▸ h2)

end GYNIProof
