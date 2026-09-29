import GYNIUpper.UBPacked

/-!
# Upper bound, part 6: positive semidefiniteness from the packed row checks

`psd_of_rowsChk`: let `A i j = dig BA R_i j - offA - obj i j` (`R_i` the packed data rows) and
`L i k = dig BL RL_i k - offL` for `k ≤ i` (`0` otherwise). If the packed columns `PL k = ∑ⱼ L j k X^j`
are correct (`colOK`) and every row check `rowChk` passes, then `c A = L Lᵀ + E` with `E` the
balanced digits of the packed remainders; `E` is diagonally dominant, hence `A` is positive
semidefinite (`GYNIProof.posSemidef_of_gram`). The entrywise identity is recovered from the packed
one by `GYNIProof.eq_zero_of_sum_pow`, using `2 (c α + N λ² + eps) < X`.
-/

namespace GYNIUpperBound

open Finset
open scoped ComplexOrder

/-! ## List lemmas -/

theorem packZ_eq_sum (X : ℤ) : ∀ l : List ℤ, packZ X l = ∑ j ∈ range l.length, l.getD j 0 * X ^ j
  | [] => by simp [packZ]
  | a :: l => by
    rw [packZ, packZ_eq_sum X l, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem dotZ_eq_sum : ∀ l m : List ℤ, l.length ≤ m.length →
    dotZ l m = ∑ k ∈ range l.length, l.getD k 0 * m.getD k 0
  | [], _, _ => by simp [dotZ]
  | a :: l, b :: m, h => by
    rw [dotZ, dotZ_eq_sum l m (by simpa using h), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring
  | _ :: _, [], h => by simp at h

theorem rowA_length (BA : ℕ) (offA : ℤ) (obj : ℕ → ℕ → ℤ) (R i : ℕ) :
    ∀ j k, (rowA BA offA obj R i j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by rw [rowA, List.length_cons, rowA_length BA offA obj R i (j + 1) k]

theorem rowA_getD (BA : ℕ) (offA : ℤ) (obj : ℕ → ℕ → ℤ) (R i : ℕ) :
    ∀ j k m, m < k → (rowA BA offA obj R i j k).getD m 0 = (dig BA R (j + m) : ℤ) - offA - obj i (j + m)
  | _, 0, m, hm => absurd hm (Nat.not_lt_zero m)
  | j, k + 1, 0, _ => by rw [rowA, List.getD_cons_zero, Nat.add_zero]
  | j, k + 1, m + 1, hm => by
    rw [rowA, List.getD_cons_succ, rowA_getD BA offA obj R i (j + 1) k m (by omega),
      show j + 1 + m = j + (m + 1) by omega]

theorem digsFrom_length (B : ℕ) (off : ℤ) (R : ℕ) : ∀ j k, (digsFrom B off R j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by rw [digsFrom, List.length_cons, digsFrom_length B off R (j + 1) k]

theorem digsFrom_getD (B : ℕ) (off : ℤ) (R : ℕ) :
    ∀ j k m, m < k → (digsFrom B off R j k).getD m 0 = (dig B R (j + m) : ℤ) - off
  | _, 0, m, hm => absurd hm (Nat.not_lt_zero m)
  | j, k + 1, 0, _ => by rw [digsFrom, List.getD_cons_zero, Nat.add_zero]
  | j, k + 1, m + 1, hm => by
    rw [digsFrom, List.getD_cons_succ, digsFrom_getD B off R (j + 1) k m (by omega),
      show j + 1 + m = j + (m + 1) by omega]

theorem pw_eq (B j : ℕ) : pw B j = pw B 1 ^ j := by
  simp only [pw, Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat, Nat.mul_one]
  rw [← pow_mul]

theorem pw_pos (B : ℕ) : 0 < pw B 1 := by
  simp only [pw, Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat]; positivity

theorem colPack_eq (BL : ℕ) (offL : ℤ) (B k : ℕ) : ∀ (RLs : List ℕ) (j0 : ℕ),
    colPack BL offL B k RLs j0 = ∑ m ∈ range RLs.length,
      (if k ≤ j0 + m then (dig BL (RLs.getD m 0) k : ℤ) - offL else 0) * pw B (j0 + m)
  | [], _ => by simp [colPack]
  | RL :: rest, j0 => by
    rw [colPack, colPack_eq BL offL B k rest (j0 + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show j0 + 1 + m = j0 + (m + 1) by omega]

theorem packZ_ones (X : ℤ) (N : ℕ) : packZ X (List.replicate N 1) = ∑ j ∈ range N, X ^ j := by
  rw [packZ_eq_sum, List.length_replicate]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate, one_mul]

/-! ## Entries -/

/-- Entry `(i, j)` of the certified matrix of a block: `dig BA R_i j - offA - obj i j`. -/
def aEnt (BA : ℕ) (offA : ℤ) (obj : ℕ → ℕ → ℤ) (Rs : List ℕ) (i j : ℕ) : ℤ :=
  (dig BA (rowOf Rs i) j : ℤ) - offA - obj i j

/-- Entry `(i, k)` of the factor: `dig BL RL_i k - offL` for `k ≤ i`, else `0`. -/
def lEnt (BL : ℕ) (offL : ℤ) (RLs : List ℕ) (i k : ℕ) : ℤ :=
  if k ≤ i then (dig BL (rowOf RLs i) k : ℤ) - offL else 0

/-- The packed remainder of row `i` (shifted by `h ∑ X^j`). -/
def wRow (N B BA BL : ℕ) (offA offL c h ones : ℤ) (obj : ℕ → ℕ → ℤ) (PL : List ℤ)
    (Rs RLs : List ℕ) (i : ℕ) : ℤ :=
  c * packZ (pw B 1) (rowA BA offA obj (rowOf Rs i) i 0 N) - dotZ (rowL BL offL (rowOf RLs i) i) PL
    + h * ones

/-- Entry `(i, j)` of the remainder `E`: the balanced digit `j` of `wRow i`. -/
def eEnt (N B BA BL : ℕ) (offA offL c h ones : ℤ) (obj : ℕ → ℕ → ℤ) (PL : List ℤ)
    (Rs RLs : List ℕ) (i j : ℕ) : ℤ :=
  (dig B (wRow N B BA BL offA offL c h ones obj PL Rs RLs i).toNat j : ℤ) - h

theorem rowChk_spec {N B BA BL : ℕ} {offA offL c eps h ones : ℤ} {obj : ℕ → ℕ → ℤ}
    {PL : List ℤ} {Rs RLs : List ℕ} {i : ℕ}
    (hc : rowChk N B BA BL offA offL c eps h ones obj PL (rowOf Rs i) (rowOf RLs i) i = true) :
    ∃ w : ℕ, wRow N B BA BL offA offL c h ones obj PL Rs RLs i = (w : ℤ) ∧
      eChk B h eps i w 0 N 0 0 = true := by
  unfold rowChk at hc
  split at hc
  · rename_i w hw
    exact ⟨w, hw, hc⟩
  · simp at hc

/-! ## The main soundness theorem -/

theorem psd_of_rowsChk {N B BA BL : ℕ} {offA offL c eps h ones α lam : ℤ} {obj : ℕ → ℕ → ℤ}
    {PL : List ℤ} {Rs RLs : List ℕ} (hRL : RLs.length = N) (hPL : PL.length = N)
    (_hh : 2 * h = pw B 1) (hones : ones = packZ (pw B 1) (List.replicate N 1))
    (hc : 0 < c) (_heps : 0 ≤ eps)
    (hα : ∀ i < N, ∀ j < N, |aEnt BA offA obj Rs i j| ≤ α)
    (hlam : ∀ i < N, ∀ k < N, |lEnt BL offL RLs i k| ≤ lam)
    (hX : 2 * (c * α + N * (lam * lam) + eps) < pw B 1)
    (hsym : ∀ i < N, ∀ j < N, aEnt BA offA obj Rs i j = aEnt BA offA obj Rs j i)
    (hcol : colOK BL offL B RLs PL 0 N = true)
    (hrows : rowsChk N B BA BL offA offL c eps h ones obj PL Rs RLs 0 N = true) :
    ((Matrix.of fun i j : Fin N => aEnt BA offA obj Rs i j).map (Int.cast : ℤ → ℂ)).PosSemidef := by
  set X : ℤ := pw B 1 with hXdef
  have hX0 : 0 < X := pw_pos B
  set A := aEnt BA offA obj Rs with hA
  set L := lEnt BL offL RLs with hL
  set E := eEnt N B BA BL offA offL c h ones obj PL Rs RLs with hE
  -- packed columns
  have hPLk : ∀ k < N, PL.getD k 0 = ∑ j ∈ range N, L j k * X ^ j := by
    intro k hk
    have h1 := allFrom_true hcol k (Nat.zero_le k) (by omega)
    simp only [beq_iff_eq] at h1
    rw [h1, colPack_eq, hRL]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hL, lEnt, rowOf, Nat.zero_add, pw_eq B j]
    rfl
  -- the row identities
  have hrow : ∀ i < N, ∀ j < N, c * A i j = ∑ k ∈ range N, L i k * L j k + E i j ∧
      |E i j| ≤ eps := by
    intro i hi
    have hri := allFrom_true hrows i (Nat.zero_le i) (by omega)
    obtain ⟨w, hw, hchk⟩ := rowChk_spec hri
    obtain ⟨hwlt, hdig, -⟩ := eChk_top hi hchk
    have hEij : ∀ j, E i j = (dig B w j : ℤ) - h := by
      intro j; simp only [hE, eEnt, hw, Int.toNat_natCast]
    -- the packed identity
    have hwsum : (w : ℤ) = ∑ j ∈ range N, (dig B w j : ℤ) * X ^ j := by
      have h1 := eq_sum_dig B N w hwlt
      calc (w : ℤ) = ((∑ j ∈ range N, dig B w j * 2 ^ (B * j) : ℕ) : ℤ) :=
            congrArg (fun x : ℕ => (x : ℤ)) h1
        _ = ∑ j ∈ range N, (dig B w j : ℤ) * X ^ j := by
          push_cast
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hXdef, ← pw_eq B j]
          simp [pw]
    have hpackA : packZ X (rowA BA offA obj (rowOf Rs i) i 0 N) = ∑ j ∈ range N, A i j * X ^ j := by
      rw [packZ_eq_sum, rowA_length]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [rowA_getD _ _ _ _ _ _ _ _ (Finset.mem_range.mp hj), Nat.zero_add]
      rfl
    have hdot : dotZ (rowL BL offL (rowOf RLs i) i) PL = ∑ k ∈ range N, L i k * PL.getD k 0 := by
      rw [rowL, dotZ_eq_sum _ _ (by rw [digsFrom_length, hPL]; omega), digsFrom_length]
      rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ N by omega)]
      have hzero : ∑ k ∈ Finset.Ico (i + 1) N, L i k * PL.getD k 0 = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have : ¬ k ≤ i := by simp at hk; omega
        simp [hL, lEnt, this]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < i + 1 := Finset.mem_range.mp hk
      rw [digsFrom_getD _ _ _ _ _ _ hk', Nat.zero_add]
      simp [hL, lEnt, show k ≤ i by omega]
    have hLL : ∑ k ∈ range N, L i k * PL.getD k 0 =
        ∑ j ∈ range N, (∑ k ∈ range N, L i k * L j k) * X ^ j := by
      rw [Finset.sum_congr rfl fun k hk => by rw [hPLk k (Finset.mem_range.mp hk)]]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hid0 : ∑ j ∈ range N, (c * A i j - ∑ k ∈ range N, L i k * L j k - E i j) * X ^ j = 0 := by
      have hW : wRow N B BA BL offA offL c h ones obj PL Rs RLs i = (w : ℤ) := hw
      simp only [wRow] at hW
      rw [hpackA, hdot, hLL, hones, packZ_ones, hwsum] at hW
      have e2 : ∑ j ∈ range N, (c * A i j - ∑ k ∈ range N, L i k * L j k - E i j) * X ^ j
          = c * ∑ j ∈ range N, A i j * X ^ j - ∑ j ∈ range N, (∑ k ∈ range N, L i k * L j k) * X ^ j
            + h * ∑ j ∈ range N, X ^ j - ∑ j ∈ range N, (dig B w j : ℤ) * X ^ j := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hEij j]; ring
      rw [e2, hW]; ring
    intro j hj
    have hz := GYNIProof.eq_zero_of_sum_pow hX0 N
      (fun j => c * A i j - ∑ k ∈ range N, L i k * L j k - E i j) (fun j hj => by
        have b1 : |c * A i j| ≤ c * α := by
          rw [abs_mul, abs_of_pos hc]
          exact mul_le_mul_of_nonneg_left (hα i hi j hj) hc.le
        have b2 : |∑ k ∈ range N, L i k * L j k| ≤ N * (lam * lam) := by
          calc |∑ k ∈ range N, L i k * L j k|
              ≤ ∑ k ∈ range N, |L i k * L j k| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k ∈ range N, lam * lam := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hk' := Finset.mem_range.mp hk
                rw [abs_mul]
                exact mul_le_mul (hlam i hi k hk') (hlam j hj k hk') (abs_nonneg _)
                  ((abs_nonneg _).trans (hlam i hi k hk'))
            _ = N * (lam * lam) := by simp
        have b3 : |E i j| ≤ eps := by rw [hEij]; exact hdig j hj
        have := abs_sub (c * A i j - ∑ k ∈ range N, L i k * L j k) (E i j)
        have := abs_sub (c * A i j) (∑ k ∈ range N, L i k * L j k)
        linarith) hid0 j hj
    refine ⟨by linarith, ?_⟩
    rw [hEij]; exact hdig j hj
  -- symmetry of `E` and dominance
  have hEsym : ∀ i < N, ∀ j < N, E i j = E j i := by
    intro i hi j hj
    have h1 := (hrow i hi j hj).1
    have h2 := (hrow j hj i hi).1
    rw [hsym j hj i hi] at h2
    have : ∑ k ∈ range N, L i k * L j k = ∑ k ∈ range N, L j k * L i k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  have hdom : ∀ i < N, ∑ j ∈ range N, |E i j| ≤ 2 * E i i := by
    intro i hi
    have hri := allFrom_true hrows i (Nat.zero_le i) (by omega)
    obtain ⟨w, hw, hchk⟩ := rowChk_spec hri
    obtain ⟨-, -, hs⟩ := eChk_top hi hchk
    have hEij : ∀ j, E i j = (dig B w j : ℤ) - h := by
      intro j; simp only [hE, eEnt, hw, Int.toNat_natCast]
    simp only [hEij]; exact hs
  refine GYNIProof.posSemidef_of_gram (Matrix.of fun i j : Fin N => A i j)
    (Matrix.of fun i k : Fin N => L i k) (Matrix.of fun i j : Fin N => E i j) c hc
    (fun i j => hEsym i i.2 j j.2) (fun i => ?_) (fun i j => ?_)
  · simp only [Matrix.of_apply]
    rw [← Finset.sum_range (fun j => |E i j|)]
    exact hdom i i.2
  · simp only [Matrix.of_apply]
    rw [← Finset.sum_range (fun k => L i k * L j k)]
    exact (hrow i i.2 j j.2).1

end GYNIUpperBound
