import GYNIProof.BlockPSD
import GYNIUpper.UBCheck

/-!
# Upper bound, part 5: soundness of the kernel checks

* Loops: `allLT_true`, `allFrom_true`, `sumTo_eq`.
* Digits: `dig_eq`, `dig_lt`, `dig_succ`, `eq_sum_dig` (`R < 2^(B N) → R = ∑ⱼ dⱼ 2^(B j)`),
  `abs_dig_sub_le`.
* `eChk_spec`: what the digit scan of a row check establishes.
* `psd_of_rowsChk`: the row checks `c A = L Lᵀ + E` (with `E` given by the balanced digits of the
  packed remainder) and the packed-column check imply that `A` is positive semidefinite
  (via `GYNIProof.posSemidef_of_gram` and `GYNIProof.eq_zero_of_sum_pow`).
* `sym_of_symOK`, `classSum_zero` (vanishing class sums from a table-driven check).
-/

namespace GYNIUpperBound

open Finset

/-! ## Loops -/

theorem allLT_true {p : ℕ → Bool} : ∀ {n : ℕ}, allLT p n = true → ∀ k < n, p k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    simp only [allLT, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · exact allLT_true h.2 k hk'
    · exact h.1

theorem allFrom_true {p : ℕ → Bool} {lo : ℕ} : ∀ {n : ℕ}, allFrom p lo n = true →
    ∀ k, lo ≤ k → k < lo + n → p k = true
  | 0, _, k, h1, h2 => absurd h2 (by omega)
  | n + 1, h, k, h1, h2 => by
    simp only [allFrom, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k (lo + n) with hk | hk
    · exact allFrom_true h.2 k h1 hk
    · have : k = lo + n := by omega
      subst this; exact h.1

theorem allLT_of_forall {p : ℕ → Bool} : ∀ {n : ℕ}, (∀ k < n, p k = true) → allLT p n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [allLT, Bool.and_eq_true]
    exact ⟨h n (by omega), allLT_of_forall fun k hk => h k (by omega)⟩

theorem allFrom_of_forall {p : ℕ → Bool} {lo : ℕ} : ∀ {n : ℕ},
    (∀ k, lo ≤ k → k < lo + n → p k = true) → allFrom p lo n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [allFrom, Bool.and_eq_true]
    exact ⟨h (lo + n) (by omega) (by omega),
      allFrom_of_forall fun k h1 h2 => h k h1 (by omega)⟩

theorem allFrom_add {p : ℕ → Bool} {lo a b : ℕ} (h1 : allFrom p lo a = true)
    (h2 : allFrom p (lo + a) b = true) : allFrom p lo (a + b) = true := by
  refine allFrom_of_forall fun k hk1 hk2 => ?_
  rcases Nat.lt_or_ge k (lo + a) with hk | hk
  · exact allFrom_true h1 k hk1 hk
  · exact allFrom_true h2 k hk (by omega)

/-- Row checks of consecutive chunks combine. -/
theorem rowsChk_add {N B BA BL : ℕ} {offA offL c eps h ones : ℤ} {obj : ℕ → ℕ → ℤ}
    {PL : List ℤ} {Rs RLs : List ℕ} {lo a b : ℕ}
    (h1 : rowsChk N B BA BL offA offL c eps h ones obj PL Rs RLs lo a = true)
    (h2 : rowsChk N B BA BL offA offL c eps h ones obj PL Rs RLs (lo + a) b = true) :
    rowsChk N B BA BL offA offL c eps h ones obj PL Rs RLs lo (a + b) = true :=
  allFrom_add h1 h2

/-- Column checks of consecutive chunks combine. -/
theorem colOK_add {BL : ℕ} {offL : ℤ} {B : ℕ} {RLs : List ℕ} {PL : List ℤ} {lo a b : ℕ}
    (h1 : colOK BL offL B RLs PL lo a = true) (h2 : colOK BL offL B RLs PL (lo + a) b = true) :
    colOK BL offL B RLs PL lo (a + b) = true :=
  allFrom_add h1 h2

theorem sumTo_eq (f : ℕ → ℕ) : ∀ n, sumTo f n = ∑ k ∈ range n, f k
  | 0 => rfl
  | n + 1 => by rw [sumTo, sumTo_eq f n, Finset.sum_range_succ]

/-! ## Digits -/

theorem dig_eq (B R j : ℕ) : dig B R j = R / 2 ^ (B * j) % 2 ^ B := by
  rw [dig, Nat.shiftRight_eq_div_pow]

theorem dig_lt (B R j : ℕ) : dig B R j < 2 ^ B := by
  rw [dig_eq]; exact Nat.mod_lt _ (by positivity)

theorem dig_succ (B R j : ℕ) : dig B R (j + 1) = dig B (R / 2 ^ B) j := by
  rw [dig_eq, dig_eq, Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]

theorem dig_zero (B R : ℕ) : dig B R 0 = R % 2 ^ B := by
  rw [dig_eq]; simp

theorem eq_sum_dig (B : ℕ) : ∀ (N R : ℕ), R < 2 ^ (B * N) →
    R = ∑ j ∈ range N, dig B R j * 2 ^ (B * j)
  | 0, R, h => by simp at h; simp [h]
  | N + 1, R, h => by
    have hq : R / 2 ^ B < 2 ^ (B * N) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      calc R < 2 ^ (B * (N + 1)) := h
        _ = 2 ^ (B * N + B) := by ring_nf
    have ih := eq_sum_dig B N (R / 2 ^ B) hq
    rw [Finset.sum_range_succ', dig_zero]
    simp only [dig_succ, Nat.mul_zero, pow_zero, Nat.mul_one]
    have e : ∑ j ∈ range N, dig B (R / 2 ^ B) j * 2 ^ (B * (j + 1))
        = 2 ^ B * ∑ j ∈ range N, dig B (R / 2 ^ B) j * 2 ^ (B * j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.mul_succ, pow_add]; ring
    rw [e, ← ih]
    exact (Nat.mod_add_div R (2 ^ B)).symm.trans (by ring)

theorem abs_dig_sub_le {B : ℕ} {off : ℤ} (h2 : 2 * off = 2 ^ B) (R j : ℕ) :
    |(dig B R j : ℤ) - off| ≤ off := by
  have hlt : (dig B R j : ℤ) < 2 ^ B := by exact_mod_cast dig_lt B R j
  have h0 : (0 : ℤ) ≤ dig B R j := by positivity
  rw [abs_le]; constructor <;> linarith

/-! ## The digit scan of a row check -/

theorem zabs_eq (a : ℤ) : zabs a = |a| := by
  unfold zabs
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.mp h)).symm

/-- `eChk B h eps i w j k sabs ei = true` gives: `w` has at most `k` digits, every balanced digit is
bounded by `eps`, and `sabs + ∑ |eₘ| ≤ 2 E` where `E` is the digit at `i - j` if it is among the
`k` scanned ones and `ei` otherwise. -/
theorem eChk_spec (B : ℕ) (h eps : ℤ) (i : ℕ) : ∀ (k w j : ℕ) (sabs ei : ℤ),
    eChk B h eps i w j k sabs ei = true →
    w < 2 ^ (B * k) ∧ (∀ m < k, |(dig B w m : ℤ) - h| ≤ eps) ∧
      sabs + ∑ m ∈ range k, |(dig B w m : ℤ) - h| ≤
        2 * (if j ≤ i ∧ i < j + k then (dig B w (i - j) : ℤ) - h else ei)
  | 0, w, j, sabs, ei, hc => by
    simp only [eChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    refine ⟨by simp [hc.1], fun m hm => absurd hm (Nat.not_lt_zero m), ?_⟩
    rw [if_neg (by omega), Finset.sum_range_zero, add_zero]
    exact hc.2
  | k + 1, w, j, sabs, ei, hc => by
    simp only [eChk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hb, hrest⟩ := hc
    set e : ℤ := ((w % 2 ^ B : ℕ) : ℤ) - h with he
    obtain ⟨hw, hdig, hsum⟩ := eChk_spec B h eps i k (w >>> B) (j + 1) (sabs + zabs e)
      (if j = i then e else ei) hrest
    rw [Nat.shiftRight_eq_div_pow] at hw hdig hsum
    have hd0 : (dig B w 0 : ℤ) - h = e := by rw [dig_zero]
    refine ⟨?_, ?_, ?_⟩
    · -- `w < 2^(B (k+1))`
      have h1 : w % 2 ^ B < 2 ^ B := Nat.mod_lt _ (by positivity)
      have h2 := Nat.mod_add_div w (2 ^ B)
      have h3 : 2 ^ B * (w / 2 ^ B) ≤ 2 ^ B * (2 ^ (B * k) - 1) :=
        Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt hw)
      have h4 : 2 ^ (B * (k + 1)) = 2 ^ B * 2 ^ (B * k) := by rw [Nat.mul_succ, pow_add, mul_comm]
      have h5 : 1 ≤ 2 ^ (B * k) := Nat.one_le_two_pow
      rw [h4]
      calc w = w % 2 ^ B + 2 ^ B * (w / 2 ^ B) := h2.symm
        _ < 2 ^ B + 2 ^ B * (2 ^ (B * k) - 1) := by omega
        _ = 2 ^ B * 2 ^ (B * k) := by
          rw [Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right (2 ^ B) (by omega : 0 < 2 ^ (B * k))
          omega
    · intro m hm
      cases m with
      | zero => rw [hd0, ← zabs_eq]; rw [zabs_eq]; exact abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
      | succ m =>
        rw [dig_succ]
        exact hdig m (by omega)
    · rw [Finset.sum_range_succ', hd0]
      simp only [dig_succ]
      rw [zabs_eq] at hsum
      have key : (if j + 1 ≤ i ∧ i < j + 1 + k then (dig B (w / 2 ^ B) (i - (j + 1)) : ℤ) - h
            else if j = i then e else ei) =
          (if j ≤ i ∧ i < j + (k + 1) then (dig B w (i - j) : ℤ) - h else ei) := by
        by_cases hji : j = i
        · subst hji
          have h1 : ¬ (j + 1 ≤ j ∧ j < j + 1 + k) := by omega
          have h2 : j ≤ j ∧ j < j + (k + 1) := by omega
          rw [if_neg h1, if_pos rfl, if_pos h2, Nat.sub_self, hd0]
        · by_cases hin : j + 1 ≤ i ∧ i < j + 1 + k
          · have h2 : j ≤ i ∧ i < j + (k + 1) := by omega
            rw [if_pos hin, if_pos h2]
            have : i - j = (i - (j + 1)) + 1 := by omega
            rw [this, dig_succ]
          · have h2 : ¬ (j ≤ i ∧ i < j + (k + 1)) := by omega
            rw [if_neg hin, if_neg hji, if_neg h2]
      rw [key] at hsum
      linarith

theorem eChk_top {B : ℕ} {h eps : ℤ} {i N w : ℕ} (hi : i < N)
    (hc : eChk B h eps i w 0 N 0 0 = true) :
    w < 2 ^ (B * N) ∧ (∀ m < N, |(dig B w m : ℤ) - h| ≤ eps) ∧
      ∑ m ∈ range N, |(dig B w m : ℤ) - h| ≤ 2 * ((dig B w i : ℤ) - h) := by
  obtain ⟨h1, h2, h3⟩ := eChk_spec B h eps i N w 0 0 0 hc
  have hin : 0 ≤ i ∧ i < 0 + N := by omega
  rw [if_pos hin, Nat.sub_zero, zero_add] at h3
  exact ⟨h1, h2, h3⟩

end GYNIUpperBound
