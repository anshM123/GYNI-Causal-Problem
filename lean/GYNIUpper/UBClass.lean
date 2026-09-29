import GYNIUpper.UBPSD

/-!
# Upper bound, part 7: soundness of the class, symmetry and trace checks

* `tabOK_spec`, `coverOK_spec`, `tabShapeOK_spec`: the class table `tab[t][a] = a' + 1` iff
  `clsW (wd a) (wd a') = cw[t]`; every class occurs among the slots; the slot `te` is the diagonal.
* `classSum_zero`: a table-driven class sum that vanishes for every slot `≠ te` gives the vanishing
  of `∑_{p of class w} F p` for every class `w ≠ []` (the form required by `gyni_le_of_dual`).
* `caOK_spec`, `cbOK_spec`: the kernel checks of the class sums, as integer identities.
* `symOK_spec`: the packed rows form a symmetric matrix.
* `traceSum_eq`: the trace sum.
-/

namespace GYNIUpperBound

open Finset

/-! ## Tables -/

theorem tabOK_spec {wd : ℕ → List (Fin 2)} {n : ℕ} {cw : List (List (Fin 2))}
    {tab : List (List ℕ)} (h : tabOK wd n cw tab = true) :
    ∀ t < cw.length, ∀ a < n, tabAt tab t a ≤ n ∧
      ∀ a' < n, (tabAt tab t a = a' + 1 ↔ clsW (wd a) (wd a') = cw.getD t []) := by
  intro t ht a ha
  have h1 := allLT_true (allLT_true h t ht) a ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1.1, fun a' ha' => ?_⟩
  have h2 := allLT_true h1.2 a' ha'
  simp only [beq_iff_eq] at h2
  constructor
  · intro h3; have := h2; simp [h3] at this; exact this
  · intro h3
    by_contra h4
    have : (tabAt tab t a == a' + 1) = false := by simpa using h4
    rw [this] at h2
    have h5 : (clsW (wd a) (wd a') == cw.getD t []) = true := by simpa using h3
    rw [h5] at h2
    exact Bool.false_ne_true h2

theorem coverOK_spec {wd : ℕ → List (Fin 2)} {n : ℕ} {cw : List (List (Fin 2))}
    (h : coverOK wd n cw = true) : ∀ a < n, ∀ a' < n, clsW (wd a) (wd a') ∈ cw := by
  intro a ha a' ha'
  have := allLT_true (allLT_true h a ha) a' ha'
  simpa using this

theorem tabShapeOK_spec {n nc te : ℕ} {tab : List (List ℕ)} (h : tabShapeOK n nc te tab = true) :
    ∀ a < n, tabAt tab te a = a + 1 := by
  intro a ha
  simp only [tabShapeOK, Bool.and_eq_true] at h
  have := allLT_true h.2 a ha
  simpa using this

/-- The class of `(a, a')` is empty iff `a = a'` (given the diagonal slot `te` with `cw[te] = []`). -/
theorem cls_nil_iff {wd : ℕ → List (Fin 2)} {n nc te : ℕ} {cw : List (List (Fin 2))}
    {tab : List (List ℕ)} (htab : tabOK wd n cw tab = true) (hlen : cw.length = nc)
    (hte : cw.getD te [] = []) (hsh : tabShapeOK n nc te tab = true) (hte' : te < nc)
    {a a' : ℕ} (ha : a < n) (ha' : a' < n) : clsW (wd a) (wd a') = [] ↔ a = a' := by
  have h := ((tabOK_spec htab te (by omega) a ha).2 a' ha')
  rw [hte, tabShapeOK_spec hsh a ha] at h
  rw [← h]; omega

/-! ## Class sums -/

/-- `0` for a missing table entry, `F k` for the entry `k + 1`. -/
def gmatch (g : ℕ) (F : ℕ → ℤ) : ℤ :=
  match g with
  | 0 => 0
  | k + 1 => F k

theorem sum_match_eq {n : ℕ} (g : ℕ) (hg : g ≤ n) (F : ℕ → ℤ) :
    ∑ a' ∈ range n, (if g = a' + 1 then F a' else 0) = gmatch g F := by
  cases g with
  | zero => simp [gmatch]
  | succ k =>
    simp only [Nat.add_right_cancel_iff, gmatch]
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (by omega))]

/-- Vanishing class sums from a table-driven check. -/
theorem classSum_zero {wd : ℕ → List (Fin 2)} {n nc te : ℕ} {cw : List (List (Fin 2))}
    {tab : List (List ℕ)} (htab : tabOK wd n cw tab = true) (hcov : coverOK wd n cw = true)
    (hlen : cw.length = nc) (hte : cw.getD te [] = []) (F : ℕ → ℕ → ℕ → ℤ)
    (hsum : ∀ t < nc, t ≠ te → ∑ r ∈ range 2, ∑ a ∈ range n, gmatch (tabAt tab t a) (F r a) = 0)
    (w : List (Fin 2)) (hw : w ≠ []) :
    ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n => clsW (wd p.2.1) (wd p.2.2) = w),
      F p.1 p.2.1 p.2.2 = 0 := by
  by_cases hmem : w ∈ cw
  · obtain ⟨t, ht, hwt⟩ := List.getElem_of_mem hmem
    have hwt' : cw.getD t [] = w := by rw [List.getD_eq_getElem _ _ ht, hwt]
    have htne : t ≠ te := by
      intro h; subst h; rw [hte] at hwt'; exact hw hwt'.symm
    rw [Finset.sum_filter]
    have hspec := tabOK_spec htab t ht
    have e1 : ∀ p : Fin 2 × Fin n × Fin n,
        (if clsW (wd p.2.1) (wd p.2.2) = w then F p.1 p.2.1 p.2.2 else 0) =
          if tabAt tab t p.2.1 = p.2.2 + 1 then F p.1 p.2.1 p.2.2 else 0 := by
      intro p
      have := (hspec p.2.1 p.2.1.2).2 p.2.2 p.2.2.2
      rw [hwt'] at this
      simp only [this]
    rw [Finset.sum_congr rfl fun p _ => e1 p]
    simp only [Fintype.sum_prod_type]
    rw [Fin.sum_univ_eq_sum_range (fun r => ∑ a : Fin n, ∑ a' : Fin n,
      if tabAt tab t ↑a = ↑a' + 1 then F r ↑a ↑a' else 0) 2]
    calc ∑ r ∈ range 2, ∑ a : Fin n, ∑ a' : Fin n,
          (if tabAt tab t ↑a = ↑a' + 1 then F r ↑a ↑a' else 0)
        = ∑ r ∈ range 2, ∑ a ∈ range n, gmatch (tabAt tab t a) (F r a) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Fin.sum_univ_eq_sum_range (fun a => ∑ a' : Fin n,
            if tabAt tab t a = ↑a' + 1 then F r a ↑a' else 0) n]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [Fin.sum_univ_eq_sum_range (fun a' => if tabAt tab t a = a' + 1 then F r a a' else 0) n]
          exact sum_match_eq _ ((hspec a (Finset.mem_range.mp ha)).1) _
      _ = 0 := hsum t (by omega) htne
  · refine Finset.sum_eq_zero fun p hp => ?_
    have := (Finset.mem_filter.mp hp).2
    exact absurd (this ▸ coverOK_spec hcov p.2.1 p.2.1.2 p.2.2 p.2.2.2) hmem

theorem gv_sub_gc (B : ℕ) (pos : ℕ → ℕ) (R g : ℕ) (off : ℤ) :
    (gv B pos R g : ℤ) - off * (gc g : ℤ) = gmatch g (fun k => (dig B R (pos k) : ℤ) - off) := by
  cases g <;> simp [gv, gc, gmatch]

theorem caOK_spec {B off n nc te : ℕ} {tab : List (List ℕ)} {blk : ℕ → ℕ → List ℕ}
    (h : caOK B off n nc te tab blk = true) :
    ∀ s < 2, ∀ b < n, ∀ b' < n, ∀ t < nc, t ≠ te →
      ∑ r ∈ range 2, ∑ a ∈ range n, gmatch (tabAt tab t a)
        (fun k => (dig B (rowOf (blk r s) (a * n + b)) (k * n + b') : ℤ) - off) = 0 := by
  intro s hs b hb b' hb' t ht hte
  have h1 := allLT_true (allLT_true (allLT_true (allLT_true h s hs) b hb) b' hb') t ht
  simp only [Bool.or_eq_true, beq_iff_eq, hte, false_or] at h1
  rw [sumTo_eq, sumTo_eq] at h1
  simp only [sumTo_eq] at h1
  have h2 : ∑ r ∈ range 2, ∑ a ∈ range n,
      ((gv B (fun a' => a' * n + b') (rowOf (blk r s) (a * n + b)) (tabAt tab t a) : ℤ)
        - (off : ℤ) * (gc (tabAt tab t a) : ℤ)) = 0 := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have := congrArg (fun x : ℕ => (x : ℤ)) h1
    push_cast at this
    rw [this, Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
    ring
  refine Eq.trans ?_ h2
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
  rw [gv_sub_gc]

theorem cbOK_spec {B off n nc te : ℕ} {tab : List (List ℕ)} {blk : ℕ → ℕ → List ℕ}
    (h : cbOK B off n nc te tab blk = true) :
    ∀ r < 2, ∀ a < n, ∀ a' < n, ∀ u < nc, u ≠ te →
      ∑ s ∈ range 2, ∑ b ∈ range n, gmatch (tabAt tab u b)
        (fun k => (dig B (rowOf (blk r s) (a * n + b)) (a' * n + k) : ℤ) - off) = 0 := by
  intro r hr a ha a' ha' u hu hte
  have h1 := allLT_true (allLT_true (allLT_true (allLT_true h r hr) a ha) a' ha') u hu
  simp only [Bool.or_eq_true, beq_iff_eq, hte, false_or] at h1
  simp only [sumTo_eq] at h1
  have h2 : ∑ s ∈ range 2, ∑ b ∈ range n,
      ((gv B (fun b' => a' * n + b') (rowOf (blk r s) (a * n + b)) (tabAt tab u b) : ℤ)
        - (off : ℤ) * (gc (tabAt tab u b) : ℤ)) = 0 := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have := congrArg (fun x : ℕ => (x : ℤ)) h1
    push_cast at this
    rw [this, Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
    ring
  refine Eq.trans ?_ h2
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => ?_
  rw [gv_sub_gc]

/-! ## Symmetry -/

theorem symRowOK_spec {B Ri i : ℕ} : ∀ (prev : List ℕ) (j0 : ℕ), symRowOK B Ri i prev j0 = true →
    ∀ j < prev.length, dig B Ri (j0 + j) = dig B (prev.getD j 0) i
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | Rj :: rest, j0, h, j, hj => by
    simp only [symRowOK, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := symRowOK_spec rest (j0 + 1) h.2 j (by simpa using hj)
      rw [show j0 + (j + 1) = j0 + 1 + j by omega, this, List.getD_cons_succ]

theorem symOK_spec {B : ℕ} : ∀ (rest prev : List ℕ) (i : ℕ), prev.length = i →
    symOK B rest prev i = true →
    ∀ m < rest.length, ∀ j < i + m, dig B (rest.getD m 0) j = dig B ((prev ++ rest).getD j 0) (i + m)
  | [], _, _, _, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | Ri :: rest, prev, i, hlen, h, m, hm => by
    simp only [symOK, Bool.and_eq_true] at h
    cases m with
    | zero =>
      intro j hj
      have := symRowOK_spec prev 0 h.1 j (by omega)
      rw [Nat.zero_add] at this
      rw [List.getD_cons_zero, this, Nat.add_zero, List.getD_append _ _ _ _ (by omega)]
    | succ m =>
      intro j hj
      have ih := symOK_spec rest (prev ++ [Ri]) (i + 1) (by simp [hlen]) h.2 m (by simpa using hm)
        j (by omega)
      rw [List.getD_cons_succ, ih, List.append_assoc, List.singleton_append,
        show i + 1 + m = i + (m + 1) by omega]

theorem symOK_full {B : ℕ} {rows : List ℕ} (h : symOK B rows [] 0 = true) :
    ∀ i < rows.length, ∀ j < rows.length, dig B (rowOf rows i) j = dig B (rowOf rows j) i := by
  have key := symOK_spec rows [] 0 rfl h
  simp only [Nat.zero_add, List.nil_append] at key
  intro i hi j hj
  rcases lt_trichotomy j i with hji | rfl | hij
  · exact key i hi j hji
  · rfl
  · exact (key j hj i hij).symm

/-! ## Trace -/

theorem traceSum_eq (B : ℕ) : ∀ (rows : List ℕ) (i0 : ℕ),
    traceSum B rows i0 = ∑ i ∈ range rows.length, dig B (rows.getD i 0) (i0 + i)
  | [], _ => by simp [traceSum]
  | R :: rest, i0 => by
    rw [traceSum, traceSum_eq B rest (i0 + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show i0 + 1 + i = i0 + (i + 1) by omega]

end GYNIUpperBound
