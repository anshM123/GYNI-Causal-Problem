import GYNIUpper.UBLevel

/-!
# Upper bound, part 9: the level theorem

`gyni_le_level`: if the packed data of a level pass all kernel checks, then every Lüders-form
strategy satisfies `I_GYNI ≤ betaNum / den`.
-/

namespace GYNIUpperBound

open Matrix GYNIProof Finset
open scoped ComplexOrder Kronecker

theorem uSgn_cast {n : ℕ} (L i1r : ℕ) (i0 i1x : Fin n) (hi0 : i0.val = L) (hi1 : i1x.val = i1r)
    (sgn : ℤ) (sg : ℝ) (hsg : (sgn : ℝ) = sg) (a : Fin n) :
    ((uSgn L i1r sgn a : ℤ) : ℝ) = uC i0 i1x sg a := by
  unfold uSgn uC
  by_cases h0 : a.val = L
  · have ha : a = i0 := Fin.ext (h0.trans hi0.symm)
    rw [if_pos h0, if_pos ha]; simp
  · have hne : a ≠ i0 := fun h => h0 (by rw [h]; exact hi0)
    rw [if_neg h0, if_neg hne]
    by_cases h1 : a.val = i1r
    · have ha : a = i1x := Fin.ext (h1.trans hi1.symm)
      rw [if_pos h1, if_pos ha, hsg]
    · have hne1 : a ≠ i1x := fun h => h1 (by rw [h]; exact hi1)
      rw [if_neg h1, if_neg hne1]; simp

theorem objT_eq {n L : ℕ} {i1 : ℕ → ℕ} {od : ℤ} {den : ℕ} (hden : 64 * od = den) (hod : 0 < od)
    (i0 : Fin n) (i1' : Fin 2 → Fin n) (hi0 : i0.val = L) (hi1 : ∀ x : Fin 2, (i1' x).val = i1 x)
    (r s : Fin 2) (a b a' b' : Fin n) :
    objT i0 i1' (r, a, a') (s, b, b') =
      (objE n L i1 od r s (a * n + b) (a' * n + b') : ℝ) / den := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) b.2
  have hb : ((a : ℕ) * n + b) / n = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt b.2, Nat.zero_add]
  have hb' : ((a' : ℕ) * n + b') / n = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt b'.2, Nat.zero_add]
  have hm : ((a : ℕ) * n + b) % n = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.2]
  have hm' : ((a' : ℕ) * n + b') % n = b' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b'.2]
  have hsA : ((if (s : ℕ) = 0 then (1 : ℤ) else -1 : ℤ) : ℝ) = sgn2 s := by
    fin_cases s <;> simp [sgn2]
  have hsB : ((if (r : ℕ) = 0 then (1 : ℤ) else -1 : ℤ) : ℝ) = sgn2 r := by
    fin_cases r <;> simp [sgn2]
  have hdenR : (den : ℝ) = 64 * (od : ℝ) := by exact_mod_cast hden.symm
  have hodR : (0 : ℝ) < od := by exact_mod_cast hod
  unfold objE
  rw [hb, hb', hm, hm']
  push_cast
  rw [uSgn_cast L (i1 r) i0 (i1' r) hi0 (hi1 r) _ _ hsA a,
    uSgn_cast L (i1 r) i0 (i1' r) hi0 (hi1 r) _ _ hsA a',
    uSgn_cast L (i1 s) i0 (i1' s) hi0 (hi1 s) _ _ hsB b,
    uSgn_cast L (i1 s) i0 (i1' s) hi0 (hi1 s) _ _ hsB b', hdenR, objT]
  field_simp

/-- **The bound of one level**, for Lüders-form strategies, from the kernel-checked data. -/
theorem gyni_le_level
    {L n N nc te bA oA bL oL bX den : ℕ} {cS eB hX onesX od betaNum : ℤ}
    {i1 : ℕ → ℕ} {cw : List (List (Fin 2))} {tab : List (List ℕ)}
    {blk fac : ℕ → ℕ → List ℕ} {col : ℕ → ℕ → List ℤ}
    (hN : N = n * n)
    (h_tab : tabOK (wordAt L) n cw tab = true)
    (h_cov : coverOK (wordAt L) n cw = true)
    (h_cwlen : cw.length = nc)
    (h_te : cw.getD te [] = [])
    (h_te' : te < nc)
    (h_shape : tabShapeOK n nc te tab = true)
    (h_ca : caOK bA oA n nc te tab blk = true)
    (h_cb : cbOK bA oA n nc te tab blk = true)
    (h_len : ∀ r < 2, ∀ s < 2, (blk r s).length = N)
    (h_sym : ∀ r < 2, ∀ s < 2, symOK bA (blk r s) [] 0 = true)
    (h_trace : ((traceSum bA (blk 0 0) 0 : ℕ) : ℤ) + (traceSum bA (blk 0 1) 0 : ℕ)
      + (traceSum bA (blk 1 0) 0 : ℕ) + (traceSum bA (blk 1 1) 0 : ℕ)
      = betaNum + 4 * (N : ℤ) * (oA : ℤ))
    (h_params : 0 < cS ∧ 0 ≤ eB ∧ 2 * hX = pw bX 1 ∧ 2 * oA = 2 ^ bA ∧ 2 * oL = 2 ^ bL ∧
      0 < od ∧ 64 * od = den ∧
      2 * (cS * ((oA : ℤ) + od) + (N : ℤ) * ((oL : ℤ) * (oL : ℤ)) + eB) < pw bX 1)
    (h_ones : onesX = packZ (pw bX 1) (List.replicate N 1))
    (h_words : wordAt L L = [] ∧ wordAt L (i1 0) = [0] ∧ wordAt L (i1 1) = [1] ∧
      L < n ∧ i1 0 < n ∧ i1 1 < n)
    (h_faclen : ∀ r < 2, ∀ s < 2, (fac r s).length = N)
    (h_collen : ∀ r < 2, ∀ s < 2, (col r s).length = N)
    (h_col : ∀ r < 2, ∀ s < 2, colOK bL oL bX (fac r s) (col r s) 0 N = true)
    (h_rows : ∀ r < 2, ∀ s < 2, rowsChk N bX bA bL oA oL cS eB hX onesX (objE n L i1 od r s)
      (col r s) (blk r s) (fac r s) 0 N = true)
    {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
    {W : Matrix ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2)))
      ((HA × (HA × Fin 2)) × (HB × (HB × Fin 2))) ℂ}
    (hW : IsProcess W) {P : Fin 2 → Fin 2 → Matrix HA HA ℂ} {Q : Fin 2 → Fin 2 → Matrix HB HB ℂ}
    (hP : IsProjMeas P) (hQ : IsProjMeas Q) :
    gyniValue W (lChoi P) (lChoi Q) ≤ (betaNum : ℝ) / den := by
  obtain ⟨hc, heps, hh, hoA, hoL, hod, hden, hX⟩ := h_params
  obtain ⟨hw0, hw1, hw2, hL, hi10, hi11⟩ := h_words
  have hdenpos : (0 : ℝ) < den := by
    have : (0 : ℤ) < den := by rw [← hden]; omega
    exact_mod_cast this
  -- the word table
  let wd : Fin n → List (Fin 2) := fun a => wordAt L a
  let i0 : Fin n := ⟨L, hL⟩
  let i1' : Fin 2 → Fin n := fun x => ⟨i1 x, by fin_cases x <;> simp [hi10, hi11]⟩
  have hwd0 : wd i0 = [] := hw0
  have hwd1 : ∀ x, wd (i1' x) = [x] := by
    intro x; fin_cases x
    · exact hw1
    · exact hw2
  -- the tensor `Φ`
  let phiZ : ℕ → ℕ → ℕ → ℕ → ℤ := fun r s i j => (dig bA (rowOf (blk r s) i) j : ℤ) - oA
  let Φ : Fin 2 × Fin n × Fin n → Fin 2 × Fin n × Fin n → ℝ := fun p q =>
    (phiZ p.1 q.1 (p.2.1 * n + q.2.1) (p.2.2 * n + q.2.2) : ℝ) / den
  -- (CA)
  have hCA : ∀ t : List (Fin 2), t ≠ [] → ∀ q,
      ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n => clsW (wd p.2.1) (wd p.2.2) = t),
        Φ p q = 0 := by
    intro t ht q
    obtain ⟨s, b, b'⟩ := q
    have hz := classSum_zero h_tab h_cov h_cwlen h_te
      (fun r a a' => phiZ r s (a * n + b) (a' * n + b'))
      (fun u hu hne => caOK_spec h_ca s s.2 b b.2 b' b'.2 u hu hne) t ht
    rw [← Finset.sum_div]
    have e : ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n => clsW (wd p.2.1) (wd p.2.2) = t),
        ((phiZ p.1 s (p.2.1 * n + b) (p.2.2 * n + b') : ℤ) : ℝ) =
        ((∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n =>
          clsW (wordAt L p.2.1) (wordAt L p.2.2) = t),
          phiZ p.1 s (p.2.1 * n + b) (p.2.2 * n + b') : ℤ) : ℝ) := by push_cast; rfl
    rw [e, hz]; simp
  -- (CB)
  have hCB : ∀ u : List (Fin 2), u ≠ [] → ∀ p,
      ∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n => clsW (wd q.2.1) (wd q.2.2) = u),
        Φ p q = 0 := by
    intro u hu p
    obtain ⟨r, a, a'⟩ := p
    have hz := classSum_zero h_tab h_cov h_cwlen h_te
      (fun s b b' => phiZ r s (a * n + b) (a' * n + b'))
      (fun v hv hne => cbOK_spec h_cb r r.2 a a.2 a' a'.2 v hv hne) u hu
    rw [← Finset.sum_div]
    have e : ∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n => clsW (wd q.2.1) (wd q.2.2) = u),
        ((phiZ r q.1 (a * n + q.2.1) (a' * n + q.2.2) : ℤ) : ℝ) =
        ((∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n =>
          clsW (wordAt L q.2.1) (wordAt L q.2.2) = u),
          phiZ r q.1 (a * n + q.2.1) (a' * n + q.2.2) : ℤ) : ℝ) := by push_cast; rfl
    rw [e, hz]; simp
  -- positive semidefiniteness of the blocks
  have hPSD : ∀ r s : Fin 2, (Matrix.of fun (i j : Fin n × Fin n) =>
      (((Φ (r, i.1, j.1) (s, i.2, j.2) - objT i0 i1' (r, i.1, j.1) (s, i.2, j.2) : ℝ) : ℂ))).PosSemidef := by
    intro r s
    have hoA' : 2 * (oA : ℤ) = 2 ^ bA := by exact_mod_cast hoA
    have hoL' : 2 * (oL : ℤ) = 2 ^ bL := by exact_mod_cast hoL
    have hlenrs := h_len r r.2 s s.2
    have hA := psd_of_rowsChk (α := (oA : ℤ) + od) (lam := (oL : ℤ))
      (h_faclen r r.2 s s.2) (h_collen r r.2 s s.2) hh h_ones hc heps
      (fun i _ j _ => by
        have h1 := abs_dig_sub_le hoA' (rowOf (blk r s) i) j
        have h2 := objE_abs_le n L i1 hod.le r s i j
        unfold aEnt
        have := abs_sub (((dig bA (rowOf (blk r s) i) j : ℕ) : ℤ) - oA) (objE n L i1 od r s i j)
        linarith)
      (fun i _ k _ => by
        unfold lEnt
        split_ifs
        · exact abs_dig_sub_le hoL' _ _
        · simp)
      hX
      (fun i hi j hj => by
        unfold aEnt
        rw [symOK_full (h_sym r r.2 s s.2) i (by omega) j (by omega), objE_symm])
      (h_col r r.2 s s.2) (h_rows r r.2 s s.2)
    let e : Fin n × Fin n ≃ Fin N := finProdFinEquiv.trans (finCongr hN.symm)
    have he : ∀ x : Fin n × Fin n, ((e x : Fin N) : ℕ) = x.1 * n + x.2 := by
      intro x
      simp only [e, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
      ring
    have h2 := hA.submatrix e
    have hinv : (0 : ℂ) ≤ ((den : ℂ))⁻¹ := by
      have : (0 : ℂ) < (den : ℂ) := by exact_mod_cast hdenpos
      exact (inv_pos.mpr this).le
    have h3 := h2.smul hinv
    convert h3 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply,
      smul_eq_mul, aEnt, he, rowOf]
    rw [objT_eq (L := L) hden hod i0 i1' rfl (fun x => rfl) r s i.1 i.2 j.1 j.2]
    simp only [Φ, phiZ, rowOf]
    push_cast
    field_simp
  -- the value
  have hβ : ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n => clsW (wd p.2.1) (wd p.2.2) = []),
      ∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n => clsW (wd q.2.1) (wd q.2.2) = []),
        Φ p q = (betaNum : ℝ) / den := by
    have hdiag : ∀ r s : Fin 2, ∑ a : Fin n, ∑ b : Fin n, phiZ r s (a * n + b) (a * n + b)
        = (traceSum bA (blk r s) 0 : ℤ) - N * oA := by
      intro r s
      have h1 : ∑ a : Fin n, ∑ b : Fin n, phiZ r s (a * n + b) (a * n + b)
          = ∑ i ∈ range (n * n), phiZ r s i i := by
        rw [← sum_pair_eq n (fun i => phiZ r s i i), Fintype.sum_prod_type]
      rw [h1, ← hN, traceSum_eq, h_len r r.2 s s.2]
      simp only [phiZ, rowOf, Nat.zero_add, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    show ∑ p ∈ univ.filter (fun p : Fin 2 × Fin n × Fin n =>
        clsW (wordAt L p.2.1) (wordAt L p.2.2) = []),
      ∑ q ∈ univ.filter (fun q : Fin 2 × Fin n × Fin n =>
        clsW (wordAt L q.2.1) (wordAt L q.2.2) = []), Φ p q = (betaNum : ℝ) / den
    rw [sum_filter_nil h_tab h_cwlen h_te h_shape h_te']
    simp only [sum_filter_nil h_tab h_cwlen h_te h_shape h_te']
    have hre : ∑ r : Fin 2, ∑ a : Fin n, ∑ s : Fin 2, ∑ b : Fin n,
        ((phiZ r s (a * n + b) (a * n + b) : ℤ) : ℝ)
        = ∑ r : Fin 2, ∑ s : Fin 2,
          ((∑ a : Fin n, ∑ b : Fin n, phiZ r s (a * n + b) (a * n + b) : ℤ) : ℝ) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      push_cast; rfl
    simp only [Φ, ← Finset.sum_div]
    congr 1
    rw [hre]
    simp only [hdiag, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
    have h' : ((traceSum bA (blk 0 0) 0 : ℤ) : ℝ) + ((traceSum bA (blk 0 1) 0 : ℤ) : ℝ)
        + ((traceSum bA (blk 1 0) 0 : ℤ) : ℝ) + ((traceSum bA (blk 1 1) 0 : ℤ) : ℝ)
        = (betaNum : ℝ) + 4 * (N : ℝ) * (oA : ℝ) := by exact_mod_cast h_trace
    push_cast at h' ⊢
    linarith
  exact (gyni_le_of_dual hW hP hQ wd i0 i1' hwd0 hwd1 Φ hCA hCB hPSD).trans hβ.le

end GYNIUpperBound
