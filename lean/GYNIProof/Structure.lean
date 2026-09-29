import GYNIProof.Defs

/-!
# Structured process matrices

`formW c HA HB` is the matrix
`c 1 + ∑_{i,i'} (|i⟩⟨i'| ⊗ 1_{AO}) ⊗ HA i i' + ∑_{j,j'} HB j j' ⊗ (|j⟩⟨j'| ⊗ 1_{BO})`,
written entrywise. The first sum acts on Alice's side only through her input space (identity on
`A_O`), the second on Bob's side only through his input space. If `∑_i HA i i = 0` and
`∑_j HB j j = 0` (these parts are traceless on the input space) and `c · |AI| · |BI| = 1`, then
`Tr[W (M ⊗ N)] = 1` for all trace-preserving `M`, `N` (`trace_formW_of_tp`); this is the
normalization condition of a process matrix. The general trace formula `trace_formW` is also used
to compute the GYNI value.
-/

namespace GYNIProof

open Matrix
open scoped Kronecker

section General

variable {R : Type*} [CommRing R]
variable {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
  [DecidableEq AI] [DecidableEq AO] [DecidableEq BI] [DecidableEq BO]

/-- `c 1 + ∑_{i,i'} (|i⟩⟨i'| ⊗ 1) ⊗ HA i i' + ∑_{j,j'} HB j j' ⊗ (|j⟩⟨j'| ⊗ 1)`, entrywise. -/
def formW (c : R) (HA : AI → AI → Matrix (BI × BO) (BI × BO) R)
    (HB : BI → BI → Matrix (AI × AO) (AI × AO) R) :
    Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) R :=
  Matrix.of fun u v => (if u = v then c else 0)
    + ((if u.1.2 = v.1.2 then HA u.1.1 v.1.1 u.2 v.2 else 0)
    + (if u.2.2 = v.2.2 then HB u.2.1 v.2.1 u.1 v.1 else 0))

/-- `|i⟩⟨i'| ⊗ 1_O` on `I × O`. -/
def liftIn {I O : Type*} [DecidableEq I] [DecidableEq O] (i i' : I) : Matrix (I × O) (I × O) R :=
  Matrix.single i i' 1 ⊗ₖ (1 : Matrix O O R)

lemma formW_eq (c : R) (HA : AI → AI → Matrix (BI × BO) (BI × BO) R)
    (HB : BI → BI → Matrix (AI × AO) (AI × AO) R) :
    formW c HA HB = c • (1 : Matrix _ _ R)
      + (∑ i, ∑ i', liftIn (O := AO) i i' ⊗ₖ HA i i'
      + ∑ j, ∑ j', HB j j' ⊗ₖ liftIn (O := BO) j j') := by
  ext u v
  simp only [formW, liftIn, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul]
  congr 1
  · by_cases h : u = v <;> simp [h, Matrix.one_apply]
  · congr 1
    · by_cases h : u.1.2 = v.1.2
      · simp [h, Matrix.single_apply, Matrix.one_apply, ite_and, Finset.sum_ite_eq,
          Finset.sum_ite_eq']
      · simp [h, Matrix.one_apply]
    · by_cases h : u.2.2 = v.2.2
      · simp [h, Matrix.single_apply, Matrix.one_apply, ite_and, Finset.sum_ite_eq,
          Finset.sum_ite_eq']
      · simp [h, Matrix.one_apply]

omit [DecidableEq AI] [DecidableEq AO] in
lemma trace_eq_trace_ptraceOut (M : Matrix (AI × AO) (AI × AO) R) :
    M.trace = (ptraceOut M).trace := by
  simp [Matrix.trace, ptraceOut, Fintype.sum_prod_type]

lemma trace_liftIn_mul (i i' : AI) (M : Matrix (AI × AO) (AI × AO) R) :
    (liftIn (O := AO) i i' * M).trace = ptraceOut M i' i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, liftIn, ptraceOut, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- The trace formula for `formW` against a product operator. -/
theorem trace_formW (c : R) (HA : AI → AI → Matrix (BI × BO) (BI × BO) R)
    (HB : BI → BI → Matrix (AI × AO) (AI × AO) R)
    (M : Matrix (AI × AO) (AI × AO) R) (N : Matrix (BI × BO) (BI × BO) R) :
    (formW c HA HB * (M ⊗ₖ N)).trace
      = c * M.trace * N.trace
        + (∑ i, ∑ i', ptraceOut M i' i * (HA i i' * N).trace
          + ∑ j, ∑ j', (HB j j' * M).trace * ptraceOut N j' j) := by
  rw [formW_eq]
  simp only [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_kronecker, smul_eq_mul, Matrix.sum_mul, Matrix.trace_sum]
  congr 1
  · ring
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, trace_liftIn_mul]
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, trace_liftIn_mul]

/-- Normalization: `Tr[formW c HA HB (M ⊗ N)] = 1` for trace-preserving `M`, `N`. -/
theorem trace_formW_of_tp (c : R) (HA : AI → AI → Matrix (BI × BO) (BI × BO) R)
    (HB : BI → BI → Matrix (AI × AO) (AI × AO) R)
    (hc : c * Fintype.card AI * Fintype.card BI = 1)
    (hA : ∑ i, HA i i = 0) (hB : ∑ j, HB j j = 0)
    (M : Matrix (AI × AO) (AI × AO) R) (N : Matrix (BI × BO) (BI × BO) R)
    (hM : ptraceOut M = 1) (hN : ptraceOut N = 1) :
    (formW c HA HB * (M ⊗ₖ N)).trace = 1 := by
  rw [trace_formW, trace_eq_trace_ptraceOut M, trace_eq_trace_ptraceOut N, hM, hN]
  simp only [Matrix.trace_one, Matrix.one_apply]
  have h1 : ∑ i, ∑ i', (if i' = i then (1 : R) else 0) * (HA i i' * N).trace = 0 := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Matrix.trace_sum, ← Matrix.sum_mul, hA, Matrix.zero_mul, Matrix.trace_zero]
  have h2 : ∑ j, ∑ j', (HB j j' * M).trace * (if j' = j then (1 : R) else 0) = 0 := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Matrix.trace_sum, ← Matrix.sum_mul, hB, Matrix.zero_mul, Matrix.trace_zero]
  rw [h1, h2, hc]
  ring

/-- `formW` commutes with ring homomorphisms applied entrywise. -/
lemma formW_map {S : Type*} [CommRing S] (f : R →+* S) (c : R)
    (HA : AI → AI → Matrix (BI × BO) (BI × BO) R) (HB : BI → BI → Matrix (AI × AO) (AI × AO) R) :
    (formW c HA HB).map f = formW (f c) (fun i i' => (HA i i').map f) (fun j j' => (HB j j').map f) := by
  ext u v
  simp only [formW, Matrix.map_apply, Matrix.of_apply, map_add]
  split_ifs <;> simp

/-- Scaling `formW`. -/
lemma formW_smul (r c : R) (HA : AI → AI → Matrix (BI × BO) (BI × BO) R)
    (HB : BI → BI → Matrix (AI × AO) (AI × AO) R) :
    r • formW c HA HB = formW (r * c) (fun i i' => r • HA i i') (fun j j' => r • HB j j') := by
  ext u v
  simp only [formW, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_add]
  split_ifs <;> simp

end General

end GYNIProof
