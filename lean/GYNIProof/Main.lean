import GYNIProof.LowerBound
import GYNIProof.CertBig_0_0
import GYNIProof.CertBig_0_13
import GYNIProof.CertBig_13_13

/-!
# GYNI lower bound: unconditional statements

The three `256 × 256` blocks are kernel-checked in `CertBig_*.lean`, which discharges the
hypothesis `BigBlocksPSD` of `LowerBound.lean`.
-/

namespace GYNIProof

/-- The three `256 × 256` blocks of `2^71 W` are positive semidefinite (kernel-checked). -/
theorem bigBlocksPSD : BigBlocksPSD := ⟨cert_0_0, cert_0_13, cert_13_13⟩

/-- `W` is a valid process matrix. -/
theorem Wc_isProcess' : IsProcess Wc := Wc_isProcess bigBlocksPSD

/-- **Main theorem** (exact value): a valid process matrix and instruments with GYNI value equal
to the certified rational `valNum / valDen = 0.62216590135390844…`. -/
theorem gyni_lower_bound_exact :
    ∃ (W : Matrix (Pt × Pt) (Pt × Pt) ℂ) (M N : Fin 2 → Fin 2 → Matrix Pt Pt ℂ),
      IsValidProcess W ∧ IsInstrument M ∧ IsInstrument N ∧
        gyniValue W M N = (((valNum : ℚ) / valDen : ℚ) : ℝ) :=
  gyni_lower_bound_exact_of_bigBlocks bigBlocksPSD

/-- **Main theorem**: `I_GYNI ≥ 0.6221659013539`. -/
theorem gyni_lower_bound :
    ∃ (W : Matrix (Pt × Pt) (Pt × Pt) ℂ) (M N : Fin 2 → Fin 2 → Matrix Pt Pt ℂ),
      IsValidProcess W ∧ IsInstrument M ∧ IsInstrument N ∧
        (0.6221659013539 : ℝ) ≤ gyniValue W M N :=
  gyni_lower_bound_of_bigBlocks bigBlocksPSD

/-- The bound beats the previous best lower bound `0.6219`. -/
theorem gyni_lower_bound_beats_previous :
    ∃ (W : Matrix (Pt × Pt) (Pt × Pt) ℂ) (M N : Fin 2 → Fin 2 → Matrix Pt Pt ℂ),
      IsValidProcess W ∧ IsInstrument M ∧ IsInstrument N ∧ (0.6219 : ℝ) < gyniValue W M N :=
  gyni_beats_previous_of_bigBlocks bigBlocksPSD

end GYNIProof
