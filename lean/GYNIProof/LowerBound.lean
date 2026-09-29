import GYNIProof.PSD
import GYNIProof.Value

/-!
# A lower bound for the GYNI causal inequality

There are a valid bipartite process matrix `W` (party spaces `A_I = ℂ^8`, `A_O = ℂ^16`) and
instruments (the same for both parties) whose GYNI value is exactly
`valNum / valDen = 0.62216590135390844…` (the value stored in the certificate
`iqoqi/programs/gyni/GYNI_J4_strategy_cert.npz`). In particular `I_GYNI ≥ 0.6221659013539`
(previous best in the literature: `0.6219`).

Status: proved from the single explicit hypothesis `BigBlocksPSD` (positive semidefiniteness of the
three `256 × 256` integer matrices `blockA 0 0`, `blockA 0 13`, `blockA 13 13`, i.e. the blocks of
`2^71 W` where both parties are in a label-diagonal class). Everything else — the normalization
`Tr[W (M ⊗ N)] = 1` on all CPTP maps, the instrument conditions, the exact value, and positive
semidefiniteness of the other 348 blocks (up to the party swap: 673 of the 676 blocks) — is
proved/kernel-checked.

Note: the 12-digit decimal `0.622165901354` quoted for this certificate is the value rounded *up*;
the exact value is `0.622165901353908…`, so the correct 13-digit lower bound is `0.6221659013539`.
-/

namespace GYNIProof

open Matrix

/-- The exact GYNI value of the strategy, as a rational number. -/
theorem valNum_div_valDen :
    ((valNum : ℚ) / valDen) =
      (531635305940712242985790407827762228344120179120176190073634765961621369637945705263661938709953180965374451288130208733938501465399549385052233002270969158553355309 : ℚ) /
      854491229403297986981752981512457986696660306707473343667723374969723257676542077044935981794293593539337845599517266940831593340089011343355546506928909713408000000 := by
  norm_num [valNum, valDen]

/-- **Main theorem** (exact value): a valid process matrix and instruments with GYNI value equal
to the certified rational `valNum / valDen = 0.62216590135390844…`. -/
theorem gyni_lower_bound_exact_of_bigBlocks (hbig : BigBlocksPSD) :
    ∃ (W : Matrix (Pt × Pt) (Pt × Pt) ℂ) (M N : Fin 2 → Fin 2 → Matrix Pt Pt ℂ),
      IsProcess W ∧ IsInstrument M ∧ IsInstrument N ∧
        gyniValue W M N = (((valNum : ℚ) / valDen : ℚ) : ℝ) :=
  ⟨Wc, Mc, Mc, Wc_isProcess hbig, Mc_instrument, Mc_instrument, gyniValue_eq⟩

lemma value_ge : (0.6221659013539 : ℝ) ≤ (((valNum : ℚ) / valDen : ℚ) : ℝ) := by
  have h : (6221659013539 / 10000000000000 : ℚ) ≤ (valNum : ℚ) / valDen := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num [valDen])]
    norm_num [valNum, valDen]
  have h2 : (0.6221659013539 : ℝ) = ((6221659013539 / 10000000000000 : ℚ) : ℝ) := by norm_num
  rw [h2]
  exact_mod_cast h

/-- **Main theorem** (decimal form): `I_GYNI ≥ 0.6221659013539`. -/
theorem gyni_lower_bound_of_bigBlocks (hbig : BigBlocksPSD) :
    ∃ (W : Matrix (Pt × Pt) (Pt × Pt) ℂ) (M N : Fin 2 → Fin 2 → Matrix Pt Pt ℂ),
      IsProcess W ∧ IsInstrument M ∧ IsInstrument N ∧
        (0.6221659013539 : ℝ) ≤ gyniValue W M N :=
  ⟨Wc, Mc, Mc, Wc_isProcess hbig, Mc_instrument, Mc_instrument, by rw [gyniValue_eq]; exact value_ge⟩

/-- The bound beats the previous best lower bound `0.6219`. -/
theorem gyni_beats_previous_of_bigBlocks (hbig : BigBlocksPSD) :
    ∃ (W : Matrix (Pt × Pt) (Pt × Pt) ℂ) (M N : Fin 2 → Fin 2 → Matrix Pt Pt ℂ),
      IsProcess W ∧ IsInstrument M ∧ IsInstrument N ∧ (0.6219 : ℝ) < gyniValue W M N := by
  obtain ⟨W, M, N, hW, hM, hN, hv⟩ := gyni_lower_bound_of_bigBlocks hbig
  exact ⟨W, M, N, hW, hM, hN, lt_of_lt_of_le (by norm_num) hv⟩

end GYNIProof
