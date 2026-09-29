import GYNIUpper.UBBasic
import GYNIUpper.LuedersNormalForm

/-!
# Upper bound, part 10: bridge to the Lüders normal form (Lemma 1)

The Lüders-form strategies of Lemma 1 (`GYNIUpper.lueders_normal_form`) use
`GYNIUpper.luedersInstr` and `GYNIUpper.IsProjFamily`; they coincide with `lChoi` and `IsProjMeas`
of `UBBasic`.
-/

namespace GYNIUpperBound

open Matrix GYNIProof

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem luedersInstr_eq_lChoi (P : Fin 2 → Fin 2 → Matrix H H ℂ) :
    GYNIUpper.luedersInstr P = lChoi P := by
  funext x a
  ext p q
  rw [GYNIUpper.luedersInstr_apply]
  simp only [lChoi, lvec, vecMulVec_apply, Pi.star_apply]
  by_cases hp : p.2.2 = x <;> by_cases hq : q.2.2 = x <;> simp [hp, hq]

theorem isProjMeas_of_isProjFamily {P : Fin 2 → Fin 2 → Matrix H H ℂ}
    (hP : GYNIUpper.IsProjFamily P) : IsProjMeas P := hP

/-- Lemma 1 in the form used here: every strategy has a Lüders-form strategy with the same GYNI
value. -/
theorem exists_lueders_form {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
    [DecidableEq AI] [DecidableEq BI]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :
    ∃ (nA nB : ℕ) (P : Fin 2 → Fin 2 → Matrix (Fin nA) (Fin nA) ℂ)
      (Q : Fin 2 → Fin 2 → Matrix (Fin nB) (Fin nB) ℂ)
      (W' : Matrix ((Fin nA × (Fin nA × Fin 2)) × (Fin nB × (Fin nB × Fin 2)))
        ((Fin nA × (Fin nA × Fin 2)) × (Fin nB × (Fin nB × Fin 2))) ℂ),
      IsProjMeas P ∧ IsProjMeas Q ∧ IsProcess W' ∧
        gyniValue W' (lChoi P) (lChoi Q) = gyniValue W M N := by
  obtain ⟨nA, nB, P, Q, W', hP, hQ, hW', -, -, -, hval⟩ :=
    GYNIUpper.lueders_normal_form W hW M hM N hN
  refine ⟨nA, nB, P, Q, W', isProjMeas_of_isProjFamily hP, isProjMeas_of_isProjFamily hQ, hW', ?_⟩
  rw [← luedersInstr_eq_lChoi, ← luedersInstr_eq_lChoi, hval]

end GYNIUpperBound
