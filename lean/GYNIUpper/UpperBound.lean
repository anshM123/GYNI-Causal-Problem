import GYNIUpper.L8.Main
import GYNIUpper.L2.Main

/-!
# GYNI upper bound: main theorems

For every finite-dimensional strategy (a process matrix `W` in the sense of `GYNIProof.IsProcess`
and instruments `M`, `N` in the sense of `GYNIProof.IsInstrument`, settings and outcomes in
`Fin 2`), the GYNI value `gyniValue W M N = ¼ ∑_{x,y} p(a = y, b = x | x, y)` satisfies

* `gyni_upper_bound`: `gyniValue W M N ≤ 175129158097837 / 2^48 = 0.6221837555310…`
  (level-8 certificate `cert3_L8_e9.pkl` of the GYNI repository);
* `gyni_upper_bound_decimal`: `gyniValue W M N ≤ 0.622183755532`;
* `gyni_upper_bound_level2`: `gyniValue W M N ≤ 724501749922913 / 2^50 = 0.6434868193…`
  (level-2 certificate).

Proof: Lemma 1 (`GYNIUpper.lueders_normal_form`) reduces to Lüders-form strategies; for those, the
moment matrix satisfies the class-sum identities (`v2_identity`, from Lemma 2
`trace_kron_of_scalar`) and the register blocks are Gram matrices, so the symmetry-free dual
certificate (checked by the Lean kernel on packed integer data) bounds the value
(`gyni_le_of_dual`, `gyni_le_level`).
-/

namespace GYNIUpperBound

open GYNIProof

/-- **GYNI upper bound** (level 8): `I_GYNI ≤ 175129158097837 / 2^48` for every finite-dimensional
strategy. -/
theorem gyni_upper_bound {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI]
    [Fintype BO] [DecidableEq AI] [DecidableEq BI]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :
    gyniValue W M N ≤ 175129158097837 / 2 ^ 48 :=
  L8.gyni_upper_bound W hW M hM N hN

/-- **GYNI upper bound**, decimal form (rounded up): `I_GYNI ≤ 0.622183755532`. -/
theorem gyni_upper_bound_decimal {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI]
    [Fintype BO] [DecidableEq AI] [DecidableEq BI]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :
    gyniValue W M N ≤ 0.622183755532 :=
  L8.gyni_upper_bound_decimal W hW M hM N hN

/-- The level-2 bound `I_GYNI ≤ 724501749922913 / 2^50`. -/
theorem gyni_upper_bound_level2 {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI]
    [Fintype BO] [DecidableEq AI] [DecidableEq BI]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) (hW : IsProcess W)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ) (hM : IsInstrument M)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (hN : IsInstrument N) :
    gyniValue W M N ≤ 724501749922913 / 2 ^ 50 :=
  L2.gyni_upper_bound W hW M hM N hN

end GYNIUpperBound
