import GYNIProof.Core
import GYNIProof.ValueData
import GYNIProof.ValueTabs

/-!
# The integer quadratic forms of the GYNI value (no Mathlib)

`hInt i i' s a = LAM² ⟨v_{a,s}| H(i,i') |v_{a,s}⟩`, computed on the class `13 s` of `v_{a,s}` with
the integer vectors `vtab a s = LAM · v_{a,s}`, and checked by the kernel against the table
`HtabData` (`hInt_tab_s_a`). `Value.lean` relates `hInt` to the trace formula.
-/

namespace GYNIProof

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- `∑_{p < 16} f p`. -/
def sum16 (f : Nat → Int) : Int :=
  f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12
    + (f 13 + (f 14 + f 15))))))))))))))

/-- `vtab a x p = LAM * v_{a,x}(embN (13 x) p)`. -/
def vtab (a x : Fin 2) (p : Nat) : Int := (vtabData.getD (a.val * 2 + x.val) []).getD p 0

/-- `LAM² ⟨v_{a,s}| H(i,i') |v_{a,s}⟩` (zero unless `lab i = lab i'`). -/
def hInt (i i' : Fin 8) (s a : Fin 2) : Int :=
  if lab i = lab i' then
    sum16 (fun p => sum16 (fun p' =>
      HintF i i' (embN (13 * s.val) p) (embN (13 * s.val) p') * vtab a s p' * vtab a s p))
  else 0

/-- Table of `hInt i i' s a`. -/
def Htab (s a : Fin 2) (i i' : Fin 8) : Int :=
  HtabData.getD (128 * s.val + 64 * a.val + 8 * i.val + i'.val) 0

theorem hInt_tab_0_0 : ∀ i i' : Fin 8, hInt i i' 0 0 = Htab 0 0 i i' := by decide +kernel
theorem hInt_tab_0_1 : ∀ i i' : Fin 8, hInt i i' 0 1 = Htab 0 1 i i' := by decide +kernel
theorem hInt_tab_1_0 : ∀ i i' : Fin 8, hInt i i' 1 0 = Htab 1 0 i i' := by decide +kernel
theorem hInt_tab_1_1 : ∀ i i' : Fin 8, hInt i i' 1 1 = Htab 1 1 i i' := by decide +kernel

end GYNIProof
