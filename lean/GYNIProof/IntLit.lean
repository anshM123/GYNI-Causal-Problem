/-!
Integer literals for the generated data files (no imports: the data files are elaborated with a
small memory footprint).
-/

namespace GYNIProof

/-- `n` as an integer. -/
def zp (n : Nat) : Int := Int.ofNat n
/-- `-n` as an integer. -/
def zn (n : Nat) : Int := -Int.ofNat n

end GYNIProof
