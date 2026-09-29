import GYNIProof.Data

/-!
# Computable core (no Mathlib)

Everything the Lean kernel evaluates in the certificate checks is defined here, in plain Lean
(`Nat`, `Int`, `Fin`, `List`, `Bool`), so that the check files (`CertSmall*`, `CertMid*`,
`CertBigShape_*`, `CertBigRows_*`) do not import Mathlib and run with a small memory footprint.
The Mathlib files (`BlockPSD`, `Model`, …) prove the soundness of these checks.

* Party space `Pt = Fin 8 × (Fin 8 × Fin 2)`: `A_I = ℂ^8` (index `i = 4 q + l`: Jordan qubit `q`,
  label `l`), `A_O = ℂ^8 ⊗ ℂ^2` (output qubit/label `o`, setting register `r`); flat index
  `16 i + 2 o + r` as in `verify_strategy.py`.
* 26 classes per party: `clsN = 13 r + sector(lab i, lab o)` (`sector 0`: equal labels, 16
  elements; the 12 others: 4 elements); `embN c p` is the `p`-th element of class `c` (increasing
  flat index), `posN` its position.
* `HintF i i'` = the integer matrix `H(i,i')` (read from `Hdat`, symmetric by construction),
  `WintF = 2^71 W = 2^65 1 + (2^30 - 1) (T_A + T_B)`, `blockA cA cB` = block `(cA, cB)` of `WintF`.
* Certificate checks: `packL`, `dotL`, `packCols`, `rowOK`, `rowsOK`, `shapeOK`, `paramsOK`.
-/

namespace GYNIProof

/-- Absolute value on `Int`. -/
def iabs (a : Int) : Int := if a < 0 then -a else a

/-- Party space `A_I × A_O`. -/
abbrev Pt := Fin 8 × (Fin 8 × Fin 2)

/-- Label of an `A_I`-index `4 q + l`. -/
def lab (i : Fin 8) : Nat := i.val % 4

/-- Sector of (input label, output label). -/
def secL (l l' : Nat) : Nat := if l = l' then 0 else 1 + l * 3 + (if l' < l then l' else l' - 1)

/-- Class of a party index: `13 * register + sector`. -/
def clsN (a : Pt) : Nat := a.2.2.val * 13 + secL (lab a.1) (lab a.2.1)

/-- Position of a party index inside its class (increasing flat index). -/
def posN (a : Pt) : Nat :=
  if lab a.1 = lab a.2.1 then a.1.val * 2 + a.2.1.val / 4 else (a.1.val / 4) * 2 + a.2.1.val / 4

/-- Class sizes. -/
def szN (c : Nat) : Nat := if c % 13 = 0 then 16 else 4

/-- `x % n` in `Fin n`; the proof term is closed (cheap for the kernel to instantiate). -/
def fmod (n : Nat) (h : 0 < n) (x : Nat) : Fin n := ⟨x % n, Nat.mod_lt x h⟩

/-- The `p`-th element of class `c`. -/
def embN (c p : Nat) : Pt :=
  if c % 13 = 0 then
    (fmod 8 (by decide) (p / 2),
      (fmod 8 (by decide) ((p % 2) * 4 + (p / 2) % 4), fmod 2 (by decide) (c / 13)))
  else
    (fmod 8 (by decide) ((p / 2 % 2) * 4 + (c % 13 - 1) / 3 % 4),
      (fmod 8 (by decide) ((p % 2) * 4 + (if (c % 13 - 1) % 3 < (c % 13 - 1) / 3 % 4
          then (c % 13 - 1) % 3 else (c % 13 - 1) % 3 + 1)), fmod 2 (by decide) (c / 13)))

theorem embN_spec : ∀ c < 26, ∀ p < szN c, clsN (embN c p) = c ∧ posN (embN c p) = p := by
  decide +kernel

/-- Index of the pair `(i, i')` (same label) in `Hdat`. -/
def pairIdx (i i' : Fin 8) : Nat := lab i * 4 + (i.val / 4) * 2 + i'.val / 4

/-- Raw lookup in the data `Hdat`. -/
def Hval (c : Nat) (i i' : Fin 8) (x y : Nat) : Int :=
  (((Hdat.getD c []).getD (pairIdx i i') []).getD x []).getD y 0

/-- The integer matrices `H(i,i')` on the party space. -/
def HintF (i i' : Fin 8) (b b' : Pt) : Int :=
  if lab i = lab i' ∧ clsN b = clsN b' then
    (if i.val * 16 + posN b ≤ i'.val * 16 + posN b' then Hval (clsN b) i i' (posN b) (posN b')
      else Hval (clsN b) i' i (posN b') (posN b))
  else 0

/-- `2^71 W`: `2^65 = 36893488147419103232`, `2^30 - 1 = 1073741823`. -/
def WintF (u v : Pt × Pt) : Int :=
  (if u = v then 36893488147419103232 else 0)
    + 1073741823 * ((if u.1.2 = v.1.2 then HintF u.1.1 v.1.1 u.2 v.2 else 0)
      + (if u.2.2 = v.2.2 then HintF u.2.1 v.2.1 u.1 v.1 else 0))

/-- Block `(cA, cB)` of `2^71 W`, rows/columns `i ↦ (embN cA (i / sB), embN cB (i % sB))`. -/
def blockA (cA cB : Nat) (i j : Nat) : Int :=
  WintF (embN cA (i / szN cB), embN cB (i % szN cB)) (embN cA (j / szN cB), embN cB (j % szN cB))

/-- Bound on the data `Hdat`. -/
def HdatBound : Int := 30000000000

/-- Entry bound for `2^71 W`: `2^65 + 2 (2^30 - 1) HdatBound`. -/
def alphaW : Int := 36893488147419103232 + 2 * 1073741823 * 30000000000

/-- `∑_{i < 8} f i`. -/
def sum8 (f : Fin 8 → Int) : Int := f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + f 7))))))

/-- `∑_i H(i,i) = 0` on the data (for each class `c` and positions `x, y`). -/
theorem Hdiag_data : ∀ c < 26, ∀ x < 16, ∀ y < 16,
    sum8 (fun i => if x ≤ y then Hval c i i x y else Hval c i i y x) = 0 := by
  decide +kernel

/-- All data entries are bounded by `HdatBound`. -/
theorem Hdat_bound : Hdat.all (fun m => m.all (fun r => r.all (fun row => row.all
    (fun a => decide (iabs a ≤ HdatBound))))) = true := by
  decide +kernel

/-! ## Certificate checks -/

/-- Little-endian packing `∑_j l_j X^j` of a list. -/
def packL (X : Int) : List Int → Int
  | [] => 0
  | a :: l => a + X * packL X l

/-- `∑_k l_k m_k` for two lists. -/
def dotL : List Int → List Int → Int
  | a :: l, b :: m => a * b + dotL l m
  | _, _ => 0

/-- Pack all columns of a list of rows at once (Horner in the row index). -/
def packCols (X : Int) (m : Nat) : List (List Int) → List Int
  | [] => List.replicate m 0
  | r :: rs => List.zipWith (fun a p => a + X * p) r (packCols X m rs)

/-- `∑ |l_k|`. -/
def sumAbs : List Int → Int
  | [] => 0
  | a :: l => iabs a + sumAbs l

/-- Row `i`: packed identity `pack(c A_i) = ∑_k L_ik PL_k + pack(E_i)` and dominance of `E_i`. -/
def rowOK (n : Nat) (A : Nat → Nat → Int) (c X : Int) (PL : List Int) (i : Nat)
    (lrow erow : List Int) : Bool :=
  (packL X ((List.range n).map fun j => c * A i j) == dotL lrow PL + packL X erow)
    && decide (sumAbs erow ≤ 2 * erow.getD i 0)

/-- Rows `i, i+1, …` of the certificate. -/
def rowsOK (n : Nat) (A : Nat → Nat → Int) (c X : Int) (PL : List Int) :
    Nat → List (List Int) → List (List Int) → Bool
  | i, l :: ls, e :: es => rowOK n A c X PL i l e && rowsOK n A c X PL (i + 1) ls es
  | _, [], [] => true
  | _, _, _ => false

/-- All rows have length `n` and entries bounded by `b` in absolute value. -/
def rowsBoundOK (n : Nat) (b : Int) (rows : List (List Int)) : Bool :=
  rows.all (fun r => (r.length == n) && r.all fun a => decide (iabs a ≤ b))

/-- Shapes and entry bounds of the certificate data. -/
def shapeOK (n : Nat) (lam eps : Int) (Ls Es : List (List Int)) (PL : List Int) : Bool :=
  (Ls.length == n) && (Es.length == n) && (PL.length == n)
    && rowsBoundOK n lam Ls && rowsBoundOK n eps Es

/-- Positivity of the scale and size of the packing base. -/
def paramsOK (n : Nat) (c X lam eps alpha : Int) : Bool :=
  decide (0 < c) && decide (0 ≤ alpha) && decide (0 ≤ eps)
    && decide (2 * (c * alpha + (n : Int) * (lam * lam) + eps) < X)

theorem rowsBoundOK_append (n : Nat) (b : Int) (l1 l2 : List (List Int)) :
    rowsBoundOK n b (l1 ++ l2) = (rowsBoundOK n b l1 && rowsBoundOK n b l2) := by
  simp [rowsBoundOK, List.all_append]

theorem shapeOK_of_chunks {n : Nat} {lam eps : Int} {Ls Es : List (List Int)} {PL : List Int}
    (hLl : Ls.length = n) (hEl : Es.length = n) (hPl : PL.length = n)
    (hL : rowsBoundOK n lam Ls = true) (hE : rowsBoundOK n eps Es = true) :
    shapeOK n lam eps Ls Es PL = true := by
  simp [shapeOK, hLl, hEl, hPl, hL, hE]

end GYNIProof
