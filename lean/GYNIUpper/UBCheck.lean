/-!
# Upper bound: computable core (no Mathlib)

Everything the Lean kernel evaluates in the certificate checks of the GYNI upper bound is defined
here, in plain Lean (`Nat`, `Int`, `List`, `Bool`), so that the check files do not import Mathlib.
The Mathlib files (`UBPacked`, `UBBridge`, …) prove the soundness of these checks.

* Free reduction in `ℤ₂ * ℤ₂` (`pushRed`, `red`), the class `clsW w w' = red (w.reverse ++ w')` of a
  pair of words, and the word table `wordAt L a` (position `a - L` on the Cayley line of `ℤ₂ * ℤ₂`).
* Packed rows: a row of a matrix is one natural number `R = ∑ⱼ dⱼ 2^(B j)` with digits
  `dⱼ = dig B R j` (`0 ≤ dⱼ < 2^B`); the entry is `dⱼ - offset`.
* Checks: class tables (`tabOK`, `coverOK`), class sums (`gsum`, `caOK`, `cbOK`), symmetry
  (`symOK`), trace (`traceSum`), packed columns of a Cholesky-type factor (`colOK`) and the row
  identities `c A = L Lᵀ + E` with `E` diagonally dominant (`rowChk`).
-/

namespace GYNIUpperBound

/-! ## Words -/

/-- One step of free reduction; the stack is stored reversed (head = last letter). -/
def pushRed : List (Fin 2) → Fin 2 → List (Fin 2)
  | c :: s, x => if c = x then s else x :: c :: s
  | [], x => [x]

/-- Free reduction in `ℤ₂ * ℤ₂` (cancel equal adjacent letters). -/
def red (w : List (Fin 2)) : List (Fin 2) := (w.foldl pushRed []).reverse

/-- The class `w⁻¹ w'` (reduced) of the pair (bra `w`, ket `w'`). -/
def clsW (w w' : List (Fin 2)) : List (Fin 2) := red (w.reverse ++ w')

/-- The other letter. -/
def flip2 (x : Fin 2) : Fin 2 := if x = 0 then 1 else 0

/-- The alternating word of length `k` starting with `x`. -/
def altWord : Fin 2 → Nat → List (Fin 2)
  | _, 0 => []
  | x, k + 1 => x :: altWord (flip2 x) k

/-- The word at index `a` of level `L`: position `m = a - L` on the Cayley line
(`m ≥ 0`: `1 0 1 …` of length `m`; `m < 0`: `0 1 0 …` of length `-m`). -/
def wordAt (L a : Nat) : List (Fin 2) :=
  if L ≤ a then altWord 1 (a - L) else altWord 0 (L - a)

/-! ## Loops -/

/-- `∀ k < n, p k` as a Boolean (evaluated from `n - 1` down to `0`). -/
def allLT (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => p k && allLT p k

/-- `∀ k, lo ≤ k < lo + cnt → p k` as a Boolean. -/
def allFrom (p : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => p (lo + k) && allFrom p lo k

/-! ## Packed rows -/

/-- Digit `j` of `R` in base `2^B`. -/
def dig (B R j : Nat) : Nat := (R >>> (B * j)) % (2 ^ B)

/-- Row `i` of a list of packed rows (`0` if out of range). -/
def rowOf (rows : List Nat) (i : Nat) : Nat := rows.getD i 0

/-! ## Class tables -/

/-- Entry `(a, t)` of a table stored by columns: `tab[t][a]`. -/
def tabAt (tab : List (List Nat)) (t a : Nat) : Nat := (tab.getD t []).getD a 0

/-- Table specification: for all `a, a' < n` and slots `t < nc`,
`tab[t][a] = a' + 1 ↔ clsW (wd a) (wd a') = cw[t]`, and `tab[t][a] ≤ n`. -/
def tabOK (wd : Nat → List (Fin 2)) (n : Nat) (cw : List (List (Fin 2)))
    (tab : List (List Nat)) : Bool :=
  allLT (fun t => allLT (fun a => decide (tabAt tab t a ≤ n) && allLT (fun a' =>
    (tabAt tab t a == a' + 1) == (clsW (wd a) (wd a') == cw.getD t [])) n) n) cw.length

/-- Every class `clsW (wd a) (wd a')` is one of the slots. -/
def coverOK (wd : Nat → List (Fin 2)) (n : Nat) (cw : List (List (Fin 2))) : Bool :=
  allLT (fun a => allLT (fun a' => cw.contains (clsW (wd a) (wd a'))) n) n

/-! ## Class sums -/

/-- `∑_{k < n} f k`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumTo f k + f k

/-- Table-driven digit: `0` if `g = 0`, otherwise digit `pos (g - 1)` of the row `R`. -/
def gv (B : Nat) (pos : Nat → Nat) (R g : Nat) : Nat :=
  match g with
  | 0 => 0
  | k + 1 => dig B R (pos k)

/-- `1` if the table entry is present. -/
def gc (g : Nat) : Nat := if g = 0 then 0 else 1

/-- (CA) for register `s` and Bob's bra word `b`: for every `b' < n` and slot `t ≠ te`,
`∑_{r, a} gv … (row (a, b) of block (r, s)) (tab[t][a]) = off ⋅ #{(r, a) : tab[t][a] ≠ 0}`,
i.e. the class sums of `Φ = digit - off` vanish. `blk r s` = the packed rows of block `(r, s)`. -/
def caSB (B off n nc te : Nat) (tab : List (List Nat)) (blk : Nat → Nat → List Nat)
    (s b : Nat) : Bool :=
  allLT (fun b' => allLT (fun t => t == te ||
    (sumTo (fun r => sumTo (fun a =>
        gv B (fun a' => a' * n + b') (rowOf (blk r s) (a * n + b)) (tabAt tab t a)) n) 2 ==
      off * sumTo (fun _ => sumTo (fun a => gc (tabAt tab t a)) n) 2)) nc) n

/-- (CA) for all registers `s` and words `b`. -/
def caOK (B off n nc te : Nat) (tab : List (List Nat)) (blk : Nat → Nat → List Nat) : Bool :=
  allLT (fun s => allLT (fun b => caSB B off n nc te tab blk s b) n) 2

/-- (CB) for register `r` and Alice's bra word `a`: for every `a' < n` and slot `u ≠ te`,
`∑_{s, b} gv … (row (a, b) of block (r, s)) (tab[u][b]) = off ⋅ #{(s, b) : tab[u][b] ≠ 0}`. -/
def cbRA (B off n nc te : Nat) (tab : List (List Nat)) (blk : Nat → Nat → List Nat)
    (r a : Nat) : Bool :=
  allLT (fun a' => allLT (fun u => u == te ||
    (sumTo (fun s => sumTo (fun b =>
        gv B (fun b' => a' * n + b') (rowOf (blk r s) (a * n + b)) (tabAt tab u b)) n) 2 ==
      off * sumTo (fun _ => sumTo (fun b => gc (tabAt tab u b)) n) 2)) nc) n

/-- (CB) for all registers `r` and words `a`. -/
def cbOK (B off n nc te : Nat) (tab : List (List Nat)) (blk : Nat → Nat → List Nat) : Bool :=
  allLT (fun r => allLT (fun a => cbRA B off n nc te tab blk r a) n) 2

/-- All table columns have `n` entries and the slot `te` is the diagonal: `tab[te][a] = a + 1`. -/
def tabShapeOK (n nc te : Nat) (tab : List (List Nat)) : Bool :=
  (tab.length == nc) && tab.all (fun col => col.length == n) &&
    allLT (fun a => tabAt tab te a == a + 1) n

/-! ## Symmetry and trace -/

/-- `∀ j < prev.length, dig B Ri j = dig B prev[j] i`. -/
def symRowOK (B Ri i : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | Rj :: rest, j => (dig B Ri j == dig B Rj i) && symRowOK B Ri i rest (j + 1)

/-- The packed rows form a symmetric matrix: `dig B rows[i] j = dig B rows[j] i` for `j < i`. -/
def symOK (B : Nat) : List Nat → List Nat → Nat → Bool
  | [], _, _ => true
  | Ri :: rest, prev, i => symRowOK B Ri i prev 0 && symOK B rest (prev ++ [Ri]) (i + 1)

/-- `∑ᵢ dig B rows[i] (i₀ + i)` (the diagonal digits). -/
def traceSum (B : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | R :: rest, i => dig B R i + traceSum B rest (i + 1)

/-! ## Positive semidefiniteness: `c A = L Lᵀ + E` -/

/-- `2^(B j)` as an integer (a `Nat` power, evaluated with GMP by the kernel). -/
def pw (B j : Nat) : Int := Int.ofNat (2 ^ (B * j))

/-- Absolute value on `Int`. -/
def zabs (a : Int) : Int := if a < 0 then -a else a

/-- Little-endian packing `∑ⱼ lⱼ X^j`. -/
def packZ (X : Int) : List Int → Int
  | [] => 0
  | a :: l => a + X * packZ X l

/-- `∑ₖ lₖ mₖ`. -/
def dotZ : List Int → List Int → Int
  | a :: l, b :: m => a * b + dotZ l m
  | _, _ => 0

/-- `k` digits of `R` from digit `j` on (base `2^B`), minus `off`, as integers. -/
def digsFrom (B : Nat) (off : Int) (R : Nat) : Nat → Nat → List Int
  | _, 0 => []
  | j, k + 1 => ((dig B R j : Int) - off) :: digsFrom B off R (j + 1) k

/-- `k` entries of row `i` of `A` from column `j` on: `dig BA R j - offA - obj i j`. -/
def rowA (BA : Nat) (offA : Int) (obj : Nat → Nat → Int) (R i : Nat) : Nat → Nat → List Int
  | _, 0 => []
  | j, k + 1 => ((dig BA R j : Int) - offA - obj i j) :: rowA BA offA obj R i (j + 1) k

/-- Row `i` of the factor `L` (`i + 1` stored entries; the others are `0`). -/
def rowL (BL : Nat) (offL : Int) (RL i : Nat) : List Int := digsFrom BL offL RL 0 (i + 1)

/-- Column `k` of the factor, packed: `∑ⱼ L_{jk} 2^(B j)`, rows `RLs` (row index from `j`). -/
def colPack (BL : Nat) (offL : Int) (B k : Nat) : List Nat → Nat → Int
  | [], _ => 0
  | RL :: rest, j => (if k ≤ j then (dig BL RL k : Int) - offL else 0) * pw B j
      + colPack BL offL B k rest (j + 1)

/-- The stored packed columns agree with the factor rows: `PL[k] = colPack … k` for
`lo ≤ k < lo + cnt`. -/
def colOK (BL : Nat) (offL : Int) (B : Nat) (RLs : List Nat) (PL : List Int) (lo cnt : Nat) :
    Bool :=
  allFrom (fun k => PL.getD k 0 == colPack BL offL B k RLs 0) lo cnt

/-- Scan the `k` remaining digits of `w` (base `2^B`, balanced by `h`): every
`e = digit - h` satisfies `|e| ≤ eps`; at the end nothing is left (`w = 0`) and
`∑ |e| ≤ 2 eᵢ` (`sabs` accumulates `∑ |e|`, `ei` records `eᵢ`). -/
def eChk (B : Nat) (h eps : Int) (i : Nat) : Nat → Nat → Nat → Int → Int → Bool
  | w, _, 0, sabs, ei => w == 0 && decide (sabs ≤ 2 * ei)
  | w, j, k + 1, sabs, ei =>
    let e : Int := ((w % 2 ^ B : Nat) : Int) - h
    decide (-eps ≤ e ∧ e ≤ eps) &&
      eChk B h eps i (w >>> B) (j + 1) k (sabs + zabs e) (if j = i then e else ei)

/-- Row `i` of `c A = L Lᵀ + E`: `W = c ∑ⱼ Aᵢⱼ X^j - ∑ₖ Lᵢₖ PL[k] + h ∑_{j<N} X^j` (`X = 2^B`)
must be a natural number with `N` digits whose balanced digits `eⱼ` (the row `i` of `E`) satisfy
`|eⱼ| ≤ eps` and `∑ⱼ |eⱼ| ≤ 2 eᵢ`. `ones = ∑_{j<N} X^j`. -/
def rowChk (N B BA BL : Nat) (offA offL c eps h ones : Int) (obj : Nat → Nat → Int)
    (PL : List Int) (R RL i : Nat) : Bool :=
  match c * packZ (pw B 1) (rowA BA offA obj R i 0 N) - dotZ (rowL BL offL RL i) PL + h * ones with
  | Int.ofNat w => eChk B h eps i w 0 N 0 0
  | Int.negSucc _ => false

/-- Rows `lo ≤ i < lo + cnt` of a block. -/
def rowsChk (N B BA BL : Nat) (offA offL c eps h ones : Int) (obj : Nat → Nat → Int)
    (PL : List Int) (Rs RLs : List Nat) (lo cnt : Nat) : Bool :=
  allFrom (fun i => rowChk N B BA BL offA offL c eps h ones obj PL (rowOf Rs i) (rowOf RLs i) i)
    lo cnt

/-! ## The objective (scaled) -/

/-- Coefficient pattern of `u_{c|x}` on the word index `a`: `1` at the empty word `i0`, `sgn` at
the one-letter word `i1x`, `0` elsewhere. -/
def uSgn (i0 i1x : Nat) (sgn : Int) (a : Nat) : Int :=
  if a = i0 then 1 else if a = i1x then sgn else 0

/-- The GYNI objective tensor, scaled by `den` (`od = den / 64`): block `(r, s)`, row `i = a n + b`,
column `j = a' n + b'`, value `od ⋅ ±1` on the support. `i1 x` is the index of the
word `[x]`; Alice's outcome is `s` and Bob's outcome is `r`. -/
def objE (n i0 : Nat) (i1 : Nat → Nat) (od : Int) (r s i j : Nat) : Int :=
  od * (uSgn i0 (i1 r) (if s = 0 then 1 else -1) (i / n) *
    uSgn i0 (i1 r) (if s = 0 then 1 else -1) (j / n) *
    uSgn i0 (i1 s) (if r = 0 then 1 else -1) (i % n) *
    uSgn i0 (i1 s) (if r = 0 then 1 else -1) (j % n))

end GYNIUpperBound
