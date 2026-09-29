import GYNIProof.ValueCore

/-!
# The instruments and the rational pieces of the GYNI value (no Mathlib)

Core Lean's `Rat` (= Mathlib's `ℚ`). All finite sums are written out (`sumR8`, `sumR2`), so the
kernel checks below never enumerate a `Fintype`; `Value.lean` converts them to `Finset` sums.

Instruments (Alice = Bob): in label block `l`, `P_{0|x} = |φ_l^x⟩⟨φ_l^x|`,
`φ_l^x = (c_l, (-1)^{x+1} s_l)` rational with `c_l² + s_l² = 1` (`cs_unit`), `P_{1|x} = 1 - P_{0|x}`;
Lüders Choi matrix `M_{a|x} = |v⟩⟨v|`, `v[(i, (o, r))] = P_{a|x}[o, i] δ_{r,x}` (`vvec`).
-/

namespace GYNIProof

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- `c_l`. -/
def cS (l : Nat) : Rat := ((cNum.getD l 0 : Nat) : Rat) / ((csDen.getD l 1 : Nat) : Rat)
/-- `s_l`. -/
def sS (l : Nat) : Rat := ((sNum.getD l 0 : Nat) : Rat) / ((csDen.getD l 1 : Nat) : Rat)

theorem cs_unit : ∀ l < 4, cS l * cS l + sS l * sS l = 1 := by decide +kernel

/-- Component `q` of `φ_l^x = (c_l, (-1)^{x+1} s_l)`. -/
def phi (x : Fin 2) (l q : Nat) : Rat := if q = 0 then cS l else if x = 0 then -sS l else sS l

/-- `P_{0|x}` on `A_I` (indices `q * 4 + l`). -/
def P0 (x : Fin 2) (o i : Fin 8) : Rat :=
  if lab o = lab i then phi x (lab o) (o.val / 4) * phi x (lab i) (i.val / 4) else 0

/-- `P_{a|x}`. -/
def Pm (a x : Fin 2) (o i : Fin 8) : Rat :=
  if a = 0 then P0 x o i else (if o = i then 1 else 0) - P0 x o i

/-- `v_{a,x}[(i, (o, r))] = P_{a|x}[o, i] δ_{r,x}`. -/
def vvec (a x : Fin 2) (b : Pt) : Rat := if b.2.2 = x then Pm a x b.2.1 b.1 else 0

/-- `∑_{i : Fin 8} f i`, written out. -/
def sumR8 (f : Fin 8 → Rat) : Rat := f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + f 7))))))
/-- `∑_{i : Fin 2} f i`, written out. -/
def sumR2 (f : Fin 2 → Rat) : Rat := f 0 + f 1

/-- The projectors are symmetric idempotents (`P_{1|x} = 1 - P_{0|x}` by definition). -/
theorem Pm_proj : ∀ a x : Fin 2, ∀ o i : Fin 8,
    sumR8 (fun k => Pm a x o k * Pm a x k i) = Pm a x o i ∧ Pm a x o i = Pm a x i o := by
  decide +kernel

/-- `Tr_O ∑_a M_{a|x} = 1` (entries). -/
theorem ptrace_vvec : ∀ x : Fin 2, ∀ i j : Fin 8,
    sumR2 (fun a => sumR8 (fun o => sumR2 (fun r => vvec a x (i, (o, r)) * vvec a x (j, (o, r)))))
      = if i = j then 1 else 0 := by
  decide +kernel

/-- `v_{a,x}` vanishes outside the class `13 x`. -/
theorem vvec_support : ∀ a x : Fin 2, ∀ i o : Fin 8, ∀ r : Fin 2,
    clsN (i, (o, r)) ≠ 13 * x.val → vvec a x (i, (o, r)) = 0 := by
  decide +kernel

/-- `v_{a,x}` on its class, as integers over `LAM`. -/
theorem vvec_tab : ∀ a x : Fin 2, ∀ p < 16,
    vvec a x (embN (13 * x.val) p) = (vtab a x p : Rat) / (LAM : Rat) := by
  decide +kernel

/-- A rational given as (numerator, denominator). -/
def qOf (p : Int × Nat) : Rat := (p.1 : Rat) / (p.2 : Rat)

/-- Table of `Tr M_{a|x}`. -/
def Ttab (x a : Fin 2) : Rat := qOf (TtabData.getD (2 * x.val + a.val) (0, 1))
/-- Table of `(Tr_O M_{a|x}) i' i`. -/
def Ktab (x a : Fin 2) (i' i : Fin 8) : Rat :=
  qOf (KtabData.getD (128 * x.val + 64 * a.val + 8 * i'.val + i.val) (0, 1))
/-- Table of the four terms `Tr[W (M_{y|x} ⊗ M_{x|y})]`. -/
def trTab (x y : Fin 2) : Rat := qOf (trTabData.getD (2 * x.val + y.val) (0, 1))

/-- `Tr M_{a|x} = ∑_b v_b²`. -/
def traceQ (x a : Fin 2) : Rat :=
  sumR8 (fun i => sumR8 (fun o => sumR2 (fun r => vvec a x (i, (o, r)) * vvec a x (i, (o, r)))))

/-- `(Tr_O M_{a|x}) i' i = ∑_o v_{(i',o)} v_{(i,o)}`. -/
def ptraceQ (x a : Fin 2) (i' i : Fin 8) : Rat :=
  sumR8 (fun o => sumR2 (fun r => vvec a x (i', (o, r)) * vvec a x (i, (o, r))))

theorem traceQ_tab : ∀ x a : Fin 2, traceQ x a = Ttab x a := by decide +kernel

theorem ptraceQ_tab_0_0 : ∀ i' i : Fin 8, ptraceQ 0 0 i' i = Ktab 0 0 i' i := by decide +kernel
theorem ptraceQ_tab_0_1 : ∀ i' i : Fin 8, ptraceQ 0 1 i' i = Ktab 0 1 i' i := by decide +kernel
theorem ptraceQ_tab_1_0 : ∀ i' i : Fin 8, ptraceQ 1 0 i' i = Ktab 1 0 i' i := by decide +kernel
theorem ptraceQ_tab_1_1 : ∀ i' i : Fin 8, ptraceQ 1 1 i' i = Ktab 1 1 i' i := by decide +kernel

/-- `κ = (2^30 - 1) / 2^71`. -/
def kappaQ : Rat := 1073741823 / 2361183241434822606848

/-- One term `Tr[W (M_{y|x} ⊗ M_{x|y})]` from the tables. -/
def trTabQ (x y : Fin 2) : Rat :=
  1 / 64 * Ttab x y * Ttab y x
    + (sumR8 (fun i => sumR8 (fun i' =>
          Ktab x y i' i * (kappaQ * (Htab y x i i' : Rat) / ((LAM : Rat) * (LAM : Rat)))))
      + sumR8 (fun j => sumR8 (fun j' =>
          kappaQ * (Htab x y j j' : Rat) / ((LAM : Rat) * (LAM : Rat)) * Ktab y x j' j)))

theorem trTabQ_0_0 : trTabQ 0 0 = trTab 0 0 := by decide +kernel
theorem trTabQ_0_1 : trTabQ 0 1 = trTab 0 1 := by decide +kernel
theorem trTabQ_1_0 : trTabQ 1 0 = trTab 1 0 := by decide +kernel
theorem trTabQ_1_1 : trTabQ 1 1 = trTab 1 1 := by decide +kernel

theorem trTab_sum : 1 / 4 * ((trTab 0 0 + trTab 0 1) + (trTab 1 0 + trTab 1 1))
    = (valNum : Rat) / (valDen : Rat) := by
  decide +kernel

end GYNIProof
