import Mathlib

/-!
# Finite-dimensional bipartite process matrices, instruments and the GYNI value

Conventions (exactly those of `iqoqi/programs/gyni/verify_strategy.py`):

* A party has an input space `ℂ^I` and an output space `ℂ^O` (finite types `I`, `O`). A linear map
  `𝓜 : L(ℂ^I) → L(ℂ^O)` is represented by its Choi matrix
  `M = ∑_{i,j} |i⟩⟨j| ⊗ 𝓜(|i⟩⟨j|)` on `I × O`, i.e. `M (i, o) (j, o') = ⟨o| 𝓜(|i⟩⟨j|) |o'⟩`.
  `𝓜` is completely positive iff `M` is positive semidefinite, and trace preserving iff the
  partial trace over the output is the identity: `Tr_O M = 1_I` (`ptraceOut`).
* A bipartite process matrix (Oreshkov–Costa–Brukner) is a positive semidefinite `W` on
  `(AI × AO) × (BI × BO)` with `Tr[W (M ⊗ N)] = 1` for all CPTP Choi matrices `M` (Alice) and
  `N` (Bob) (`IsProcess`).
* An instrument with settings `x` and outcomes `a` is a family of CP maps `M x a` (positive
  semidefinite Choi matrices) whose sum over the outcomes is trace preserving, for each setting
  (`IsInstrument`).
* Correlations: `p(a, b | x, y) = Tr[W (M_{a|x} ⊗ N_{b|y})]` (`prob`, real part; for a process
  matrix and instruments this trace is real and nonnegative).
* GYNI ("guess your neighbour's input", settings and outcomes in `Fin 2`):
  `I_GYNI = ¼ ∑_{x,y} p(a = y, b = x | x, y)` (`gyniValue`).

The Kronecker product `M ⊗ₖ N` (`Matrix.kroneckerMap (· * ·)`) is indexed by `(AI × AO) × (BI × BO)`, the ordering
of `verify_strategy.py` (`np.kron`).
-/

namespace GYNIProof

open Matrix
open scoped ComplexOrder Kronecker

/-- Partial trace over the output factor: `(Tr_O M) i j = ∑_o M (i, o) (j, o)`. -/
def ptraceOut {I O R : Type*} [Fintype O] [AddCommMonoid R] (M : Matrix (I × O) (I × O) R) :
    Matrix I I R :=
  Matrix.of fun i j => ∑ o, M (i, o) (j, o)

/-- `M` is the Choi matrix of a completely positive trace-preserving map `L(ℂ^I) → L(ℂ^O)`. -/
def IsCPTP {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (M : Matrix (I × O) (I × O) ℂ) : Prop :=
  M.PosSemidef ∧ ptraceOut M = 1

/-- `W` is a valid bipartite process matrix: `W ≥ 0` and `Tr[W (M ⊗ N)] = 1` for all CPTP
Choi matrices `M` of Alice and `N` of Bob. -/
def IsProcess {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
    [DecidableEq AI] [DecidableEq BI]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) : Prop :=
  W.PosSemidef ∧ ∀ (M : Matrix (AI × AO) (AI × AO) ℂ) (N : Matrix (BI × BO) (BI × BO) ℂ),
    IsCPTP M → IsCPTP N → (W * (M ⊗ₖ N)).trace = 1

/-- Alias of `IsProcess`. -/
abbrev IsValidProcess {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
    [DecidableEq AI] [DecidableEq BI]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ) : Prop :=
  IsProcess W

/-- `M x a` (setting `x`, outcome `a`) is an instrument: every `M x a` is the Choi matrix of a
CP map, and for every setting `x` the sum `∑_a M x a` is trace preserving. -/
def IsInstrument {I O X A : Type*} [Fintype I] [Fintype O] [DecidableEq I] [Fintype A]
    (M : X → A → Matrix (I × O) (I × O) ℂ) : Prop :=
  ∀ x, (∀ a, (M x a).PosSemidef) ∧ ptraceOut (∑ a, M x a) = 1

/-- Correlations `p(a, b | x, y) = Tr[W (M_{a|x} ⊗ N_{b|y})]` (real part). -/
noncomputable def prob {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI] [Fintype BO]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) (a b x y : Fin 2) : ℝ :=
  ((W * (M x a ⊗ₖ N y b)).trace).re

/-- The GYNI value `¼ ∑_{x,y} p(a = y, b = x | x, y)`. -/
noncomputable def gyniValue {AI AO BI BO : Type*} [Fintype AI] [Fintype AO] [Fintype BI]
    [Fintype BO]
    (W : Matrix ((AI × AO) × (BI × BO)) ((AI × AO) × (BI × BO)) ℂ)
    (M : Fin 2 → Fin 2 → Matrix (AI × AO) (AI × AO) ℂ)
    (N : Fin 2 → Fin 2 → Matrix (BI × BO) (BI × BO) ℂ) : ℝ :=
  (1 / 4 : ℝ) * ∑ x : Fin 2, ∑ y : Fin 2, prob W M N y x x y

end GYNIProof
