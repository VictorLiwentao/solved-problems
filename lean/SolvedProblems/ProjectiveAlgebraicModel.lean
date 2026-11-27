module

public import SolvedProblems.ProjectiveTransferModel
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes

variable (L : Language) {M ι : Type*} [L.Structure M]

/-- Append one distinguished element to a parameter tuple. -/
def point (x : ι → M) (a : M) : ι ⊕ Unit → M := Sum.elim x fun _ => a

/-- A unary definable set, with its displayed finite parameter tuple. -/
def locus (x : ι → M) (φ : L.Formula (ι ⊕ Unit)) : Set M :=
  {a | φ.Realize (point x a)}

/-- The algebraic closure of a tuple consists of the elements of finite
unary sets defined over precisely those parameters. -/
def tupleClosure (x : ι → M) : Set M :=
  {a | ∃ φ : L.Formula (ι ⊕ Unit), a ∈ locus L x φ ∧ (locus L x φ).Finite}

/-- Every unary set definable with finitely many parameters is finite or cofinite. -/
def Minimal (M : Type*) [L.Structure M] : Prop :=
  ∀ (ι : Type) [Finite ι] (x : ι → M) (φ : L.Formula (ι ⊕ Unit)),
    (locus L x φ).Finite ∨ (locus L x φ)ᶜ.Finite

/-- Algebraic closure on arbitrary parameter sets has finite character by definition. -/
def acl (S : Set M) : Set M :=
  {a | ∃ (n : ℕ) (x : Fin n → M), Set.range x ⊆ S ∧ a ∈ tupleClosure L x}

end ProjectiveAlgebraic
