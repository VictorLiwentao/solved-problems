module

public import SolvedProblems.ProjectiveTypesCard
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic

variable {d : ℕ} {M : Type*} {κ ι : Type} (L : Language) [L.Structure M]

/-- One tuple lists the finite core followed by all positions in the designated blocks. -/
def marked (core : κ → M) (B : ℚ → Fin d → M) (m : ι → ℚ) : κ ⊕ (ι × Fin d) → M :=
  Sum.elim core fun ij => B (m ij.1) ij.2

/-- The full first-order type of an extra enumerated block over the marked ones. -/
def overMarks (core : κ → M) (B : ℚ → Fin d → M) (m : ι → ℚ) (t : ℚ) :=
  tupleType L (Sum.elim (marked core B m) (B t))

/-- Ordered indiscernibility over the named core, stated using increasing embeddings
of the rationals. Parameters can list their blocks in any order. -/
def OrderIndiscernible (core : κ → M) (B : ℚ → Fin d → M) : Prop :=
  ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (f : ℚ → ℚ), StrictMono f →
    tupleType L (marked core B m) = tupleType L (marked core B (f ∘ m))

/-- The distinguished point of an unmarked block is generic over the core and
all positions of the finitely many marked blocks. -/
def IndependentBlocks (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) : Prop :=
  ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (t : ℚ), t ∉ Set.range m →
    B t i₀ ∉ tupleClosure L (marked core B m)

/-- Every position in a block is algebraic over its distinguished point. -/
def AlgebraicBlocks (B : ℚ → Fin d → M) (i₀ : Fin d) : Prop :=
  ∀ t j, B t j ∈ tupleClosure L (fun _ : Unit => B t i₀)

end ProjectiveIndiscernibles
