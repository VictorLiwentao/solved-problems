module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Finset.Card

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace ProcessSeparation

/-- The deterministic instance at round t is t, so the observed labels determine the history. -/
abbrev Stream := ℕ → ℕ

abbrev Strategy := (t : ℕ) → (Fin t → ℕ) → ℕ

def prediction (A : Strategy) (y : Stream) (t : ℕ) : ℕ :=
  A t (fun i ↦ y i)

/-- Number of mistakes on rounds zero through T−1. -/
def mistakes (p y : Stream) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t ↦ p t ≠ y t)).card

noncomputable def loss (p y : Stream) (T : ℕ) : ℝ :=
  (mistakes p y T : ℝ) / T

/-- Each finite observed prefix is realized by a member of the concept class. -/
def Realizable (H : Set Stream) (y : Stream) : Prop :=
  ∀ T : ℕ, ∃ f ∈ H, ∀ t < T, f t = y t

end ProcessSeparation
