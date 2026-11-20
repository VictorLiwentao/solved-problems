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

/-- One is the universal upper bound on regret at every finite horizon. -/
theorem regret_upper (p f y : Stream) (T : ℕ) : loss p y T - loss f y T ≤ 1 := by sorry

/-- Proposition on realizable versus agnostic learning. For every diverging mistake
budget, one closed class on the deterministic enumeration is learnable within that
budget. Against each causal randomized learner there is a fixed sequence and a
single comparator of loss tending to zero for which regret tends to one almost surely. -/
theorem separation (g : ℕ → ℝ) (nonneg : ∀ T, 0 ≤ g T) (mono : Monotone g)
    (diverges : Tendsto g atTop atTop) :
    ∃ (H : Set Stream) (A : Strategy), H.Nonempty ∧ IsClosed H ∧
      (∀ y : Stream, Realizable H y → ∀ T, (mistakes (prediction A y) y T : ℝ) ≤ g T) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (R : (t : ℕ) → (Fin t → ℕ) → Ω → ℕ) (_ : ∀ t h, Measurable (R t h)),
        ∃ (y f : Stream), f ∈ H ∧ Tendsto (loss f y) atTop (𝓝 0) ∧
          ∀ᵐ ω ∂μ, Tendsto
            (fun T ↦ loss (fun t ↦ R t (fun i ↦ y i) ω) y T - loss f y T) atTop (𝓝 1)
    := by sorry

end ProcessSeparation
