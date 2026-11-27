module

public import SolvedProblems.EMXModel
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace EMX

open MeasureTheory Set
open scoped ENNReal

/-- Every subset of the countable domain is measurable. -/
scoped instance pointSpace : MeasurableSpace Point := ⊤
scoped instance discretePointSpace : DiscreteMeasurableSpace Point := ⟨fun _ => trivial⟩

abbrev Learner := (m : ℕ) → (Fin m → Point) → Hyp

def deficitEvent (A : Learner) (μ : Measure Point) (m : ℕ) (ε : ℝ) : Set (Fin m → Point) :=
  {xs | ∃ h : Hyp, μ.real (support (A m xs) : Set Point) + ε < μ.real (support h : Set Point)}

/-- A single proper learner works for all accuracies and confidence levels on all
probability laws under their ordinary independent product sampling measures. -/
def Learnable : Prop := ∃ A : Learner, ∀ ε δ : ℝ, 0 < ε → 0 < δ →
  ∃ M : ℕ, ∀ m ≥ M, ∀ μ : Measure Point, IsProbabilityMeasure μ →
    Measure.pi (fun _ : Fin m => μ) (deficitEvent A μ m ε) ≤ ENNReal.ofReal δ

end EMX
