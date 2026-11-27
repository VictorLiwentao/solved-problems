module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section

open Set MeasureTheory
open scoped Cardinal unitInterval ENNReal

namespace BinaryBandit

abbrev Arm := unitInterval
abbrev Strategy (Ω : Type*) := (t : ℕ) → (Fin t → Bool) → Ω → Arm

/-- An arm is queried after each binary transcript. At the budget the same
prescription gives the output. All choices can share a single random seed. -/
noncomputable def transcript {Ω : Type*} (A : Strategy Ω) (U : Set Arm) (ω : Ω) :
    (t : ℕ) → Fin t → Bool
  | 0 => Fin.elim0
  | t + 1 => by
    classical
    exact Fin.snoc (transcript A U ω t) (decide (A t (transcript A U ω t) ω ∈ U))

/-- The zero target and the indicators of open sets whose complements have
cardinality at most the first uncountable cardinal. -/
def Eligible (U : Set Arm) : Prop :=
  U = ∅ ∨ (U.Nonempty ∧ IsOpen U ∧ #(↥(Uᶜ)) ≤ ℵ₁)

/-- Under the zero target, every arm is optimal. Otherwise the expected reward
deficit is the probability that the output is outside the winning set. -/
def failure {Ω : Type*} (A : Strategy Ω) (m : ℕ) (U : Set Arm) : Set Ω :=
  {ω | U.Nonempty ∧ A m (transcript A U ω m) ω ∉ U}

def Learnable : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ (m : ℕ) (Ω : Type) (_s : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧ ∃ A : Strategy Ω,
        (∀ t h, Measurable (A t h)) ∧ ∀ U, Eligible U → μ (failure A m U) ≤ ε

end BinaryBandit
