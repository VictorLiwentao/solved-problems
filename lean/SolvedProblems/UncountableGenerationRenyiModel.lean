module

public import SolvedProblems.UncountableGenerationModel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open MeasureTheory Set Function
namespace UncountableGeneration

/-- The finite-partition definition of a bounded Rényi divergence at order α>1.
One can include a leftover cell to complete any disjoint finite family to a partition.
Absolute continuity handles zero-probability cells. -/
def RenyiBudget (P : Rule) (α D : ℝ) : Prop :=
  ∀ x y, Neighbors x y → (P x) ≪ (P y) ∧
    ∀ (n : ℕ) (E : Fin n → Set Output), Pairwise (Disjoint on E) →
      (∀ j, MeasurableSet (E j)) →
        (∑ j, ((P x).real (E j)) ^ α / ((P y).real (E j)) ^ (α-1))
          ≤ Real.exp ((α-1)*D)

end UncountableGeneration
