module

public import SolvedProblems.PrivateWitnessNecessity
public import SolvedProblems.PrivateWitnessSampler

public section

namespace PrivateWitness
open scoped NNReal ENNReal

/-- A finite nonempty family admits pure private, exponentially accurate generation
at every admissible law exactly when its languages have infinite common intersection. -/
theorem finiteFamily (Ls : List (Set Nat)) (nonempty : Ls ≠ [])
    (infinite : ∀ L ∈ Ls, L.Infinite) (k : ℝ≥0) (budget : 1 < k) :
    (∃ G : Rule, Private G k ∧ ∀ p, Admissible Ls p → Exponential (error G p)) ↔
    {x | ∀ L ∈ Ls, x ∈ L}.Infinite := by
  constructor
  · rintro ⟨G,priv,success⟩
    exact common_infinite Ls nonempty infinite priv success
  · exact common_sampler Ls k budget.le

end PrivateWitness
