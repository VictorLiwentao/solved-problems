module

public import SolvedProblems.ProjectiveElementary
public import SolvedProblems.ProjectiveHomogeneity

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveIndiscernibles ProjectiveBlocks Function

/-- A noninjective self-surjection on finite/cofinite codes forces algebraic
closure in its graph language to be nondegenerate, provided the infinite graph
structure has finite type spectra and finite/cofinite unary definable sets. -/
theorem nondegenerateClosure {M : Type*} [Infinite M] (k : ℕ) (f : Codes M k → Codes M k) :
    letI := graphStructure f
    FiniteTypes (graphLanguage k) M → Minimal (graphLanguage k) M →
      Surjective f → ¬ Injective f → ¬ Degenerate (graphLanguage k) M := by
  let := graphStructure f
  intro fin min surj collision deg
  obtain ⟨c,d,_,s,eq,block⟩ := symmetricBlockModel fin min deg
  let := s
  exact collision (obstructionOfBlockModel c d k f block eq surj)

end ProjectiveTransfer
