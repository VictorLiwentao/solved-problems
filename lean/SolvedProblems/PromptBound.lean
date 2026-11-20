module

public import SolvedProblems.PromptBoundExtraction
public import SolvedProblems.PromptBoundSelector
public import SolvedProblems.PromptBoundFair

public section
namespace PromptBound

/-- For a uniformly decidable indexed family of infinite languages, an effective
length bound on every possible unordered sample and prompt is precisely what
permits almost-sure eventual generation. A deterministic generator suffices. -/
theorem lengthCriterion {q : ℕ} (C : Family q) (X : Oracle) (μ : FairLaw)
    (mem : Computable (fun z : ℕ × Word q => C z.1 z.2))
    (inf : ∀ i, {w | C i w = true}.Infinite) :
    (RandomGenerates C X μ ↔ LengthBound C X) ∧
    (LengthBound C X ↔ DetGenerates C X) := by
  have rb := random_to_bound C X μ inf
  have bd := bound_to_det C X mem
  have dr := det_to_random C X μ
  exact ⟨⟨rb,fun h => dr (bd h)⟩,⟨bd,fun h => rb (dr h)⟩⟩

end PromptBound
