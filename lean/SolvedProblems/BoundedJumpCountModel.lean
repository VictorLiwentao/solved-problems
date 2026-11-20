module

public import SolvedProblems.BoundedJumpModel
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace BoundedJump

/-- Number of accepted words of length n when the rightmost letter is read from q. -/
def Machine.wordCount {α : Type} [Fintype α] (M : Machine α) (n : Nat) (q : M.State) : Nat :=
  (Finset.univ.filter (fun w : Fin n → α => M.accept ((List.ofFn w).foldr M.step q) = true)).card

end BoundedJump
