module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace BoundedJump

/-- A deterministic word automaton scanning from right to left. -/
structure Machine (α : Type) where
  State : Type
  finite : Fintype State
  eqState : DecidableEq State
  start : State
  step : α → State → State
  accept : State → Bool

def Machine.accepts (M : Machine α) (w : List α) : Bool :=
  M.accept (w.foldr M.step M.start)

end BoundedJump
