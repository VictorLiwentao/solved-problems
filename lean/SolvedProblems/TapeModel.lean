module

@[expose] public section

namespace TapeInclusion
abbrev Word := List Bool

def copies (u : Word) : Nat → Word :=
  Nat.rec [] (fun _ previous => u ++ previous)

def primitive (u : Word) := ∀ v k, copies v k = u → k ≤ 1

/-- Two outward-facing stars with their initial, intervening and terminal walls. -/
structure Half where
  start : Word
  first : Word
  middle : Word
  second : Word
  finish : Word

def accepts (h : Half) (w : Word) := ∃ i j,
  w = h.start ++ copies h.first i ++ h.middle ++ copies h.second j ++ h.finish

def aligned (h : Half) := (h.middle = [] ∨ h.first.head? ≠ h.middle.head?) ∧
  (h.finish = [] ∨ h.second.head? ≠ h.finish.head?)

def target : Half := ⟨[],[false,false,true],[],[false,true,true],[]⟩
def source : Half := ⟨[false],[false,true,false],[true,true],[false,true,true],[]⟩

end TapeInclusion
