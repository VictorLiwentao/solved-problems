module

@[expose] public section

namespace TwoGuess

/-- Vertices are grouped by block. Extra vertex labels outside the first n
have private words only, so need no special encoding as a dependent type. -/
abbrev Vertex := Nat × Nat
inductive Word where
  | privateWord (v : Vertex) (height : Nat)
  | edgeWord (block left right serial : Nat)
  deriving DecidableEq

def belongs (v : Vertex) : Word → Prop
  | .privateWord u _ => u = v
  | .edgeWord n a b r => a < b ∧ b < n ∧ r < n ∧ (v = (n,a) ∨ v = (n,b))

end TwoGuess
