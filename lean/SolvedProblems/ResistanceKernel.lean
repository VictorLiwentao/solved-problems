module

public import SolvedProblems.ResistanceGraph

@[expose] public section

namespace ResistanceLifts

/-- The terminals met at either end of the long path containing `x`, and the
distance from its left end. A terminal has zero distance and both ends equal. -/
structure Ends where
  left : Vertex
  right : Vertex
  pos : ℕ

def ends (t : Bool) (x : Vertex) : Ends :=
  let b := x.1.val
  if b < 3 then ⟨x, x, 0⟩ else
    let s := (b-3)/12
    ⟨(base s, x.2), (base ((s+1)%3), xor x.2 (!(direct t s))), (b-3)%3 + 1⟩

def commonPath (x y : Vertex) : Bool :=
  3 ≤ x.1.val && 3 ≤ y.1.val && (x.1.val-3)/3 == (y.1.val-3)/3 && x.2 == y.2

/-- The terminal Schur complement is the Laplacian of the complete tripartite
K₂,₂,₂. Its inverse on zero-mean terminal loads, multiplied by 72. -/
def terminalGreen (x y : Vertex) : ℤ :=
  if x.1 != y.1 then -2 else if x.2 == y.2 then 13 else -5

/-- Green kernel multiplied by 1152. Linearly interpolate from each pair of
endpoints, then add the length-four Dirichlet kernel for a common path interior. -/
def green (t : Bool) (x y : Vertex) : ℤ :=
  let a := ends t x
  let b := ends t y
  let p : ℤ := a.pos
  let q : ℤ := b.pos
  (4-p)*((4-q)*terminalGreen a.left b.left + q*terminalGreen a.left b.right) +
    p*((4-q)*terminalGreen a.right b.left + q*terminalGreen a.right b.right) +
    (if commonPath x y then 288 * min p q * (4-max p q) else 0)

/-- Kirchhoff's equation with a source at `z` and one sixth of the return current
at each terminal, in the same integer scaling as `green`. -/
def columnHolds (t : Bool) (z x : Vertex) : Prop :=
  (neighbors t x).length * green t x z - ((neighbors t x).map fun y => green t y z).sum =
    (if x = z then 1152 else 0) - (if x.1.val < 3 then 192 else 0)

instance (t : Bool) (z x : Vertex) : Decidable (columnHolds t z x) :=
  inferInstanceAs (Decidable ((_ : ℤ) = _))

/-- Raw resistance numerator as the voltage drop of the difference of columns. -/
def numerator (t : Bool) (x y : Vertex) : ℤ :=
  (green t x x - green t x y) - (green t y x - green t y y)

end ResistanceLifts
