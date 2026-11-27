module

public import SolvedProblems.ResistanceKernel

@[expose] public section

namespace ResistanceLifts

abbrev Terminal := Fin 3 × Bool

def terminal (z : Terminal) : Vertex := (base z.1.val, z.2)

/-- Direct terminals form two triangles or one hexagon. A long path between
opposite direct sheets has length four. -/
def terminalDistance (t : Bool) (x z : Vertex) : ℕ :=
  if x = z then 0 else if t then
    if x.1 = z.1 then 3 else
      let twist := (x.1.val == 0 && z.1.val == 1) || (x.1.val == 1 && z.1.val == 0)
      if xor x.2 z.2 == twist then 1 else 2
  else if x.2 == z.2 then 1 else if x.1 == z.1 then 5 else 4

/-- The two routes from an interior vertex to a specified terminal. -/
def distanceTo (t : Bool) (x : Vertex) (z : Terminal) : ℕ :=
  let a := ends t x
  if x.1.val < 3 then terminalDistance t x (terminal z) else
    min (a.pos + terminalDistance t a.left (terminal z))
      (4-a.pos + terminalDistance t a.right (terminal z))

/-- A shortest path potential has a unit descent step away from its zero and
changes by at most one across every edge. -/
def distanceCheck (t : Bool) (z : Terminal) (x : Vertex) : Prop :=
  let d := fun v => distanceTo t v z
  (d x = 0 ↔ x = terminal z) ∧
    (∀ y ∈ neighbors t x, d x ≤ d y + 1) ∧
    (x ≠ terminal z → ∃ y ∈ neighbors t x, d y + 1 = d x)

instance (t : Bool) (z : Terminal) (x : Vertex) : Decidable (distanceCheck t z x) := by
  unfold distanceCheck
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem distance_valid : ∀ t z x, distanceCheck t z x := by decide +kernel

end ResistanceLifts
