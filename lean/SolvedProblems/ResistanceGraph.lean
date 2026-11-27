module

public import SolvedProblems.ResistanceModel

@[expose] public section

namespace ResistanceLifts

/-- Number the three terminals first. Each side then contains four length-four
paths, with three fresh interior vertices on each path. -/
def base (n : ℕ) : Fin 39 := ⟨n % 39, Nat.mod_lt _ (by decide)⟩

def interior (s path pos : ℕ) : Fin 39 := base (3 + s * 12 + path * 3 + pos)

/-- The direct edge changes sheet on side zero exactly in the twisted graph. -/
def direct (twist : Bool) (s : ℕ) : Bool := twist && (s == 0)

/-- An explicit neighborhood list for the unweighted two-sheet lift. All sheet
changes on a long path are concentrated at its final edge. -/
def neighbors (t : Bool) (x : Vertex) : List Vertex :=
  let b := x.1.val
  let e := x.2
  if b < 3 then
    let prev := (b + 2) % 3
    [(base ((b+1)%3), xor e (direct t b)), (base prev, xor e (direct t prev))] ++
      (List.range 4).map (fun p => (interior b p 0, e)) ++
      (List.range 4).map (fun p => (interior prev p 2, xor e (!(direct t prev))))
  else
    let s := (b - 3) / 12
    let p := ((b - 3) / 3) % 4
    let k := (b - 3) % 3
    [(if k = 0 then base s else interior s p (k-1), e),
      if k = 2 then (base ((s+1)%3), xor e (!(direct t s))) else (interior s p (k+1), e)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem neighbors_valid : ∀ t : Bool, ∀ x : Vertex,
    (neighbors t x).Nodup ∧ x ∉ neighbors t x ∧
    ∀ y ∈ neighbors t x, x ∈ neighbors t y := by decide +kernel

def graph (t : Bool) : SimpleGraph Vertex where
  Adj x y := y ∈ neighbors t x
  symm := ⟨fun x y h => (neighbors_valid t x).2.2 y h⟩
  loopless := ⟨fun x => (neighbors_valid t x).2.1⟩

instance (t : Bool) : DecidableRel (graph t).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem neighborFinset_eq (t : Bool) (v : Vertex) :
    (graph t).neighborFinset v = (neighbors t v).toFinset := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, List.mem_toFinset]
  rfl

end ResistanceLifts
