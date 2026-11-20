module

public import SolvedProblems.BoundedJumpModel
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace BoundedJump

/-- None denotes the final value. A right/left offset has magnitude k + 1. -/
abbrev Letter (m : Nat) := Option (Bool × Fin m)

def Edge {m n : Nat} (w : Fin n → Letter m) (i j : Fin n) : Prop :=
  match w i with
  | none => False
  | some (true,k) => i.val + (k.val+1) = j.val
  | some (false,k) => j.val + (k.val+1) = i.val

/-- Closure under all sets of vertices defines reflexive reachability. -/
def Reach (w : Fin n → Letter m) (i j : Fin n) : Prop :=
  ∀ s : Fin n → Bool, s i = true → (∀ x y, s x = true → Edge w x y → s y = true) → s j = true

def Strict (w : Fin n → Letter m) (i j : Fin n) := Reach w i j ∧ i ≠ j

def Valid (w : Fin n → Letter m) : Prop :=
  (∀ x, w x ≠ none → ∃ y, Edge w x y) ∧
  (∀ x y, Reach w x y → Reach w y x → x = y) ∧
  (∀ x y, Reach w x y ∨ Reach w y x) ∧
  (∀ x y, Edge w x y ↔ Strict w x y ∧ ¬∃ z, Strict w x z ∧ Strict w z y)

/-- The pattern entries are visited in position order. Each new value goes
above or below each earlier one according to the pattern's ranks. -/
def OccursFrom (r : Fin n → Fin n → Prop) :
    List Nat → List (Nat × Fin n) → Prop
  | [], _ => True
  | a :: rest, prev => ∃ j, (∀ u ∈ prev, r u.2 j ∧
      (if u.1 < a then u.2 < j else if a < u.1 then j < u.2 else False)) ∧
      OccursFrom r rest ((a,j) :: prev)

def Avoid (B : List (List Nat)) (r : Fin n → Fin n → Prop) :=
  ∀ p ∈ B, ¬OccursFrom r p []

def Counted (m : Nat) (B : List (List Nat)) {n : Nat} (p : Equiv.Perm (Fin n)) : Prop :=
  (∀ i j, (p i).val+1 = (p j).val → Nat.dist i.val j.val ≤ m) ∧
    Avoid B (fun i j => p i < p j)

end BoundedJump
