module

public import Std

@[expose] public section

namespace PositiveWitness

/-- anchorPart distinguishes A or B, and whether satellites contain the part.
stripe s 0 is S or T; stripe s (j+1) is the indexed block Xⱼ or Yⱼ. -/
inductive Word
  | anchorPart (side included : Bool) (row : Nat)
  | stripe (side : Bool) (slot row : Nat)
  | neutralCore (row : Nat)
  | partner (side : Bool) (index : Nat)
  deriving DecidableEq, Repr

def rank : Word → Nat
  | .stripe _ k r => max k r
  | .anchorPart _ _ r | .neutralCore r | .partner _ r => r

inductive Target
  | anchor (side : Bool)
  | satellite (side : Bool) (index : Nat)
  deriving DecidableEq, Repr

/-- Finite increasing core squares exhaust C, as do the prefixes Pₘ in the paper. -/
def member : Target → Word → Bool
  | .anchor a, .anchorPart b _ _ => a == b
  | .anchor _, .partner .. => false
  | .anchor _, _ => true
  | .satellite _ _, .anchorPart _ inc _ => inc
  | .satellite b j, .partner s i => (b == s) && decide (j ≠ i)
  | .satellite _ j, .neutralCore r => decide (r ≤ j)
  | .satellite b j, .stripe s k r =>
      decide (k ≤ j ∧ r ≤ j) ||
        (if k = 0 then b == s else (b == s) == (decide (k = j+1)))

abbrev Edges := Word → Word → Prop
def observed (s : List (Word × Word)) : Edges := fun x y =>
  (x,y) ∈ s ∨ (y,x) ∈ s
def seen (E : Edges) (x : Word) := ∃ y, E x y
def honest (h : Target) (e : Word × Word) := member h e.1 ≠ member h e.2
def consistent (h : Target) (E : Edges) := ∀ x y, E x y → member h x ≠ member h y

def prefixEdges (e : Nat → Word × Word) (n : Nat) := observed ((List.range (n+1)).map e)
def generates := ∃ G : Edges → Word, ∀ h (e : Nat → Word × Word),
  (∀ i, honest h (e i)) → (∀ x, member h x → ∃ i, (e i).1 = x ∨ (e i).2 = x) →
  ∃ N, ∀ n ≥ N, member h (G (prefixEdges e n)) ∧ ¬ seen (prefixEdges e n) (G (prefixEdges e n))

def active (W : Target → List Word) (E : Edges) (h : Target) :=
  consistent h E ∧ ∀ x ∈ W h, seen E x

def compatible := ∃ W : Target → List Word, (∀ h x, x ∈ W h → member h x) ∧
  ∀ s : List (Word × Word), (∃ h, active W (observed s) h) →
    ∃ x, ¬ seen (observed s) x ∧ ∀ h, active W (observed s) h → member h x

end PositiveWitness
