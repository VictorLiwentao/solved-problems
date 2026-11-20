module

public import SolvedProblems.GenerationThresholdModel

@[expose] public section

namespace SetDriven
open GenerationThreshold

abbrev Edges := Edge → Prop
abbrev Family := Nat → Language
abbrev Generator := List Edge → Nat

def obs (e : Nat → Edge) (n : Nat) := (List.range n).map e
def content (s : List Edge) : Edges := fun x => x ∈ s
def touches (p : Edge) (x : Nat) := p.lo = x ∨ p.hi = x
def present (H : Language) (e : Nat → Edge) :=
  (∀ k, crosses H (e k)) ∧ ∀ x, H x → ∃ k, touches (e k) x

def good (H : Language) (s : List Edge) (x : Nat) := H x ∧ fresh s x
def succeeds (H : Family) (G : Generator) :=
  ∀ j e, present (H j) e → ∃ N, ∀ n ≥ N, good (H j) (obs e n) (G (obs e n))

def compatibleWitnesses (H : Family) :=
  ∃ W : Nat → Edges → List Edge,
    (∀ j P, (∀ p, P p → crosses (H j) p) →
      (∀ x, H j x → ∃ p, P p ∧ touches p x) → ∀ p ∈ W j P, P p) ∧
    ∀ s : List Edge, ∃ x, ∀ j (P : Edges),
      (∀ p, P p → crosses (H j) p) → (∀ y, H j y → ∃ p, P p ∧ touches p y) →
      (∀ p ∈ W j P, p ∈ s) → (∀ p ∈ s, P p) → good (H j) s x

end SetDriven
