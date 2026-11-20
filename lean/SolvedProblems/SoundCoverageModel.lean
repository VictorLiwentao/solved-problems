module

public import Mathlib.Data.Set.Defs

@[expose] public section

namespace SoundCoverage

/-- A language is a set of words in the universe numbered by the natural numbers. -/
abbrev Language := Set Nat
abbrev Family := Nat → Language
abbrev Learner := List Nat → Language

def Sub (A B : Language) := ∀ x, x ∈ A → x ∈ B
def Inside (s : List Nat) (A : Language) := ∀ x ∈ s, A x

/-- A full positive text, allowing repetitions. -/
def Enumerates (e : Nat → Nat) (A : Language) := ∀ x, A x ↔ ∃ k, e k = x

def history (e : Nat → Nat) (n : Nat) := (List.range n).map e

def Covers (L : Learner) (A : Language) (s : List Nat) :=
  ∀ x, A x → x ∉ s → L s x

def Learnable (H F : Family) :=
  ∃ L : Learner, ∀ i e, Enumerates e (H i) →
    ∃ N, ∀ n ≥ N, Covers L (H i) (history e n) ∧ Sub (L (history e n)) (F i)

def HasWitnesses (H F : Family) :=
  ∀ i, ∃ t : List Nat, Inside t (H i) ∧
    ∀ j, Inside t (H j) → Sub (H j) (H i) → Sub (H i) (F j)

end SoundCoverage
