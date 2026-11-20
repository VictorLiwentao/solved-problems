module

public import Std

@[expose] public section

namespace Displacement

/-- The increasing enumeration of an infinite language on a naturally indexed universe. -/
structure Language where
  word : Nat → Nat
  ordered : ∀ {a b}, a < b → word a < word b

def Language.Has (K : Language) (x : Nat) := ∃ r, K.word r = x

def Same (J K : Language) := ∀ x, J.Has x ↔ K.Has x
def Sub (J K : Language) := ∀ x, J.Has x → K.Has x
def Inside (s : List Nat) (K : Language) := ∀ x ∈ s, K.Has x

def history (e : Nat → Nat) (t : Nat) := (List.range t).map e

/-- D(t) = floor(M t) in the paper. Ranks start at zero, rounds at one. -/
def Text (D : Nat → Nat) (K : Language) (e : Nat → Nat) :=
  (∀ a b, e a = e b → a = b) ∧
  (∀ x, K.Has x ↔ ∃ k, e k = x) ∧
  ∃ b, ∀ k ≥ b, e k < K.word (D (k+1))

def Identifiable (L : Nat → Language) (D : Nat → Nat) :=
  ∃ G : List Nat → Nat, ∀ j e, Text D (L j) e →
    ∃ N, ∀ n ≥ N, Same (L (G (history e n))) (L j)

/-- The intersection with K's first D(t) words contains at least t distinct elements. -/
def Fits (J K : Language) (D : Nat → Nat) (b : Nat) :=
  ∀ t ≥ b, ∃ w : List Nat, w.Nodup ∧ w.length = t ∧ Inside w J ∧
    ∀ x ∈ w, K.Has x ∧ x < K.word (D t)

def Witnesses (L : Nat → Language) (D : Nat → Nat) :=
  ∀ i b, 1 ≤ b → ∃ T : List Nat, Inside T (L i) ∧
    ∀ j, Inside T (L j) → Sub (L j) (L i) → Fits (L j) (L i) D b → Same (L j) (L i)

end Displacement
