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

/-- The intersection with K's first D(t) words contains at least t distinct elements. -/
def Fits (J K : Language) (D : Nat → Nat) (b : Nat) :=
  ∀ t ≥ b, ∃ w : List Nat, w.Nodup ∧ w.length = t ∧ Inside w J ∧
    ∀ x ∈ w, K.Has x ∧ x < K.word (D t)

end Displacement

namespace SetDensity
open Displacement

/-- A set-valued output is a predicate on the ordered universe of words. -/
abbrev Output := Nat → Prop

/-- The lower density of A within K is at least p/q. For every smaller nonnegative
rational a/d, all sufficiently long initial segments of K contain at least a/d of
their length in distinct members of A. Only positive denominators are used. -/
def AtLeast (A : Output) (K : Language) (p q : Nat) :=
  ∀ a d, 0 < d → a*q < p*d → ∃ R, ∀ r ≥ R,
    ∃ w : List Nat, w.Nodup ∧ (∀ x ∈ w, A x ∧ K.Has x ∧ x < K.word r) ∧ a*r ≤ d*w.length

/-- Each target's level is specified by its positive rational lower cut.
For a real endpoint cᵢ, take level i p q to mean p/q < cᵢ. -/
abbrev Levels := Nat → Nat → Nat → Prop

/-- Every output is infinite. On each legal text the outputs are eventually
contained in its target and their lower densities attain every rational below
the prescribed endpoint in the limit inferior. -/
def Succeeds (L : Nat → Language) (D : Nat → Nat) (level : Levels)
    (G : List Nat → Output) :=
  (∀ s (f : List Nat), ∃ x, G s x ∧ x ∉ f) ∧ ∀ i e, Text D (L i) e →
    (∃ N, ∀ n ≥ N, ∀ x, G (history e n) x → (L i).Has x) ∧
    ∀ p q, level i (p+1) (q+1) → ∃ N, ∀ n ≥ N, AtLeast (G (history e n)) (L i) (p+1) (q+1)

/-- Each target, starting round, and positive rational lower threshold has a
finite positive sample forcing that density on every feasible subtarget. -/
def Witnesses (L : Nat → Language) (D : Nat → Nat) (level : Levels) :=
  ∀ i b p q, level i (p+1) (q+1) → ∃ T : List Nat, Inside T (L i) ∧
    ∀ j, Inside T (L j) → Sub (L j) (L i) → Fits (L j) (L i) D (b+1) →
      AtLeast (L j).Has (L i) (p+1) (q+1)

/-- Full bounded-displacement texts admit set-valued generation at the prescribed
target-specific lower densities exactly when all rational thresholds have finite witnesses.
Whenever attainable, these guarantees can be attained from the current seen set alone, with every output disjoint from that set. -/
theorem densityCriterion (L : Nat → Language) (D : Nat → Nat) (level : Levels)
    (nondecreasing : ∀ i j, i ≤ j → D i ≤ D j) (growth : ∀ t, t ≤ D t)
    (positive : ∀ i, ∃ p q, level i (p+1) (q+1)) :
    ((∃ G, Succeeds L D level G) ↔ SetDensity.Witnesses L D level) ∧
    (SetDensity.Witnesses L D level ↔
      ∃ F : Output → Output, (∀ S x, F S x → ¬ S x) ∧
        Succeeds L D level (fun s => F (fun x => x ∈ s))) := by sorry

end SetDensity
