module

public import SolvedProblems.DisplacementModel

@[expose] public section

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

end SetDensity
