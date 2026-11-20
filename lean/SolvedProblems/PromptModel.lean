module

public import SolvedProblems.SoundCoverageModel

@[expose] public section

namespace PromptGeneration
open SoundCoverage

variable {Y : Type}
structure Round (Y : Type) where
  word : Nat
  label : Y
  request : Y

def trace {α} (e : Nat → α) (n : Nat) := (List.range (n+1)).map e

def ordinary (B : Language → Prop) := ∃ G : List Nat → Nat,
  ∀ A, B A → ∀ e, Enumerates e A → ∃ N, ∀ n ≥ N,
    A (G (trace e n)) ∧ G (trace e n) ∉ trace e n

def fiber (h : Nat → Y) (y : Y) (x : Nat) := h x = y

def prompted (C : (Nat → Y) → Prop) := ∃ G : List (Round Y) → Y → Nat,
  ∀ h, C h → ∀ e : Nat → Round Y, (∀ i, (e i).label = h (e i).word) →
    ∀ y, (∀ x, h x = y → ∃ i, (e i).word = x) → ∃ N, ∀ n ≥ N,
      (e n).request = y →
      let w := G (trace e n) y
      h w = y ∧ ∀ i ≤ n, (e i).word ≠ w

def unbounded (A : Language) := ∀ b, ∃ x, b < x ∧ A x

end PromptGeneration
