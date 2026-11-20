module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace SingletonDensity

/-- Ranks start at zero. This is the number of points of A among the first n ranks. -/
noncomputable def cnt (A : Set Nat) (n : Nat) : Nat := by
  classical
  exact ((Finset.range n).filter (fun x => x ∈ A)).card

/-- The set of ranks has asymptotic density a. -/
def Exact (A : Set Nat) (a : ℝ) := ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n ≥ N,
  (a - ε) * n ≤ (cnt A n : ℝ) ∧ (cnt A n : ℝ) ≤ (a + ε) * n

/-- The lower asymptotic density is at least a. -/
def Lower (A : Set Nat) (a : ℝ) := ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n ≥ N,
  (a - ε) * n ≤ (cnt A n : ℝ)

/-- The upper asymptotic density is at most a. -/
def Upper (A : Set Nat) (a : ℝ) := ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n ≥ N,
  (cnt A n : ℝ) ≤ (a + ε) * n

/-- History of the first n adversary moves, most recent first. -/
def seenPrefix (e : Nat → Nat) : Nat → List Nat :=
  Nat.rec [] (fun n h => e n :: h)

/-- A strategy receives the entire enumerated history; none represents output outside the target. -/
abbrev Strategy := List Nat → Option Nat

/-- A generator may repeat a past output but must avoid all input ranks seen so far. -/
def Legal (G : Strategy) := ∀ h : List Nat, h.Nodup → ∀ x ∈ h, G h ≠ some x

/-- The set of target ranks ever output after observing the current adversary move. -/
def Outputs (G : Strategy) (e : Nat → Nat) : Set Nat :=
  {x | ∃ t, G (seenPrefix e (t+1)) = some x}

/-- For every exact core density between zero and one half, a set-driven generator
attains the complementary lower density. Every legal deterministic generator admits
an injective enumeration at that core density bounding even its upper output density. -/
theorem minimax {a : ℝ} (ha : 0 ≤ a) (aHalf : a ≤ 1/2) :
    (∃ F : Finset Nat → Nat, Legal (fun h => some (F h.toFinset)) ∧
      ∀ e : Nat → Nat, Function.Injective e → Exact (Set.range e) a →
        Lower (Outputs (fun h => some (F h.toFinset)) e) (1-a)) ∧
    (∀ G : Strategy, Legal G → ∃ e : Nat → Nat, Function.Injective e ∧
      Exact (Set.range e) a ∧ Upper (Outputs G e) (1-a)) := by
  sorry

end SingletonDensity
