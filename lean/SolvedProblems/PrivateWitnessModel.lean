module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace PrivateWitness
open scoped NNReal ENNReal

/-- A discrete probability law on a countable universe, represented by point masses. -/
structure Law where
  weight : Nat → ℝ≥0∞
  total : ∑' x, weight x = 1

instance : CoeFun Law (fun _ => Nat → ℝ≥0∞) := ⟨Law.weight⟩

def Law.support (p : Law) := {x | p x ≠ 0}

abbrev Rule := List Nat → Law

/-- Probability of an event in a discrete output law. -/
noncomputable def mass (p : Law) (E : Set Nat) : ℝ≥0∞ := by
  classical
  exact ∑' x, if x ∈ E then p x else 0

/-- Expectation after n further independent observations. Histories are newest first. -/
noncomputable def iid (p : Law) (f : List Nat → ℝ≥0∞) : Nat → List Nat → ℝ≥0∞
  | 0,h => f h
  | n+1,h => ∑' x, p x * iid p f n (x::h)

/-- Replace-one pure differential privacy with multiplicative budget k = exp ε. -/
def Private (G : Rule) (k : ℝ≥0) : Prop :=
  ∀ u v : List Nat, ∀ a b : Nat, ∀ E : Set Nat,
    mass (G (u ++ a::v)) E ≤ (k:ℝ≥0∞) * mass (G (u ++ b::v)) E

def Admissible (Ls : List (Set Nat)) (p : Law) : Prop :=
  (∃ L ∈ Ls, L ⊆ p.support) ∧ ∃ T : Finset Nat, (∀ x ∈ T, x ∉ p.support) ∧
    ∀ L ∈ Ls, ¬ L ⊆ p.support → ∃ x ∈ T, x ∈ L

/-- A geometric upper bound with a law-dependent multiplicative constant and base below one. -/
def Exponential (f : Nat → ℝ≥0∞) : Prop :=
  ∃ c r : ℝ≥0, r < 1 ∧ ∀ n, f n ≤ (c:ℝ≥0∞) * (r:ℝ≥0∞)^n

noncomputable def error (G : Rule) (p : Law) (n : Nat) : ℝ≥0∞ :=
  iid p (fun h => mass (G h) {x | x ∉ p.support ∨ x ∈ h}) n []

end PrivateWitness
