module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Germ.Basic

@[expose] public section

namespace SolvedProblems.PartitionRamsey

open Filter

/-- Subsets of the countable atom set, identified when they differ at only finitely many atoms.
The germ order on predicates is inclusion outside a finite set. -/
abbrev ModFinite := Germ (cofinite : Filter ℕ) Prop

def classOf (s : Set ℕ) : ModFinite := Germ.ofFun s

/-- The fibres of a finite colouring are the blocks of a finite partition. A family of
classes is internal when it is invariant under all permutations preserving some partition. -/
def Supported (Y : Set ModFinite) : Prop :=
  ∃ k : ℕ, ∃ block : ℕ → Fin k, ∀ π : Equiv.Perm ℕ, (∀ x, block (π x) = block x) →
    ∀ s : Set ℕ, classOf s ∈ Y ↔ classOf (π ⁻¹' s) ∈ Y

/-- In Bruce's finite partition model the quotient is an infinite poset, each point has
a finite partition support, and comparability colours both ways on every infinite internal
family. The strict comparison gives two distinct comparable points. -/
theorem finitePartitionRamsey :
    Infinite ModFinite ∧ (∀ a : ModFinite, Supported {a}) ∧
    (∀ (π : Equiv.Perm ℕ) (s t : Set ℕ),
      classOf (π ⁻¹' s) ≤ classOf (π ⁻¹' t) ↔ classOf s ≤ classOf t) ∧
    ∀ Y : Set ModFinite, Supported Y → Y.Infinite →
      (∃ a ∈ Y, ∃ b ∈ Y, a < b) ∧
      (∃ a ∈ Y, ∃ b ∈ Y, ¬ a ≤ b ∧ ¬ b ≤ a) := by
  sorry

end SolvedProblems.PartitionRamsey
