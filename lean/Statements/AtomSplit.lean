module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace AtomSplit

/-- The full stabilizer of a finite partition of the countably many atoms. -/
def stabilizer {k : ℕ} (block : ℕ → Fin k) : Subgroup (Equiv.Perm ℕ) where
  carrier := {g | ∀ a, block (g a) = block a}
  one_mem' := fun _ => rfl
  mul_mem' hg hh a := (hg _).trans (hh a)
  inv_mem' {g} hg a := by simpa using (hg (g.symm a)).symm

/-- Preserving each of finitely many subsets preserves every cell in their common refinement. -/
def Preserves (cuts : List (Set ℕ)) (g : Equiv.Perm ℕ) : Prop :=
  ∀ D ∈ cuts, ∀ a, g a ∈ D ↔ a ∈ D

/-- Once a set is supported by the partition, its stabilizer acts on the elements.
Hereditary symmetry gives each element its own finite partition support. -/
def LocallySupported {k : ℕ} {block : ℕ → Fin k} {X : Type u}
    (act : stabilizer block →* Equiv.Perm X) : Prop :=
  ∀ x : X, ∃ cuts : List (Set ℕ), ∀ g : stabilizer block,
    Preserves cuts g.val → act g x = x

/-- A subset of the carrier is internal if a finite refinement supports it setwise. -/
def Supported {k : ℕ} {block : ℕ → Fin k} {X : Type u}
    (act : stabilizer block →* Equiv.Perm X) (Y : Set X) : Prop :=
  ∃ cuts : List (Set ℕ), ∀ g : stabilizer block,
    Preserves cuts g.val → ∀ x, act g x ∈ Y ↔ x ∈ Y

/-- Every infinite set of arbitrary rank in Bruce's finite partition model splits
into two infinite supported subsets. The carrier is the external set of its elements. -/
theorem everyInfiniteSetSplits {k : ℕ} (block : ℕ → Fin k) {X : Type u} [Infinite X]
    (act : stabilizer block →* Equiv.Perm X) (hs : LocallySupported act) :
    ∃ Y : Set X, Supported act Y ∧ Supported act Yᶜ ∧ Y.Infinite ∧ Yᶜ.Infinite
 := by sorry

end AtomSplit
