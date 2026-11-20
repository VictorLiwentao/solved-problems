module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

namespace ClosureSupport

/-- Membership in finitely many subsets gives the cells of a finite partition of the atoms. -/
abbrev Support := List (Set ℕ)

def Fixes (P : Support) (g : Equiv.Perm ℕ) : Prop :=
  ∀ S ∈ P, ∀ x, g x ∈ S ↔ x ∈ S

def stabilizer (P : Support) : Subgroup (Equiv.Perm ℕ) where
  carrier := {g | Fixes P g}
  one_mem' := fun _ _ _ => Iff.rfl
  mul_mem' ha hb := fun _ h x => (ha _ h _).trans (hb _ h x)
  inv_mem' {g} hg := fun S hs x => by simpa using (hg S hs (g.symm x)).symm

end ClosureSupport
