module

public import SolvedProblems.RadoMaterial
public import Mathlib.SetTheory.ZFC.VonNeumann

@[expose] public section

namespace RadoSelection

/-- Mathlib's material sets instantiate the rank, separation, power-set and
transitive-bound interface. The abstract equivalence already checks without choice. -/
noncomputable def vonNeumannUniverse : Material ZFSet.{u} Ordinal.{u} where
  rank := ZFSet.rank
  mem z x := z ∈ x
  lower := ZFSet.rank_lt_of_mem
  ext := ZFSet.ext
  empty := ∅
  empty_mem := ZFSet.notMem_empty
  add := insert
  add_mem := fun _ _ _ => ZFSet.mem_insert_iff
  join := (· ∪ ·)
  join_mem := fun _ _ _ => ZFSet.mem_union
  sep := fun s p => ZFSet.sep p s
  sep_mem := fun _ _ _ => ZFSet.mem_sep
  power := ZFSet.powerset
  power_mem := fun _ _ => ZFSet.mem_powerset
  transitive_bound b := ⟨ZFSet.vonNeumann b.rank,
    fun _ hx => ZFSet.subset_vonNeumann_self b hx,
    fun _ hx _ hz => ZFSet.isTransitive_vonNeumann _ _ hx hz⟩

/-- The two original principles specialized to carriers realized by Mathlib
pure sets. Families, their local choices, and the algebra are still arbitrary. -/
theorem pureSet_equivalence :
    vonNeumannUniverse.{u}.SelectionPrinciple ↔ vonNeumannUniverse.{u}.BooleanPrinciple := by
  classical
  exact vonNeumannUniverse.equivalence

end RadoSelection
