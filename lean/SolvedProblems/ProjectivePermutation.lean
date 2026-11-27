module

public import SolvedProblems.ProjectiveSufficiency
public import SolvedProblems.ProjectiveWitness

public section

namespace ProjectiveSupports

/-- In the finite point-support permutation interpretation, projective type,
dual Dedekind infinity of the internal powerset, and of some or every positive
finite power are equivalent. The two implications construct a supported
pregeometry from the map and a supported map from the pregeometry. -/
theorem projectivePowers {A : Type*} (G : Subgroup (Equiv.Perm A)) (am : Amorphous G) :
    ((∃ cl : Set A → Set A, Geometry G cl) ↔ DuallyInfinitePower G 1) ∧
    ((∃ cl : Set A → Set A, Geometry G cl) ↔ ∃ k > 0, DuallyInfinitePower G k) ∧
    ((∃ cl : Set A → Set A, Geometry G cl) ↔ ∀ k > 0, DuallyInfinitePower G k) := by
  have any {k : ℕ} (h : DuallyInfinitePower G k) : ∃ cl : Set A → Set A, Geometry G cl := by
    obtain ⟨F,supp,surj,collision⟩ := h
    exact supportedNecessity G am F supp surj collision
  have all (h : ∃ cl : Set A → Set A, Geometry G cl) (k : ℕ) (pos : 0 < k) : DuallyInfinitePower G k := by
    obtain ⟨_,geom⟩ := h
    exact allPositivePowers am geom k pos
  exact ⟨⟨fun h => all h 1 Nat.zero_lt_one,any⟩,
    ⟨fun h => ⟨1,Nat.zero_lt_one,all h 1 Nat.zero_lt_one⟩,fun ⟨_,_,h⟩ => any h⟩,
    ⟨all,fun h => any (h 1 Nat.zero_lt_one)⟩⟩

end ProjectiveSupports
