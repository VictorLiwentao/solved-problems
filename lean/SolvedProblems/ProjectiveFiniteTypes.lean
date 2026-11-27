module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.Finite.Sum

@[expose] public section

namespace ProjectiveTypes

open FirstOrder FirstOrder.Language Set

variable (L : Language) {ι κ M N : Type*} [L.Structure M] [L.Structure N]

/-- The full first-order type of a tuple over the empty set. -/
def tupleType (x : ι → M) : Set (L.Formula ι) := {φ | φ.Realize x}

/-- Types of the given arity actually realized in a structure. -/
def typesIn (M : Type*) [L.Structure M] (ι : Type*) : Set (Set (L.Formula ι)) :=
  Set.range (tupleType L : (ι → M) → Set (L.Formula ι))

private theorem distinguish (x : ι → M) (y : ι → N) (h : tupleType L x ≠ tupleType L y) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ¬φ.Realize y := by
  by_contra! no
  apply h
  ext φ
  change φ.Realize x ↔ φ.Realize y
  refine ⟨no φ, fun hy => ?_⟩
  by_contra hx
  exact (Formula.realize_not.mp (no φ.not (Formula.realize_not.mpr hx))) hy

/-- A single formula separates a tuple from any finite collection of other realized types. -/
private theorem separate (x : ι → M) (S : Set (Set (L.Formula ι))) (hs : S.Finite)
    (realized : S ⊆ typesIn L N ι) (avoids : tupleType L x ∉ S) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ∀ y : ι → N, tupleType L y ∈ S → ¬φ.Realize y := by
  induction S, hs using Set.Finite.induction_on with
  | empty => exact ⟨⊤, Formula.realize_top.mpr trivial, by simp⟩
  | @insert q S hq hs ih =>
    have nq : tupleType L x ≠ q := fun h => avoids (h ▸ Set.mem_insert q S)
    obtain ⟨y,hy⟩ := realized (Set.mem_insert q S)
    obtain ⟨φ,hφ,hφy⟩ := distinguish L x y (hy ▸ nq)
    obtain ⟨θ,hθ,hθy⟩ := ih ((Set.subset_insert q S).trans realized)
      (fun h => avoids (Set.mem_insert_of_mem q h))
    refine ⟨φ ⊓ θ, Formula.realize_inf.mpr ⟨hφ,hθ⟩, ?_⟩
    intro z hz h
    obtain ⟨hp,ht⟩ := Formula.realize_inf.mp h
    rcases Set.mem_insert_iff.mp hz with eq | hz
    · exact hφy ((show φ ∈ tupleType L y from (eq.trans hy.symm) ▸ hp))
    · exact hθy z hz ht

private theorem exists_transfer [Finite ι] (h : M ≅[L] N) (φ : L.Formula ι) :
    (∃ x : ι → M, φ.Realize x) ↔ (∃ y : ι → N, φ.Realize y) := by
  let ψ : L.Sentence := (φ.relabel (Sum.inr : ι → Empty ⊕ ι)).iExs ι
  have transfer := elementarilyEquivalent_iff.mp h ψ
  simpa only [ψ, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
    Sum.elim_comp_inr] using transfer

private theorem types_subset [Finite ι] (h : M ≅[L] N) (hN : (typesIn L N ι).Finite) :
    typesIn L M ι ⊆ typesIn L N ι := by
  rintro _ ⟨x,rfl⟩
  by_contra missing
  obtain ⟨φ,hx,hn⟩ := separate L x _ hN Set.Subset.rfl missing
  obtain ⟨y,hy⟩ := (exists_transfer L h φ).mp ⟨x,hx⟩
  exact hn y ⟨y,rfl⟩ hy

/-- Each finite-arity type is realized in both elementarily equivalent structures
when one of them realizes only finitely many types of that arity. -/
theorem realizedTypes_eq [Finite ι] (h : M ≅[L] N) (hM : (typesIn L M ι).Finite) :
    typesIn L M ι = typesIn L N ι := by
  have sub := types_subset L (M := N) (N := M) (ι := ι) (Eq.symm h) hM
  exact Set.Subset.antisymm (types_subset L h (hM.subset sub)) sub

/-- Tuples of a fixed type in the two models can be extended on the second
side to match arbitrarily many additional prescribed elements on the first.
The isolation formula is obtained from finitely many realized joint types. -/
theorem extendTuple [Finite κ] [Finite ι] (h : M ≅[L] N)
    (finite : (typesIn L M (ι ⊕ κ)).Finite) {x : ι → M} {y : ι → N}
    (same : tupleType L x = tupleType L y) (z : κ → M) :
    ∃ w : κ → N, tupleType L (Sum.elim x z) = tupleType L (Sum.elim y w) := by
  let p := tupleType L (Sum.elim x z)
  let S := typesIn L N (ι ⊕ κ) \ {p}
  have eq := realizedTypes_eq L h finite
  have hs : S.Finite := (eq ▸ finite : (typesIn L N (ι ⊕ κ)).Finite).subset Set.sdiff_subset
  have avoids : p ∉ S := fun h => h.2 rfl
  obtain ⟨φ,hp,other⟩ := separate L (Sum.elim x z) S hs Set.sdiff_subset avoids
  have hx : φ.iExs κ ∈ tupleType L x := Formula.realize_iExs.mpr ⟨z,hp⟩
  have hy : φ.iExs κ ∈ tupleType L y := same ▸ hx
  obtain ⟨w,hw⟩ := Formula.realize_iExs.mp hy
  refine ⟨w, ?_⟩
  by_contra diff
  exact other _ ⟨⟨_,rfl⟩, fun eq => diff eq.symm⟩ hw

end ProjectiveTypes
