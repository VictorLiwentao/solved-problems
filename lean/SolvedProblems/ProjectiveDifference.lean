module

public import SolvedProblems.ProjectiveSpan

@[expose] public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} {G : Subgroup (Equiv.Perm A)} {cl : Set A → Set A}

/-- Send a finite subset to the points in its generated flat that it omits. -/
noncomputable def flatDifference (geom : Geometry G cl) (S : Finset A) : Finset A :=
  open Classical in finiteFlat geom S \ S

/-- This specific map is supported and surjective but fails to be injective.
All closed finite flats map to the empty set. -/
theorem differenceSurjection [Infinite A] (geom : Geometry G cl) :
    (∃ E : Finset A, ∀ σ ∈ G, Fixes σ E → ∀ S : Finset A,
      flatDifference geom (S.map σ.toEmbedding) = (flatDifference geom S).map σ.toEmbedding) ∧
    Surjective (flatDifference geom) ∧ ¬ Injective (flatDifference geom) := by
  classical
  obtain ⟨E,supp⟩ := geom.support
  refine ⟨⟨E,?_⟩,?_,?_⟩
  · intro σ hm fix S
    apply Finset.coe_injective
    simp only [flatDifference,Finset.coe_sdiff,coe_finiteFlat,Finset.coe_map,Equiv.coe_toEmbedding]
    rw [supp σ hm fix,Set.image_sdiff σ.injective]
  · intro S
    obtain ⟨D,sub,flat⟩ := flat_spanned_by_difference geom S
    exact ⟨D \ S,by rw [flatDifference,flat,Finset.sdiff_sdiff_eq_self sub]⟩
  · intro hinj
    let C := finiteFlat geom ∅
    obtain ⟨a,fresh⟩ := C.finite_toSet.exists_notMem
    let D := finiteFlat geom {a}
    have empty (T : Finset A) : flatDifference geom (finiteFlat geom T) = ∅ := by
      have fixed : finiteFlat geom (finiteFlat geom T) = finiteFlat geom T := Finset.coe_injective ((coe_finiteFlat geom (finiteFlat geom T)).trans (finiteFlat_closed geom T))
      simp [flatDifference,fixed]
    have eq : C = D := hinj ((empty ∅).trans (empty {a}).symm)
    apply fresh
    change a ∈ C
    rw [eq]
    exact intoFlat geom {a} (Finset.mem_singleton_self a)

end ProjectiveSupports
