module

public import SolvedProblems.ProjectiveFlatSets
public import SolvedProblems.ProjectiveFlatActions

public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} {G : Subgroup (Equiv.Perm A)} {cl : Set A → Set A}

/-- Any generic point has a finite spanning configuration outside its own
singleton closure, by transitivity over the finite algebraic core. -/
theorem spans_each_generic (geom : Geometry G cl) {b : A} (fresh : b ∉ cl ∅) : ∃ X, SpansOff cl b X := by
  classical
  obtain ⟨z,X,zo,hX⟩ := exists_spanning_set geom
  let C := finiteFlat geom ∅
  let T := insert b (insert z X)
  let D := finiteFlat geom T
  have core : (C : Set A) = cl ∅ := by simp [C]
  have cd : C ⊆ D := by
    intro x hx
    apply (coe_finiteFlat geom T).superset
    exact geom.monotone _ _ (Set.empty_subset _) (core.subset hx)
  let a : D := ⟨z,intoFlat geom T (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
  let t : D := ⟨b,intoFlat geom T (Finset.mem_insert_self _ _)⟩
  have xd : X ⊆ D := fun _ h => intoFlat geom T (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  obtain ⟨p,eq,_,symm,_⟩ := geom.locally_homogeneous C D cd (finiteFlat_closed _ _) (finiteFlat_closed _ _)
    a t (fun h => zo (core.subset h)) (fun h => fresh (core.subset h))
  have tr := move_spanning_set xd symm (z := a) hX
  exact ⟨_,eq ▸ tr⟩

/-- A given point has a finite spanning set disjoint from any prescribed finite
set. All other members of the initial configuration lie in the same orbit of
a finite-flat stabilizer, so a sufficiently large finite flat allows a
translate avoiding every forbidden point. -/
theorem spans_point_away [Infinite A] (geom : Geometry G cl) (b : A) (S : Finset A) :
    ∃ W : Finset A, Disjoint W S ∧ b ∈ cl (W : Set A) := by
  classical
  by_cases root : b ∈ cl ∅
  · exact ⟨∅,Finset.disjoint_empty_left _,by simpa using root⟩
  obtain ⟨X,hX⟩ := spans_each_generic geom root
  let C := finiteFlat geom {b}
  have ce : (C : Set A) = cl {b} := by simp [C]
  obtain ⟨T,away,num⟩ := C.finite_toSet.infinite_compl.exists_subset_card_eq (X.card*S.card+1)
  let B := C ∪ X ∪ T
  let D := finiteFlat geom B
  have cd : C ⊆ D := fun _ h => intoFlat geom B (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have xd : X ⊆ D := fun _ h => intoFlat geom B (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have td : T ⊆ D := fun _ h => intoFlat geom B (Finset.mem_union_right _ h)
  let embed (t : T) : Outside C D := ⟨⟨t.val,td t.property⟩,away t.property⟩
  have bound : T.card ≤ Nat.card (Outside C D) := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective embed
      (fun a b h => Subtype.ext (congrArg (fun u : Outside C D => u.val.val) h))
  rw [num] at bound
  have enough : X.card*S.card < Nat.card (Outside C D) := bound
  obtain ⟨p,fix,pres,miss⟩ := displace geom C D cd (finiteFlat_closed _ _) (finiteFlat_closed _ _)
    X S (fun a h hc => hX.2 a h (ce.subset hc)) enough
  have bc : b ∈ C := intoFlat geom {b} (Finset.mem_singleton_self _)
  let a : D := ⟨b,cd bc⟩
  have spanning := moves_closure xd pres a |>.mp hX.1
  rw [fix a bc] at spanning
  refine ⟨moveSet p X,Finset.disjoint_left.mpr ?_,spanning⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact miss x ((mem_inside D X x).mp hx)

open Classical in
/-- Each finite set lies in a finite closed flat spanned by the complement of
that set inside the flat. -/
theorem flat_spanned_by_difference [Infinite A] (geom : Geometry G cl) (S : Finset A) :
    ∃ D : Finset A, S ⊆ D ∧ finiteFlat geom (D \ S) = D := by
  classical
  choose w apart span using fun a => spans_point_away geom a S
  let W := S.biUnion w
  let D := finiteFlat geom W
  have sub : S ⊆ D := by
    intro a ha
    apply (coe_finiteFlat geom W).superset
    apply geom.monotone _ _ _ (span a)
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨a,ha,hx⟩
  have wd : W ⊆ D \ S := by
    intro x hx
    obtain ⟨u,hu,xm⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_sdiff.mpr ⟨intoFlat geom W hx,Finset.disjoint_left.mp (apart u) xm⟩
  refine ⟨D,sub,Finset.coe_injective ?_⟩
  rw [coe_finiteFlat]
  exact Set.Subset.antisymm ((geom.monotone _ _ (by exact Finset.sdiff_subset : (↑(D \ S) : Set A) ⊆ D)).trans (finiteFlat_closed geom W).subset)
    ((coe_finiteFlat geom W).subset.trans (geom.monotone _ _ wd))

end ProjectiveSupports
