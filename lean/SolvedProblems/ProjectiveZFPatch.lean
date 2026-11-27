module

public import SolvedProblems.ProjectiveZFFunctions

@[expose] public section

namespace ProjectiveZF

variable {V : Type*} [Membership V V] (M : Core V)

/-- A coordinate of an internal graph is changed to the given value. -/
def Patch (i y s t : V) : Prop := ∀ j z, Edge t j z ↔ (j = i ∧ z = y) ∨ (j ≠ i ∧ Edge s j z)

theorem defPatch {ι : Type*} {i y s t : (ι → V) → V} (hi : Term i) (hy : Term y) (hs : Term s) (ht : Term t) :
    Definable (fun u => Patch (i u) (y u) (s u) (t u)) := by unfold Patch; zf_map_formula

include M

/-- Coordinate replacement exists internally. -/
theorem patchExists {X I s i y : V} (hs : IsMap I X s) (hi : i ∈ I) (hy : y ∈ X) :
    ∃ t, IsMap I X t ∧ Patch i y s t := by
  let R (j z : V) := (j = i ∧ z = y) ∨ (j ≠ i ∧ Edge s j z)
  have d : Binary R := by unfold Binary R; zf_map_formula
  have typed {j z : V} (h : R j z) : j ∈ I ∧ z ∈ X := by
    rcases h with ⟨rfl,rfl⟩|⟨_,edge⟩
    · exact ⟨hi,hy⟩
    · exact edge_typed M hs edge
  have total (j) (hj : j ∈ I) : ∃ z, z ∈ X ∧ R j z := by
    by_cases eq : j = i
    · exact ⟨y,hy,Or.inl ⟨eq,rfl⟩⟩
    · obtain ⟨z,hz⟩ := hs.2.1 _ hj
      exact ⟨z,(edge_typed M hs hz).2,Or.inr ⟨eq,hz⟩⟩
  have unique (j) (_ : j ∈ I) (a) (_ : a ∈ X) (b) (_ : b ∈ X) (x : R j a) (y : R j b) : a = b := by
    rcases x with ⟨xi,xa⟩|⟨xi,xa⟩ <;> rcases y with ⟨yi,yb⟩|⟨yi,yb⟩
    · exact xa.trans yb.symm
    · exact (yi xi).elim
    · exact (xi yi).elim
    · exact hs.2.2 _ _ _ xa yb
  obtain ⟨t,ht,rule⟩ := mapFrom M I X R d total unique
  exact ⟨t,ht,fun j z => (rule j z).trans ⟨fun h => h.2.2,fun h => ⟨(typed h).1,(typed h).2,h⟩⟩⟩

theorem patchUnique {X I s t u i y : V} (ht : IsMap I X t) (hu : IsMap I X u) (p : Patch i y s t) (q : Patch i y s u) :
    t = u := graph_ext M ht hu fun j _ z => (p j z).trans (q j z).symm

omit M in
theorem patchBack {I X s t i a b : V} (hs : IsMap I X s) (old : Edge s i b) (p : Patch i a s t) : Patch i b t s := by
  intro j z
  by_cases eq : j = i
  · subst j
    simp
    exact ⟨fun h => hs.2.2 _ _ _ h old,fun h => h ▸ old⟩
  · simpa [eq] using (p j z).symm

omit M in
theorem patchAbsorb {s t u i a b : V} (p : Patch i a s t) (q : Patch i b s u) : Patch i b t u := by
  intro j z
  by_cases eq : j = i
  · simpa [eq] using q j z
  · simpa [eq] using ((q j z).trans (by simpa [eq] using (p j z).symm))

/-- A constant graph is an internal element of the function space. -/
theorem constantGraph {X I a : V} (ha : a ∈ X) : ∃ s, IsMap I X s ∧ ∀ j ∈ I, Edge s j a := by
  let R (_ z : V) := z = a
  obtain ⟨s,hs,edge⟩ := mapFrom M I X R (by unfold Binary R; zf_map_formula)
    (fun j _ => ⟨a,ha,rfl⟩) (fun _ _ _ _ _ _ h k => h.trans k.symm)
  exact ⟨s,hs,fun j hj => (edge j a).mpr ⟨hj,ha,rfl⟩⟩

end ProjectiveZF
