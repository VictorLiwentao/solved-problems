module

public import SolvedProblems.ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- The closure operator on all parameter sets commutes with every permutation
fixing one support. It therefore restricts to an internal closure operator. -/
def SupportedClosure (cl : Set A → Set A) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ S, cl (σ '' S) = σ '' cl S

/-- Preservation of the closure of arbitrary subsets of a finite closed set. -/
def Preserves (cl : Set A → Set A) (D : Finset A) (p : D ≃ D) : Prop :=
  ∀ (V : Set D) (a : D), a.val ∈ cl (Subtype.val '' V) ↔
    (p a).val ∈ cl ((fun d : D => (p d).val) '' V)

/-- The pregeometry, nondegeneracy, and the two local homogeneity conditions
in Truss's projective-type definition. Finitary closure is specified on all
subsets, and its finite support makes its restriction an internal witness. -/
structure Geometry (cl : Set A → Set A) : Prop where
  support : ∃ E, SupportedClosure G cl E
  extensive : ∀ S, S ⊆ cl S
  monotone : ∀ S T, S ⊆ T → cl S ⊆ cl T
  idempotent : ∀ S, cl (cl S) = cl S
  finite_character : ∀ S a, a ∈ cl S ↔ ∃ D : Finset A, (D : Set A) ⊆ S ∧ a ∈ cl (D : Set A)
  locally_finite : ∀ S : Set A, S.Finite → (cl S).Finite
  exchange : ∀ S a b, b ∈ cl (insert a S) → b ∉ cl S → a ∈ cl (insert b S)
  nondegenerate : ∃ D : Finset A, D.Nonempty ∧ cl (D : Set A) ≠ ⋃ x ∈ D, cl {x}
  locally_homogeneous : ∀ (S D : Finset A), S ⊆ D → cl (S : Set A) = S → cl (D : Set A) = D →
    ∀ (a b : D), a.val ∉ S → b.val ∉ S →
      ∃ p : D ≃ D, p a = b ∧ (∀ d : D, d.val ∈ S → p d = d) ∧ Preserves cl D p ∧
        ∀ (U : Finset A) (inc : D ⊆ U), cl (U : Set A) = U →
          ∃ q : U ≃ U, (∀ d : D, q ⟨d.val,inc d.property⟩ = ⟨(p d).val,inc (p d).property⟩) ∧ Preserves cl U q

/-- The closure of an internal set is internal. A support is the union of a
support of the operator with a support of the input set. -/
theorem closed_supported {cl : Set A → Set A} {E : Finset A} (supp : SupportedClosure G cl E)
    {S : Set A} (hs : Supported G S) : Supported G (cl S) := by
  classical
  obtain ⟨D,sd⟩ := hs
  refine ⟨E ∪ D,?_⟩
  intro σ hg fix a
  have move := sd σ hg (fun t h => fix _ (Finset.mem_union_right _ h))
  have eq : σ '' S = S := by
    ext z
    refine ⟨fun ⟨w,hw,h⟩ => h ▸ (move w).mpr hw,fun hz => ?_⟩
    exact ⟨σ.symm z,(move _).mp (by simpa using hz),σ.apply_symm_apply z⟩
  have ce := supp σ hg (fun t ht => fix _ (Finset.mem_union_left _ ht)) S
  rw [eq] at ce
  conv_lhs => rw [ce]
  exact σ.injective.mem_set_image

end ProjectiveSupports
