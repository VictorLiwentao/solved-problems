module

public import SolvedProblems.ProjectiveSupports
public import SolvedProblems.ProjectiveTypesCard
import SolvedProblems.ProjectiveCodeMatch

@[expose] public section

namespace ProjectiveSupports

open FirstOrder FirstOrder.Language ProjectiveAlgebraic ProjectiveTransfer ProjectiveTypes Set Function

variable {A : Type*} (G : Subgroup (_root_.Equiv.Perm A)) {L : Language} [L.Structure A]

/-- Every permutation fixing these finitely many points induces a genuine
first-order automorphism of the displayed structure. -/
def SupportedStructure (L : Language) [L.Structure A] (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∃ e : A ≃[L] A, e.toEquiv = σ

/-- Amorphousness in the support interpretation implies both model-theoretic
properties used in the argument, without postulating a well-order of the
internal atom set or its internal powerset. -/
theorem structure_properties (am : Amorphous G) (E : Finset A) (h : SupportedStructure G L E) :
    FiniteTypes L A ∧ Minimal L A := by
  classical
  refine ⟨?_,?_⟩
  · intro ι _
    apply finite_image G am _ E
    intro σ hg fix v
    obtain ⟨e,rfl⟩ := h _ hg fix
    ext φ
    exact StrongHomClass.realize_formula e φ
  · intro ι _ v φ
    let := Fintype.ofFinite ι
    apply am.2
    refine ⟨E ∪ Finset.univ.image v,?_⟩
    intro σ hg fix a
    obtain ⟨e,rfl⟩ := h _ hg (fun t ht => fix t (Finset.mem_union_left _ ht))
    have cut : e ∘ point v a = point v (e a) := by
      funext j
      rcases j with j|j
      · exact fix _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      · rfl
    change φ.Realize (point v (e a)) ↔ φ.Realize (point v a)
    rw [← cut]
    exact StrongHomClass.realize_formula e φ

/-- An internal self-map on codes commutes with permutations fixing its support. -/
def SupportedCodeMap {k : ℕ} (f : Codes A k → Codes A k) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ x, f (decode σ x) = decode σ (f x)

private theorem decode_injective {k : ℕ} (σ : _root_.Equiv.Perm A) : Injective (decode (k := k) σ) := by
  have inv (x : Codes A k) : decode σ.symm (decode σ x) = x := by
    rw [decode_comp]
    funext j
    simp [decode,Function.comp_def]
  exact Function.LeftInverse.injective inv

/-- The graph language recording every finite mask of the map has the very
same finite support as the map. -/
theorem graph_supported {k : ℕ} (f : Codes A k → Codes A k) (E : Finset A) (h : SupportedCodeMap G f E) :
    letI := graphStructure f
    SupportedStructure G (graphLanguage k) E := by
  let := graphStructure f
  intro σ hg fix
  refine ⟨{toEquiv := σ
           map_fun' := fun r => nomatch r
           map_rel' := ?_},rfl⟩
  intro n r v
  change f (decode (σ ∘ v) r.1) = decode (σ ∘ v) r.2 ↔ f (decode v r.1) = decode v r.2
  rw [← decode_comp v σ,← decode_comp v σ,h _ hg fix]
  exact (decode_injective σ).eq_iff

private theorem acl_map (fin : FiniteTypes L A) (e : A ≃[L] A) {S : Set A} {a : A} (h : a ∈ acl L S) :
    e a ∈ acl L (e '' S) := by
  obtain ⟨n,v,inc,mem⟩ := h
  have t : tupleType L (point (e ∘ v) (e a)) = tupleType L (point v a) := by
    have cut : e ∘ point v a = point (e ∘ v) (e a) := by funext j; cases j <;> rfl
    rw [← cut]
    ext φ
    exact StrongHomClass.realize_formula e φ
  refine ⟨n,e ∘ v,?_,(algebraic_match fin t).mpr mem⟩
  rintro _ ⟨i,rfl⟩
  exact ⟨v i,inc (Set.mem_range_self i),rfl⟩

/-- Algebraic closure commutes with every automorphism, also on infinite and
externally given parameter sets. -/
theorem acl_image (fin : FiniteTypes L A) (e : A ≃[L] A) (S : Set A) :
    acl L (e '' S) = e '' acl L S := by
  ext y
  refine ⟨?_,fun ⟨x,hx,eq⟩ => eq ▸ acl_map fin e hx⟩
  intro hy
  have back := acl_map fin e.symm hy
  have eq : e.symm '' (e '' S) = S := by
    ext x
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      simpa using hz
    · intro h
      exact ⟨e x,⟨x,h,rfl⟩,e.symm_apply_apply x⟩
  exact ⟨e.symm y,eq ▸ back,e.apply_symm_apply y⟩

end ProjectiveSupports
