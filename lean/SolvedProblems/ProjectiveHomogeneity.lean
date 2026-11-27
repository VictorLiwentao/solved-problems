module

public import SolvedProblems.ProjectiveLocal
import SolvedProblems.ProjectiveCodeMatch

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M]

/-- A permutation of a closed set preserves the inherited pregeometry on every
subset, using algebraic closure in the ambient structure on both sides. -/
def PreservesClosure (L : Language) {M : Type*} [L.Structure M] (D : Finset M) (e : D ≃ D) : Prop :=
  ∀ (V : Set D) (a : D), a.val ∈ acl L (Subtype.val '' V) ↔
    (e a).val ∈ acl L ((fun d : D => (e d).val) '' V)

/-- View an element of a finite subset in a larger finite subset. -/
def includePoint {T U : Finset M} (h : T ⊆ U) (x : T) : U := ⟨x.val,h x.property⟩

private theorem image_closure {A : Type*} (f : A → M) (S : Set A) (a : M) :
    a ∈ acl L (f '' S) ↔ ∃ (n : ℕ) (w : Fin n → A), (∀ i, w i ∈ S) ∧ a ∈ tupleClosure L (f ∘ w) := by
  classical
  constructor
  · rintro ⟨n,x,inc,ha⟩
    choose w hw eq using fun j => inc (Set.mem_range_self j)
    exact ⟨n,w,hw,(show f ∘ w = x from funext eq) ▸ ha⟩
  · rintro ⟨n,w,inside,ha⟩
    exact ⟨n,f ∘ w,fun _ ⟨j,eq⟩ => ⟨w j,inside j,eq⟩,ha⟩

private theorem preserves_of_elementary (fin : FiniteTypes L M) {D : Finset M} (e : D ≃ D)
    (elem : ∀ (n : ℕ) (u : Fin n → D), tupleType L (fun j => (u j).val) =
      tupleType L (fun j => (e (u j)).val)) : PreservesClosure L D e := by
  classical
  intro V d
  simp only [image_closure]
  have each (n : ℕ) (w : Fin n → D) : d.val ∈ tupleClosure L (Subtype.val ∘ w) ↔
      (e d).val ∈ tupleClosure L ((fun z : D => (e z).val) ∘ w) := by
    let I := Fin n ⊕ Unit
    let z := point w d
    let idx := Fintype.equivFin I
    have m := elem _ (z ∘ idx.symm)
    have pull := match_subtuple m idx
    have cut (f : D → M) : (fun j => f ((z ∘ idx.symm) j)) ∘ idx = point (f ∘ w) (f d) := by
      funext j
      rcases j with j|j <;> simp [Function.comp_def,z,point]
    change tupleType L ((fun j => Subtype.val ((z ∘ idx.symm) j)) ∘ idx) =
      tupleType L ((fun j => (fun t : D => (e t).val) ((z ∘ idx.symm) j)) ∘ idx) at pull
    rw [cut (fun t => t.val),cut (fun t => (e t).val)] at pull
    exact algebraic_match fin pull
  exact exists_congr fun n => exists_congr fun w => and_congr_right fun _ => each n w

/-- The local homogeneity and extension clauses. Given finite closed `S ⊆ D`,
any two points of `D \\ S` are related by a permutation fixing `S` pointwise
and preserving closure on every subset. That same permutation extends inside
every larger finite closed set. -/
theorem localHomogeneity (fin : FiniteTypes L M) (min : Minimal L M)
    (S D : Finset M) (sub : S ⊆ D) (sclosed : acl L (S : Set M) = S) (dclosed : acl L (D : Set M) = D)
    (a b : D) (ha : a.val ∉ S) (hb : b.val ∉ S) :
    ∃ e : D ≃ D, e a = b ∧ (∀ d : D, d.val ∈ S → e d = d) ∧ PreservesClosure L D e ∧
      ∀ (U : Finset M) (inc : D ⊆ U), acl L (U : Set M) = U →
        ∃ g : U ≃ U, (∀ d : D, g (includePoint inc d) = includePoint inc (e d)) ∧ PreservesClosure L U g := by
  classical
  let s (i : Fin S.card) := includePoint sub (S.equivFin.symm i)
  let x := point s a
  let y := point s b
  have eq : tupleClosure L (enumerate S) = (S : Set M) := by
    rw [← acl_range,range_enumerate,sclosed]
  have m := generic_type min (x := enumerate S) (a := a.val) (b := b.val) (fun h => ha (eq.subset h)) (fun h => hb (eq.subset h))
  have cut (v : D) : (fun i => (point s v i).val) = point (enumerate S) v.val := by
    funext i; cases i <;> rfl
  have initial : tupleType L (fun i => (x i).val) = tupleType L (fun i => (y i).val) := by
    simpa only [x,y,cut] using m
  obtain ⟨e,fix,elem⟩ := finite_extension fin min D dclosed x y initial
  refine ⟨e,fix (.inr ()),?_,preserves_of_elementary fin e elem,?_⟩
  · intro d hd
    let u : S := ⟨d.val,hd⟩
    have h := fix (.inl (S.equivFin u))
    have id' : s (S.equivFin u) = d := by simp [s,u,includePoint]
    change e (s (S.equivFin u)) = s (S.equivFin u) at h
    rwa [id'] at h
  · intro U inc closed
    let u := D.equivFin.symm
    obtain ⟨g,extension,elemU⟩ := finite_extension fin min U closed
      (fun i => includePoint inc (u i)) (fun i => includePoint inc (e (u i))) (elem _ u)
    refine ⟨g,?_,preserves_of_elementary fin g elemU⟩
    intro d
    simpa [u] using extension (D.equivFin d)

end ProjectiveAlgebraic
