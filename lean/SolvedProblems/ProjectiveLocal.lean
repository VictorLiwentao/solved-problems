module

public import SolvedProblems.ProjectivePregeometry
import SolvedProblems.ProjectiveCodeMatch

public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M]

private theorem closure_inside {ι : Type} [Finite ι] {D : Finset M} (closed : acl L (D : Set M) = D)
    {x : ι → M} (hx : ∀ i, x i ∈ D) : tupleClosure L x ⊆ (D : Set M) := by
  rw [← acl_range x,← closed]
  exact acl_mono fun _ ⟨i,h⟩ => h ▸ hx i

/-- A prescribed new element in a finite closed set can be matched inside the
same set. Algebraic images lie in the set by closedness. For generic images,
the two closures already occupied have the same finite size. -/
private theorem add_inside {ι : Type} [Finite ι] (fin : FiniteTypes L M) (min : Minimal L M)
    {D : Finset M} (closed : acl L (D : Set M) = D) {x y : ι → M} (m : tupleType L x = tupleType L y)
    (hx : ∀ i, x i ∈ D) (hy : ∀ i, y i ∈ D) {a : M} (ha : a ∈ D) :
    ∃ b ∈ D, tupleType L (point x a) = tupleType L (point y b) := by
  obtain ⟨f,hf⟩ := extendTuple L (Eq.refl _) (fin (ι ⊕ Unit)) m (fun _ : Unit => a)
  have eq : tupleType L (point x a) = tupleType L (point y (f ())) := by
    have unique : (fun _ : Unit => f ()) = f := funext fun u => by cases u; rfl
    simpa [point,unique] using hf
  by_cases alg : a ∈ tupleClosure L x
  · exact ⟨f (),closure_inside closed hy ((algebraic_match fin eq).mp alg),eq⟩
  have proper : tupleClosure L x ⊂ (D : Set M) := Set.ssubset_iff_subset_ne.mpr
    ⟨closure_inside closed hx,fun h => alg (h ▸ ha)⟩
  have less := (finite_tupleClosure fin x).encard_lt_encard proper
  rw [closure_card fin m] at less
  have gap : ∃ b ∈ D, b ∉ tupleClosure L y := by
    by_contra! nogap
    exact (not_le_of_gt less) (Set.encard_mono (show (D : Set M) ⊆ tupleClosure L y from nogap))
  obtain ⟨b,hb,hAlg⟩ := gap
  exact ⟨b,hb,eq.trans (generic_type min (fun h => alg ((algebraic_match fin eq).mpr h)) hAlg)⟩

private theorem extend_inside (fin : FiniteTypes L M) (min : Minimal L M)
    {D : Finset M} (closed : acl L (D : Set M) = D) (n : ℕ) {ι : Type} [Finite ι]
    {x y : ι → M} (m : tupleType L x = tupleType L y)
    (hx : ∀ i, x i ∈ D) (hy : ∀ i, y i ∈ D) (a : Fin n → M) (ha : ∀ i, a i ∈ D) :
    ∃ b : Fin n → M, (∀ i, b i ∈ D) ∧ tupleType L (Sum.elim x a) = tupleType L (Sum.elim y b) := by
  induction n generalizing ι with
  | zero =>
    let pick : ι ⊕ Fin 0 → ι := Sum.elim id Fin.elim0
    have cut (p : ι → M) (v : Fin 0 → M) : p ∘ pick = Sum.elim p v := by
      funext j; rcases j with i|i; rfl; exact Fin.elim0 i
    have mm := match_subtuple m pick
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,?_⟩
    rwa [cut x a,cut y Fin.elim0] at mm
  | succ n ih =>
    obtain ⟨v,hv,one⟩ := add_inside fin min closed m hx hy (ha 0)
    have xIn (i : ι ⊕ Unit) : point x (a 0) i ∈ D := by cases i <;> first | exact hx _ | exact ha 0
    have yIn (i : ι ⊕ Unit) : point y v i ∈ D := by cases i <;> first | exact hy _ | exact hv
    obtain ⟨w,hw,all⟩ := ih one xIn yIn (fun j => a j.succ) (fun j => ha j.succ)
    let pick : ι ⊕ Fin (n+1) → (ι ⊕ Unit) ⊕ Fin n :=
      Sum.elim (fun i => Sum.inl (Sum.inl i)) (Fin.cases (Sum.inl (Sum.inr ())) Sum.inr)
    have cut (p : ι → M) (u : Fin (n+1) → M) :
        Sum.elim (point p (u 0)) (fun j => u j.succ) ∘ pick = Sum.elim p u := by
      funext i
      rcases i with i|i
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    let b : Fin (n+1) → M := Fin.cons v w
    refine ⟨b,fun i => Fin.cases hv hw i,?_⟩
    have mm := match_subtuple all pick
    rw [cut x a] at mm
    exact (cut y b) ▸ mm

/-- Every elementary match between two tuples in a finite closed set extends to
a permutation of that set that matches the full first-order types of all tuples. -/
theorem finite_extension {ι : Type} [Finite ι] (fin : FiniteTypes L M) (min : Minimal L M)
    (D : Finset M) (closed : acl L (D : Set M) = D) (x y : ι → D)
    (m : tupleType L (fun i => (x i).val) = tupleType L (fun i => (y i).val)) :
    ∃ e : D ≃ D, (∀ i, e (x i) = y i) ∧ ∀ (n : ℕ) (w : Fin n → D),
      tupleType L (fun j => (w j).val) = tupleType L (fun j => (e (w j)).val) := by
  classical
  let z := enumerate D
  obtain ⟨v,hv,joint⟩ := extend_inside fin min closed D.card m (fun i => (x i).property)
    (fun i => (y i).property) z (fun i => (D.equivFin.symm i).property)
  let map (a : D) : D := ⟨v (D.equivFin a),hv _⟩
  have zv : tupleType L z = tupleType L v := match_subtuple joint Sum.inr
  have equal {α : Type} {s t : α → M} (vs : tupleType L s = tupleType L t) (i j : α) :
      s i = s j ↔ t i = t j := by
    have h := Set.ext_iff.mp vs ((Term.var i).equal (Term.var j))
    change ((Term.var i).equal (Term.var j)).Realize s ↔ ((Term.var i).equal (Term.var j)).Realize t at h
    exact Formula.realize_equal.symm.trans (h.trans Formula.realize_equal)
  have inj : Injective map := by
    intro a b he
    have zEq := (equal zv (D.equivFin a) (D.equivFin b)).mpr (congrArg Subtype.val he)
    exact Subtype.ext (by simpa [z,enumerate] using zEq)
  let e := _root_.Equiv.ofBijective map ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨e,?_,?_⟩
  · intro i
    have h := (equal joint (Sum.inr (D.equivFin (x i))) (Sum.inl i)).mp (by simp [z,enumerate])
    exact Subtype.ext h
  · intro n w
    have h := match_subtuple zv (fun j => D.equivFin (w j))
    have cut : z ∘ (fun j => D.equivFin (w j)) = (fun j => (w j).val) := by
      funext j; simp [z,enumerate]
    rwa [cut] at h

end ProjectiveAlgebraic
