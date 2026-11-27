module

public import SolvedProblems.ChoiceOmegaOneModel
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Cardinal Ordinal Order

private theorem countable_predecessors (i : Row) : Countable (Iio i) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt i (show (#Row).ord = typeLT Row by simp [Row])
  simpa [Row] using h

/-- The well-ordered Erdős-Dushnik-Miller partition theorem on the first
uncountable ordinal. An uncountable set with countable blue neighborhoods
yields an ω₁-long red clique by recursion. In the other case a nested
sequence of uncountable blue neighborhoods yields a countable blue clique. -/
theorem edm_on_rows (G : SimpleGraph Row) :
    (∃ e : ℕ ↪ Row, ∀ i j, i ≠ j → ¬ G.Adj (e i) (e j)) ∨
    (∃ e : Row ↪ Row, ∀ i j, i ≠ j → G.Adj (e i) (e j)) := by
  classical
  let blue (a b : Row) := a ≠ b ∧ ¬ G.Adj a b
  by_cases thin : ∃ Y : Set Row, ¬Y.Countable ∧ ∀ a ∈ Y, {b ∈ Y | blue a b}.Countable
  · obtain ⟨Y,big,allowed⟩ := thin
    have fresh (i : Row) (prev : ∀ j : Row, j < i → Y) :
        ∃ z : Y, ∀ j (h : j < i), (prev j h).val ≠ z.val ∧ G.Adj (prev j h).val z.val := by
      let _ := countable_predecessors i
      let bad (j : Iio i) : Set Row := {b ∈ Y | blue (prev j j.property).val b} ∪ {(prev j j.property).val}
      have count (j : Iio i) : (bad j).Countable :=
        (allowed _ (prev j j.property).property).union (countable_singleton _)
      have outside : ∃ z ∈ Y, z ∉ ⋃ j,bad j := by
        by_contra! all
        exact big ((Set.countable_iUnion count).mono all)
      obtain ⟨z,hz,good⟩ := outside
      refine ⟨⟨z,hz⟩,fun j hj => ?_⟩
      have no : z ∉ bad ⟨j,hj⟩ := fun h => good (mem_iUnion.2 ⟨⟨j,hj⟩,h⟩)
      have ne : (prev j hj).val ≠ z := fun e => no (Or.inr e.symm)
      exact ⟨ne,by by_contra miss; exact no (Or.inl ⟨hz,ne,miss⟩)⟩
    choose step ok using fresh
    let e : Row → Y := wellFounded_lt.fix step
    have forward {i j : Row} (ij : i<j) : (e i).val ≠ (e j).val ∧ G.Adj (e i).val (e j).val := by
      have recurrence : e j = step j (fun k _ => e k) := WellFounded.fix_eq .. 
      rw [recurrence]; exact ok j (fun k _ => e k) i ij
    have inj : Function.Injective (fun j => (e j).val) := by
      intro i j eq
      rcases lt_trichotomy i j with lt | h | gt
      · exact (False.elim ((forward lt).1 eq))
      · exact h
      · exact (False.elim ((forward gt).1 eq.symm))
    exact Or.inr ⟨⟨_,inj⟩,fun i j ne => (lt_or_gt_of_ne ne).elim (fun h => (forward h).2) (fun h => (forward h).2.symm)⟩
  · let State := {Y : Set Row // ¬ Y.Countable}
    have find (Y : State) : ∃ a ∈ Y.val, ¬{b ∈ Y.val | blue a b}.Countable := by
      by_contra! all
      exact thin ⟨Y.val,Y.property,all⟩
    choose pick mem big using find
    let initial : State := ⟨univ,cofinal_uncountable IsCofinal.univ⟩
    let next (Y : State) : State := ⟨{b ∈ Y.val | blue (pick Y) b},big Y⟩
    let states : ℕ → State := Nat.rec initial (fun _ y => next y)
    let e (n : ℕ) := pick (states n)
    have down (n : ℕ) : (states (n+1)).val ⊆ (states n).val := fun _ h => h.1
    have nested {i j : ℕ} (le : i≤j) : (states j).val ⊆ (states i).val := by
      induction le with
      | refl => exact Subset.rfl
      | step _ ih => exact (down _).trans ih
    have forward {i j : ℕ} (lt : i<j) : blue (e i) (e j) :=
      (show e j ∈ (states (i+1)).val from nested lt (mem (states j))).2
    have inj : Function.Injective e := by
      intro i j eq
      rcases lt_trichotomy i j with lt | h | gt
      · exact (False.elim ((forward lt).1 eq))
      · exact h
      · exact (False.elim ((forward gt).1 eq.symm))
    exact Or.inl ⟨⟨e,inj⟩,fun i j ne => (lt_or_gt_of_ne ne).elim (fun h => (forward h).2)
      (fun h => fun edge => (forward h).2 edge.symm)⟩

variable {P : Type u} [Group P] {A : Type v} [MulAction (Row→P) A]

/-- A countable independent sequence or an ω₁-clique with one common support,
as required for their injections to belong to the permutation model. -/
def SupportedEDM (X : Set A) (G : SimpleGraph X) : Prop :=
  (∃ (e : ℕ ↪ X) (D : Set Row), Small D ∧ (∀ i, Holds (P := P) D (e i).val) ∧
    ∀ i j, i≠j → ¬ G.Adj (e i) (e j)) ∨
  (∃ (e : Row ↪ X) (D : Set Row), Small D ∧ (∀ i, Holds (P := P) D (e i).val) ∧
    ∀ i j, i≠j → G.Adj (e i) (e j))

theorem edm_from_comparison (X : Set A) (G : SimpleGraph X) (compare : SetComparison (P := P) X)
    (large : ¬∃ (_ : X ↪ ℕ) (D : Set Row), Small D ∧ ∀ a ∈ X, Holds (P := P) D a) :
    SupportedEDM (P := P) X G := by
  obtain ⟨e,D,small,fixed⟩ := compare.resolve_left large
  rcases edm_on_rows (G.comap e) with ⟨f,h⟩ | ⟨f,h⟩
  · exact Or.inl ⟨f.trans e,D,small,fun i => fixed (f i),h⟩
  · exact Or.inr ⟨f.trans e,D,small,fun i => fixed (f i),h⟩

/-- The graph principle on all internally uncountable supported carriers in
the same five-letter model in which the indexed row families lack selectors. -/
theorem five_edm {Y : Type v} [MulAction (Row→FiveGroup) Y] (X : Set Y) (G : SimpleGraph X)
    (setSym : SymmetricSet (P := FiveGroup) X) (points : SymmetricPoints (P := FiveGroup) X)
    (large : ¬∃ (_ : X ↪ ℕ) (D : Set Row), Small D ∧ ∀ a ∈ X, Holds (P := FiveGroup) D a) :
    SupportedEDM (P := FiveGroup) X G := edm_from_comparison X G (five_comparison X setSym points) large

end ChoiceOmegaOne
