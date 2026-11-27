module

public import SolvedProblems.ProjectiveGaps
import SolvedProblems.ProjectiveCodeMatch
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Rat.Denumerable

public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {d : ℕ} {M : Type*} [L.Structure M] {κ ι : Type} [Finite κ] [Finite ι]

private def substMark (m : ι → ℚ) (a b : ℚ) (i : ι) : ℚ := if m i = a then b else m i

omit [Finite κ] in
private theorem change_one (core : κ → M) (B : ℚ → Fin d → M)
    (gaps : ∀ {J : Type} [Finite J] (m : J → ℚ) {u v : ℚ}, u ∉ Set.range m → v ∉ Set.range m →
      overMarks L core B m u = overMarks L core B m v)
    (m : ι → ℚ) (a b : ℚ) (fresh : b ∉ Set.range m) :
    tupleType L (marked core B m) = tupleType L (marked core B (substMark m a b)) := by
  classical
  let T := {i : ι // m i ≠ a}
  let rest (i : T) := m i.val
  have fa : a ∉ Set.range rest := by rintro ⟨i,hi⟩; exact i.property hi
  have fb : b ∉ Set.range rest := by rintro ⟨i,hi⟩; exact fresh ⟨i.val,hi⟩
  have h := gaps rest fa fb
  let keep : κ ⊕ (ι × Fin d) → (κ ⊕ (T × Fin d)) ⊕ Fin d :=
    Sum.elim (fun c => Sum.inl (Sum.inl c)) fun p =>
      if h : m p.1 = a then Sum.inr p.2 else Sum.inl (Sum.inr (⟨p.1,h⟩,p.2))
  have cut (t : ℚ) : Sum.elim (marked core B rest) (B t) ∘ keep = marked core B (substMark m a t) := by
    funext p
    rcases p with v|⟨j,i⟩
    · rfl
    · by_cases h : m j = a <;> simp [keep,substMark,marked,rest,Function.comp_apply,h]
  have mm := match_subtuple h keep
  rw [cut,cut] at mm
  have id' : substMark m a a = m := by funext i; by_cases h : m i = a <;> simp [substMark,h]
  rwa [id'] at mm

omit [Finite κ] in
private theorem swap_types (core : κ → M) (B : ℚ → Fin d → M)
    (gaps : ∀ {J : Type} [Finite J] (m : J → ℚ) {u v : ℚ}, u ∉ Set.range m → v ∉ Set.range m →
      overMarks L core B m u = overMarks L core B m v)
    (m : ι → ℚ) (a b : ℚ) :
    tupleType L (marked core B m) = tupleType L (marked core B (_root_.Equiv.swap a b ∘ m)) := by
  classical
  by_cases eq : a = b
  · subst b; simp
  have small : (Set.range m ∪ {a,b}).Finite := (Set.finite_range m).union (by simp)
  obtain ⟨w,hw⟩ := small.exists_notMem
  have fw : w ∉ Set.range m := fun h => hw (Or.inl h)
  have wa : w ≠ a := fun h => hw (Or.inr (Or.inl h))
  have wb : w ≠ b := fun h => hw (Or.inr (Or.inr h))
  let u := substMark m a w
  let v := substMark u b a
  have h₁ := change_one core B gaps m a w fw
  have fa : a ∉ Set.range u := by
    rintro ⟨i,hi⟩
    by_cases e : m i = a <;> simp [u,substMark,e,wa] at hi
  have fb : b ∉ Set.range v := by
    rintro ⟨i,hi⟩
    by_cases e : u i = b <;> simp [v,substMark,e,eq] at hi
  have h₂ := change_one core B gaps u b a fa
  have h₃ := change_one core B gaps v w b fb
  have id' : substMark v w b = _root_.Equiv.swap a b ∘ m := by
    funext j
    have nw : m j ≠ w := fun h => fw ⟨j,h⟩
    by_cases ha : m j = a
    · simp [v,u,substMark,ha,wb]
    · by_cases hb : m j = b
      · simp [v,u,substMark,hb,Ne.symm eq,Ne.symm wa]
      · simp [v,u,substMark,ha,hb,nw,_root_.Equiv.swap_apply_def]
  rw [id'] at h₃
  exact h₁.trans (h₂.trans h₃)

/-- In this block geometry, every permutation of the rational index set
preserves the types of finite tuples of enumerated blocks, fixing the core.
The proof needs only finite type isolation and the explicit finite bound on
possible enumerations. -/
theorem totalIndiscernibility (fin : FiniteTypes L M) (min : Minimal L M)
    (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) (oi : OrderIndiscernible L core B)
    (indep : IndependentBlocks L core B i₀) (alg : AlgebraicBlocks L B i₀)
    (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ) :
    tupleType L (marked core B m) = tupleType L (marked core B (π ∘ m)) := by
  classical
  have gaps {J : Type} [Finite J] (m : J → ℚ) {u v : ℚ} := sameOverMarks fin min core B i₀ oi indep alg m (u := u) (v := v)
  let Good (e : _root_.Equiv.Perm ℚ) := ∀ z : ι → ℚ,
    tupleType L (marked core B z) = tupleType L (marked core B (e ∘ z))
  have approx (s : Finset ℚ) : ∃ e : _root_.Equiv.Perm ℚ, Good e ∧ ∀ i ∈ s, e i = π i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨_root_.Equiv.refl _,fun _ => rfl,by simp⟩
    | @insert a s fresh ih =>
      obtain ⟨e,good,agree⟩ := ih
      let f := _root_.Equiv.swap (e a) (π a)
      refine ⟨e.trans f,fun z => (good z).trans (swap_types core B gaps (e ∘ z) _ _),?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | mem
      · exact _root_.Equiv.swap_apply_left _ _
      · have ne : i ≠ a := fun h => fresh (h ▸ mem)
        have p : e i ≠ π a := (agree i mem) ▸ fun h => ne (π.injective h)
        exact (_root_.Equiv.swap_apply_of_ne_of_ne (fun h => ne (e.injective h)) p).trans (agree i mem)
  let := Fintype.ofFinite ι
  let s := Finset.univ.image m
  obtain ⟨e,good,agree⟩ := approx s
  have h : e ∘ m = π ∘ m := funext fun i => agree _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa only [h] using good m

end ProjectiveIndiscernibles
