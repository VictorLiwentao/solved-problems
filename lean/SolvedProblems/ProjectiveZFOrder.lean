module

public import SolvedProblems.ProjectiveZFParity
public import SolvedProblems.ProjectiveOrderRanks

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- Every internally represented subset of `X` is externally finite or
cofinite. This is the finite/cofinite clause for omega-standard models. -/
def SmallSubsets (X : V) : Prop := ∀ t : V,
  {x : El X | x.val ∈ t}.Finite ∨ {x : El X | x.val ∉ t}.Finite

include M in
theorem small_definable {X : V} (small : SmallSubsets X) {P : V → Prop} (h : Unary P) :
    {x : El X | P x.val}.Finite ∨ {x : El X | ¬P x.val}.Finite := by
  obtain ⟨z,hz⟩ := M.separation X P h
  have eq (x : El X) : (x.val ∈ z) = P x.val := propext <| (hz x.val).trans (and_iff_right x.property)
  simpa only [eq] using small z

/-- Finitely many predecessors of even size can be recognized by a pure
first-order formula with a finite parameter list. -/
def EvenRay (X : V) (R : V → V → Prop) (x : V) : Prop :=
  ∃ T : V, (∀ a, a ∈ T ↔ a ∈ X ∧ R a x) ∧ Balanced T

theorem defEvenRay (X : V) (R : V → V → Prop) (dr : Binary R) : Unary (EvenRay X R) := by
  unfold Unary EvenRay
  repeat' first | apply defBinary dr | apply defBalanced | apply defIff | apply defEx | apply defAll | apply defAnd
                | apply defMem | zf_terms

private def rayEquiv {X T : V} [LinearOrder (El X)] {R : V → V → Prop} (ord : ∀ a b : El X, R a.val b.val ↔ a < b)
    (x : El X) (rep : ∀ a, a ∈ T ↔ a ∈ X ∧ R a x.val) : El T ≃ (Iio x : Set (El X)) where
  toFun t := ⟨⟨t.val,((rep _).mp t.property).1⟩,(ord _ x).mp ((rep _).mp t.property).2⟩
  invFun t := ⟨t.val.val,(rep _).mpr ⟨t.val.property,(ord _ x).mpr t.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

include M

theorem rayParity {X : V} [LinearOrder (El X)] (R : V → V → Prop) (dr : Binary R)
    (ord : ∀ a b : El X, R a.val b.val ↔ a < b) (x : El X) (finite : (Iio x).Finite) :
    EvenRay X R x.val ↔ Even (Iio x).ncard := by
  have cast (T : V) (rep : ∀ a, a ∈ T ↔ a ∈ X ∧ R a x.val) : Balanced T ↔ Even (Iio x).ncard := by
    let e := rayEquiv ord x rep
    let := finite.to_subtype
    let := Finite.of_equiv (Iio x : Set (El X)) e.symm
    rw [balanced_iff_even M,Nat.card_congr e,Nat.card_coe_set_eq]
  refine ⟨fun ⟨T,h,bal⟩ => (cast T h).mp bal,fun even => ?_⟩
  obtain ⟨T,rep⟩ := M.separation X (fun a => R a x.val) (defBinary dr (termVar ()) (termParam _))
  exact ⟨T,rep,(cast T rep).mpr even⟩

private theorem finite_lower {X : V} [LinearOrder (El X)] (small : SmallSubsets X) (R : V → V → Prop) (dr : Binary R)
    (ord : ∀ a b : El X, R a.val b.val ↔ a < b) : {x : El X | (Iio x).Finite}.Finite := by
  by_contra large
  obtain ⟨ev,odd⟩ := rankParitySplits large (fun x => EvenRay X R x.val) (rayParity M R dr ord)
  exact (small_definable M small (defEvenRay X R dr)).elim ev odd

/-- A set whose internal subsets are all externally finite or cofinite cannot
be both externally infinite and internally linearly ordered. The order here
may be any relation definable in the pure membership language. -/
theorem finiteOfDefinableOrder (X : V) [LinearOrder (El X)] (small : SmallSubsets X) (R : V → V → Prop) (dr : Binary R)
    (ord : ∀ a b : El X, R a.val b.val ↔ a < b) : Finite (El X) := by
  have low := finite_lower M small R dr ord
  have high : {x : El X | (Ioi x).Finite}.Finite := by
    let : LinearOrder (El X) := inferInstanceAs (LinearOrder (El X)ᵒᵈ)
    exact finite_lower M small (fun a b => R b a) (defBinary dr (termVar true) (termVar false)) (fun a b => ord b a)
  apply Set.finite_univ_iff.mp
  apply (low.union high).subset
  intro b _
  have sides := small_definable M small (P := fun a => R a b.val) (defBinary dr (termVar ()) (termParam _))
  have cut (a : El X) : R a.val b.val = (a < b) := propext (ord a b)
  simp only [cut] at sides
  exact sides.imp_right (fun h => h.subset fun _ hx => lt_asymm hx)

end ProjectiveZF
