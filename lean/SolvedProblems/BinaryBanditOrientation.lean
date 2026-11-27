module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Data.Set.Countable

@[expose] public section

open Set Cardinal

namespace BinaryBandit

/-- An orientation of the complete loopless graph with countable out-neighborhoods. -/
def CountableOrientation (X : Type) : Prop :=
  ∃ r : X → X → Prop, (∀ x, ¬ r x x) ∧
    (∀ x y, x ≠ y → (r x y ↔ ¬ r y x)) ∧ ∀ x, {y | r x y}.Countable

abbrev FirstUncountable := (ℵ₁ : Cardinal.{0}).ord.ToType

theorem size_first_uncountable : #FirstUncountable = ℵ₁ := by
  rw [FirstUncountable, mk_toType, Cardinal.card_ord]

instance : Uncountable FirstUncountable := Cardinal.aleph0_lt_mk_iff.mp (by
  rw [size_first_uncountable]
  exact aleph0_lt_aleph_one)

theorem countable_earlier (i : FirstUncountable) : (Iio i).Countable := by
  apply le_aleph0_iff_set_countable.mp
  exact not_lt.mp fun h ↦ (show #(Iio i) < ℵ₁ by simpa [FirstUncountable] using Cardinal.mk_Iio_lt i (by simp [FirstUncountable])).not_ge (aleph_one_le_iff.mpr h)

/-- The manuscript's alternative eligibility rule: the cardinal bound is
equivalent to admitting a complete-graph orientation of countable out-degree. -/
theorem countable_orientation_iff (X : Type) : CountableOrientation X ↔ #X ≤ ℵ₁ := by
  classical
  constructor
  · rintro ⟨r, _, complete, degree⟩
    by_contra! large
    obtain ⟨e⟩ := (le_def FirstUncountable X).mp (size_first_uncountable ▸ large.le)
    let setAt (i : FirstUncountable) : Set X := insert (e i) {y | r (e i) y}
    have bounds (i : FirstUncountable) : #(setAt i) ≤ ℵ₀ :=
      le_aleph0_iff_set_countable.mpr ((degree _).insert _)
    have small : #(⋃ i, setAt i) ≤ ℵ₁ := by
      calc _ ≤ #FirstUncountable * ⨆ i, #(setAt i) := mk_iUnion_le setAt
           _ ≤ #FirstUncountable * ℵ₀ := mul_le_mul_right (ciSup_le bounds) _
           _ = ℵ₁ := by rw [size_first_uncountable, aleph_mul_aleph0]
    have outside : ∃ z : X, z ∉ ⋃ i, setAt i := by
      by_contra! full
      rw [eq_univ_of_forall full, mk_univ] at small
      exact large.not_ge small
    obtain ⟨z,hz⟩ := outside
    have arrow (i : FirstUncountable) : r z (e i) := by
      have h : z ∉ setAt i := fun h ↦ hz (mem_iUnion_of_mem i h)
      have hne : z ≠ e i := fun he ↦ h (Or.inl he)
      exact (complete z (e i) hne).2 fun he ↦ h (Or.inr he)
    let f (i : FirstUncountable) : {y // r z y} := ⟨e i, arrow i⟩
    have one := mk_le_of_injective (f := f) (fun i j he ↦ e.injective (congrArg Subtype.val he))
    have contra : ℵ₁ ≤ ℵ₀ := size_first_uncountable ▸ one.trans (le_aleph0_iff_set_countable.mpr (degree z))
    exact (aleph_one_le_iff.mp contra).false
  · intro small
    obtain ⟨e⟩ := (le_def X FirstUncountable).mp (size_first_uncountable ▸ small)
    refine ⟨fun x y ↦ e y < e x, fun _ ↦ lt_irrefl _, ?_, ?_⟩
    · intro x y hxy
      exact ⟨fun h ↦ not_lt_of_ge h.le, fun h ↦ lt_of_le_of_ne (le_of_not_gt h) (fun he ↦ hxy (e.injective he.symm))⟩
    · intro x
      exact (countable_earlier (e x)).preimage e.injective

end BinaryBandit
