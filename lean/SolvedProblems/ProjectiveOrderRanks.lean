module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Ring.Parity

public section

namespace ProjectiveZF

open Set Function

/-- If infinitely many elements of a linear order have finitely many strict
predecessors, every natural number occurs as one of those predecessor counts. -/
theorem ranksAttained {B : Type*} [LinearOrder B] (large : {b : B | (Iio b).Finite}.Infinite) (n : ℕ) :
    ∃ b : B, (Iio b).Finite ∧ (Iio b).ncard = n := by
  classical
  obtain ⟨T,sub,num⟩ := large.exists_subset_card_eq (n+1)
  have nonempty : T.Nonempty := Finset.card_pos.mp (num ▸ Nat.succ_pos n)
  let a := T.max' nonempty
  have finite : (Iio a).Finite := sub (T.max'_mem nonempty)
  have bounded : (Iic a).Finite := (finite.insert a).subset (by intro x h; rcases le_iff_lt_or_eq.mp h with h|h; exact Set.mem_insert_of_mem _ h; exact Set.mem_insert_iff.mpr (Or.inl h))
  let D := bounded.toFinset
  have cap : T ⊆ D := fun x hx => bounded.mem_toFinset.mpr (T.le_max' _ hx)
  have size := Finset.card_le_card cap
  rw [num] at size
  have enough : n < D.card := size
  let e := D.orderIsoOfFin (k := D.card) rfl
  let i : Fin D.card := ⟨n,enough⟩
  let b := (e i).val
  let v (j : Fin n) := (e ⟨j.val,j.isLt.trans enough⟩).val
  have inj : Injective v := fun j t eq => Fin.ext (congrArg (Fin.val : Fin D.card → ℕ) (e.injective (Subtype.ext eq)))
  have eq : Set.range v = Iio b := by
    ext z
    constructor
    · rintro ⟨j,rfl⟩
      exact (e.lt_iff_lt).mpr (show (⟨j.val,j.isLt.trans enough⟩ : Fin D.card) < i from j.isLt)
    · intro h
      have ba : b ≤ a := bounded.mem_toFinset.mp (e i).property
      let zD : D := ⟨z,bounded.mem_toFinset.mpr (le_trans (le_of_lt h) ba)⟩
      have before : e.symm zD < i := (e.lt_iff_lt).mp (by simpa [zD] using (show zD < e i from h))
      refine ⟨⟨(e.symm zD).val,before⟩,?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply zD)
  refine ⟨b,eq ▸ Set.finite_range v,?_⟩
  rw [← eq,Set.ncard_range_of_injective inj,Nat.card_fin]

/-- Any predicate that tests parity correctly on the finite strict initial
segments separates two infinite subsets when such segments have unbounded size. -/
theorem rankParitySplits {B : Type*} [LinearOrder B] (large : {b : B | (Iio b).Finite}.Infinite)
    (P : B → Prop) (parity : ∀ b, (Iio b).Finite → (P b ↔ Even (Iio b).ncard)) :
    {b | P b}.Infinite ∧ {b | ¬P b}.Infinite := by
  classical
  choose b small rank using ranksAttained large
  have inj : Injective b := fun i j h => (rank i).symm.trans (h ▸ rank j)
  constructor
  · apply (Set.infinite_range_of_injective (f := fun j : ℕ => b (2*j)) (inj.comp (by intro i j h; dsimp at h; omega))).mono
    rintro _ ⟨j,rfl⟩
    exact (parity _ (small _)).mpr (by rw [rank]; exact even_two_mul j)
  · apply (Set.infinite_range_of_injective (f := fun j : ℕ => b (2*j+1)) (inj.comp (by intro i j h; dsimp at h; omega))).mono
    rintro _ ⟨j,rfl⟩ h
    have odd := (parity _ (small _)).mp h
    rw [rank] at odd
    exact Nat.not_even_two_mul_add_one _ odd

end ProjectiveZF
