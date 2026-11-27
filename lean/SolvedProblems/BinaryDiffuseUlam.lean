module

public import SolvedProblems.BinaryBanditOrientation
public import SolvedProblems.BinaryDiffuse

@[expose] public section

open Set MeasureTheory Cardinal Function
open scoped ENNReal

namespace BinaryDiffuse

open BinaryBandit

/-- Ulam's matrix: no space of cardinality at most aleph one admits a
countably additive probability on all of its subsets vanishing on singletons. -/
theorem ulam {X : Type} [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (small : #X ≤ ℵ₁) (μ : Measure X) [IsProbabilityMeasure μ]
    (hn : ∀ x : X, μ {x} = 0) : False := by
  classical
  let _ : NullSingletonClass μ := ⟨hn⟩
  obtain ⟨e⟩ := (le_def X FirstUncountable).mp (size_first_uncountable ▸ small)
  let numbering (β : FirstUncountable) (i : Iio β) :=
    @Encodable.encode _ (countable_earlier β).toEncodable i
  have inject (β : FirstUncountable) : Injective (numbering β) :=
    @Encodable.encode_injective _ (countable_earlier β).toEncodable
  let cell (i : FirstUncountable) (j : ℕ) : Set X :=
    {x | ∃ h : i < e x, numbering (e x) ⟨i,h⟩ = j}
  have disj (j : ℕ) : Pairwise (fun i k ↦ Disjoint (cell i j) (cell k j)) := by
    intro i k hne
    apply Set.disjoint_left.mpr
    rintro x ⟨hi, ei⟩ ⟨hk, ek⟩
    exact hne (congrArg Subtype.val (inject (e x) (ei.trans ek.symm)))
  have count (j : ℕ) : {i | 0 < μ (cell i j)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun _ ↦ MeasurableSet.of_discrete) (disj j)
  have out : ∃ i : FirstUncountable, ∀ j, μ (cell i j) = 0 := by
    by_contra! hall
    have cover : (⋃ j, {i | 0 < μ (cell i j)}) = Set.univ := by
      apply eq_univ_of_forall
      intro i
      obtain ⟨j,hj⟩ := hall i
      exact mem_iUnion_of_mem j (pos_iff_ne_zero.mpr hj)
    exact not_countable (α := FirstUncountable) (countable_univ_iff.mp (cover ▸ countable_iUnion count))
  obtain ⟨i,hi⟩ := out
  let initial := e ⁻¹' Iic i
  have hc : initial.Countable := by
    exact (Iio_insert (a := i) ▸ (countable_earlier i).insert i).preimage e.injective
  have cover : initial ∪ (⋃ j, cell i j) = Set.univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : e x ≤ i
    · exact Or.inl hx
    · have hlt := lt_of_not_ge hx
      exact Or.inr (mem_iUnion_of_mem (numbering (e x) ⟨i,hlt⟩) ⟨hlt,rfl⟩)
  have z := measure_union_null (hc.measure_zero μ) (measure_iUnion_null_iff.mpr hi)
  rw [cover, measure_univ] at z
  exact one_ne_zero z

/-- Under the continuum hypothesis the discrete bandit of Theorem 2 is
unlearnable, by the Ulam-matrix argument on the actual interval. -/
theorem not_learnable_of_CH (ch : (𝔠 : Cardinal.{0}) = ℵ₁) : ¬ BinaryDiffuse.Learnable := by
  intro h
  obtain ⟨μ,hp,hn⟩ := learnable_iff_diffuse.mp h
  exact ulam (X := Coord) (by rw [show #Coord = (𝔠 : Cardinal.{0}) from mk_unitInterval, ch]) μ hn

end BinaryDiffuse
