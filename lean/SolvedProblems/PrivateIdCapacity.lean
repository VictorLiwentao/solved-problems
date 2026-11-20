module

public import SolvedProblems.PrivateIdModel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Card

import Mathlib.MeasureTheory.Measure.Dirac.Def

public section

open MeasureTheory Set
open scoped ENNReal

namespace PrivateIdentification

open scoped BigOperators
noncomputable section

open Classical in
private def winners {s k : ℕ} (u : Transcript s k) : Finset (Fin s) :=
  Finset.univ.filter fun i ↦ u ∈ Success i

private theorem mem_winners {s k : ℕ} {u : Transcript s k} {i : Fin s} :
    i ∈ winners u ↔ u ∈ Success i := by
  classical
  simp [winners]

/-- All eventual winners appear together after the latest of their finitely many
starting times, so distinct winners must occupy distinct slots. -/
private theorem winners_card_le {s k : ℕ} (u : Transcript s k) : (winners u).card ≤ k := by
  classical
  let N (i : ↥(winners u)) := (mem_winners.mp i.property).choose
  let last := Finset.univ.sup N
  have h (i : ↥(winners u)) : ∃ j, u last j = i.val.succ :=
    (mem_winners.mp i.property).choose_spec _ (Finset.le_sup (f := N) (Finset.mem_univ i))
  have inj : Function.Injective (fun i ↦ (h i).choose) := by
    intro i j e
    apply Subtype.ext
    apply Fin.succ_injective
    calc
      i.val.succ = u last (h i).choose := (h i).choose_spec.symm
      _ = u last (h j).choose := congrArg (u last) e
      _ = j.val.succ := (h j).choose_spec
  simpa using Fintype.card_le_of_injective _ inj

private def rotation {s k : ℕ} (hk : k ≤ s) (r : Fin s) : Transcript s k :=
  fun _ j ↦ (r + j.castLE hk).succ

open Classical in
private theorem count_rotations {s k : ℕ} (hk : k ≤ s) [NeZero s] (i : Fin s) :
    (Finset.univ.filter fun r : Fin s ↦ rotation hk r ∈ Success i).card = k := by
  classical
  let f : Fin k → Fin s := fun j ↦ i - j.castLE hk
  have hi : Function.Injective f := by
    intro j j' h
    apply Fin.ext
    have he : j.castLE hk = j'.castLE hk := sub_right_inj.mp h
    exact congrArg (Fin.val (n := s)) he
  have hset : (Finset.univ.filter fun r : Fin s ↦ rotation hk r ∈ Success i) =
      Finset.univ.image f := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨j, hj⟩ := hN N le_rfl
      have he : r + j.castLE hk = i := Fin.succ_injective _ hj
      exact ⟨j, (eq_sub_of_add_eq he).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨0, fun _ _ ↦ ⟨j, by simp [rotation, f]⟩⟩
  rw [hset, Finset.card_image_of_injective _ hi]
  simp


/-- Decompose the law by its finite set of eventual winners, and count the
winner incidences in each cell. -/
theorem some_low {s k : ℕ} (μ : Measure (Transcript s k)) [IsProbabilityMeasure μ]
    (hs : 0 < s) : ∃ i, μ.real (Success i) ≤ (k : ℝ) / s := by
  classical
  let cell (t : Finset (Fin s)) := {u : Transcript s k | winners u = t}
  have cell_meas (t) : MeasurableSet (cell t) := by
    have he : cell t = ⋂ i : Fin s, if i ∈ t then Success i else (Success i)ᶜ := by
      ext u
      simp only [cell, Set.mem_ofPred_eq, Set.mem_iInter]
      rw [Finset.ext_iff]
      simp only [mem_winners]
      exact forall_congr' fun i ↦ by by_cases hi : i ∈ t <;> simp [hi]
    rw [he]
    exact MeasurableSet.iInter fun i ↦ by
      split <;> first | exact measurableSet_success i | exact (measurableSet_success i).compl
  have disj {t t' : Finset (Fin s)} (h : t ≠ t') : Disjoint (cell t) (cell t') :=
    Set.disjoint_left.mpr fun _ ht ht' ↦ h (ht.symm.trans ht')
  have split_by (E : Set (Transcript s k)) (hE : MeasurableSet E) :
      μ.real E = ∑ t, μ.real (E ∩ cell t) := by
    have he : E = ⋃ t, E ∩ cell t := by
      ext u
      simp [cell]
    conv_lhs => rw [he]
    apply measureReal_iUnion_fintype
    · intro t t' h
      exact (disj h).mono Set.inter_subset_right Set.inter_subset_right
    · exact fun t ↦ hE.inter (cell_meas t)
    · exact fun _ ↦ measure_ne_top _ _
  have total : (∑ t, μ.real (cell t)) = 1 := by
    simpa using (split_by Set.univ MeasurableSet.univ).symm
  have split_success (i : Fin s) : μ.real (Success i) =
      ∑ t, if i ∈ t then μ.real (cell t) else 0 := by
    rw [split_by _ (measurableSet_success i)]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hi : i ∈ t
    · rw [ite_eq_left hi, Set.inter_eq_right.mpr]
      intro u hu
      apply mem_winners.mp
      change winners u = t at hu
      rwa [hu]
    · rw [ite_eq_right hi, ← measureReal_empty (μ := μ)]
      congr 1
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have h := mem_winners.mpr hu.1
      exact hi (hu.2 ▸ h)
  have bound : (∑ i, μ.real (Success i)) ≤ (k : ℝ) := calc
    _ = ∑ t, ∑ i : Fin s, if i ∈ t then μ.real (cell t) else 0 := by
      simp_rw [split_success]
      exact Finset.sum_comm
    _ = ∑ t, (t.card : ℝ) * μ.real (cell t) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ t, (k : ℝ) * μ.real (cell t) := by
      apply Finset.sum_le_sum
      intro t _
      by_cases h : (cell t).Nonempty
      · obtain ⟨u, hu⟩ := h
        change winners u = t at hu
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hu ▸ winners_card_le u)
          measureReal_nonneg
      · simp [Set.not_nonempty_iff_eq_empty.mp h]
    _ = _ := by rw [← Finset.mul_sum, total, mul_one]
  by_contra! h
  have : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have strict := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin s)))
    Finset.univ_nonempty (fun i _ ↦ h i)
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  simp [div_eq_mul_inv, mul_comm, hs'] at strict
  exact (not_lt_of_ge bound) strict

/-- Choose a uniform cyclic rotation of the fixed k-slot list and publish
that same list at every time. Exactly k rotations include each label. -/
theorem lottery {s k : ℕ} (hk : k ≤ s) (hs : 0 < s) :
    ∃ P : Mechanism s k, ProbLaw P ∧ Causal P ∧ PrivateWith P id ∧
      ∀ x i, (P x).real (Success i) = (k : ℝ) / s := by
  classical
  have : NeZero s := ⟨hs.ne'⟩
  let μ : Measure (Transcript s k) :=
    ∑ r : Fin s, ((s : ℝ≥0∞)⁻¹) • Measure.dirac (rotation hk r)
  have mass (E : Set (Transcript s k)) (hE : MeasurableSet E) :
      μ E = ((Finset.univ.filter fun r : Fin s ↦ rotation hk r ∈ E).card : ℝ≥0∞) / s := by
    rw [show μ E = _ from Measure.finsetSum_apply _ _ _]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hE]
    rw [div_eq_mul_inv, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    by_cases hr : rotation hk r ∈ E <;> simp [hr]
  refine ⟨fun _ ↦ μ, fun _ ↦ ⟨?_⟩, ?_, ?_, ?_⟩
  · rw [mass _ MeasurableSet.univ]
    simp [ENNReal.div_self, hs.ne']
  · intro _ _ _ _ _ _ _
    rfl
  · intro _ _ _ _ _
    exact le_rfl
  · intro _ i
    rw [measureReal_def, mass _ (measurableSet_success i), count_rotations]
    simp

end
end PrivateIdentification
