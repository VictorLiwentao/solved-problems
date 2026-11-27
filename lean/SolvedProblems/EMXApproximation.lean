module

public import SolvedProblems.EMXRestricted
public import SolvedProblems.EMXLaw
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

@[expose] public section

namespace EMX

open MeasureTheory Set
open scoped ENNReal Classical

def rowSet {j} (i : Row j) : Set Point :=
  ↑((omittedRow j i).val.map (Function.Embedding.sigmaMk j))

theorem disjoint_rows {j} {i k : Row j} (h : i ≠ k) : Disjoint (rowSet i) (rowSet k) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hc
  have hh : (i,z) ∈ (omittedRow j k).val := by simpa [rowSet] using hx'
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hh
  exact h (congrArg Prod.fst hw).symm

theorem cover_block {j} (h : Holes j) (row : Row j) :
    (support ⟨j,h⟩ : Set Point) ⊆ (support ⟨j,omittedRow j row⟩ : Set Point) ∪ rowSet row := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
  by_cases hh : c ∈ (omittedRow j row).val
  · exact Or.inr (Finset.mem_map.mpr ⟨c, hh, rfl⟩)
  · exact Or.inl (Finset.mem_map.mpr ⟨c, Finset.mem_compl.mpr hh, rfl⟩)

theorem light_row {s j : ℕ} (large : s ≤ j) (μ : Measure Point) [IsProbabilityMeasure μ] :
    ∃ i : Fin (s+1), μ.real (rowSet (rowIndex large i)) ≤ 1/(s+1:ℝ) := by
  let R (i : Fin (s+1)) := rowSet (rowIndex large i)
  have dis : Pairwise (fun i k => Disjoint (R i) (R k)) := by
    intro i k hn
    apply disjoint_rows
    exact fun he => hn (Fin.ext (congrArg (fun i : Row j => i.val) he))
  have total : (∑ i : Fin (s+1), μ.real (R i)) ≤ 1 := by
    simpa only [probReal_univ] using
      sum_measureReal_le_measureReal_univ (s := Finset.univ) (μ := μ)
        (t := R) (fun _ _ => MeasurableSet.of_discrete) (fun _ _ _ _ h => dis h)
  have hh : (∑ _i : Fin (s+1), 1/(s+1:ℝ)) = 1 := by
    simp [ne_of_gt (show (0:ℝ) < s+1 by positivity)]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    (f := fun i : Fin (s+1) => μ.real (R i)) (g := fun _ => 1/(s+1:ℝ))
    Finset.univ_nonempty (total.trans hh.ge)
  exact ⟨i,hi⟩

/-- Some retained hypothesis loses at most 1/(s+1) compared with each member of
the full family, uniformly in the distribution and the index of its block. -/
theorem approximates (μ : Measure Point) [IsProbabilityMeasure μ] (s : ℕ) (H : Hyp) :
    ∃ v : ℕ × Fin (slots s), μ.real (support H : Set Point) ≤
      μ.real (support (restricted s v.1 v.2) : Set Point) + 1/(s+1:ℝ) := by
  classical
  obtain ⟨j,h⟩ := H
  by_cases small : j < s
  · obtain ⟨k,hk⟩ := small_covered small h
    refine ⟨(j,k), ?_⟩
    change _ ≤ μ.real (support (restricted s j k) : Set Point) + _
    rw [hk]
    exact le_add_of_nonneg_right (by positivity)
  have large : s ≤ j := Nat.le_of_not_gt small
  obtain ⟨i, hi⟩ := light_row large μ
  obtain ⟨k, hk⟩ := large_covered large i
  refine ⟨(j,k), ?_⟩
  change _ ≤ μ.real (support (restricted s j k) : Set Point) + _
  rw [hk]
  exact (measureReal_mono (μ := μ) (cover_block h (rowIndex large i))).trans
    ((measureReal_union_le (μ := μ) _ _).trans (add_le_add le_rfl hi))

end EMX
