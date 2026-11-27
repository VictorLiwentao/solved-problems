module

public import SolvedProblems.EMXApproximation
public import SolvedProblems.EMXSampling
import SolvedProblems.EMXCounting
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace EMX

open Set MeasureTheory
open scoped ENNReal Classical

def candidates (s j : ℕ) (k : Fin (slots s)) : Set Point := ↑(support (restricted s j k))

theorem block_disjoint (s : ℕ) (k : Fin (slots s)) :
    Pairwise (fun i j => Disjoint (candidates s i k) (candidates s j k)) := by
  intro i j ne
  apply Set.disjoint_left.mpr
  intro x hi hj
  apply ne
  have a := in_block hi
  have b := in_block hj
  rw [restricted_block] at a b
  exact a.symm.trans b

/-- Within a slot the sets for distinct blocks are disjoint, so the sum of the
single-set deviation bounds costs only one unit of probability mass. -/
theorem uniform_tail (s : ℕ) (μ : Measure Point) [IsProbabilityMeasure μ] {m : ℕ}
    (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    Measure.pi (fun _ : Fin m => μ)
      (⋃ k : Fin (slots s), ⋃ j : ℕ, {xs | η ≤ |frequency (candidates s j k) xs -
        μ.real (candidates s j k)|}) ≤ ENNReal.ofReal (slots s / ((m:ℝ)*η^2)) := by
  classical
  let ν := Measure.pi (fun _ : Fin m => μ)
  let M := ENNReal.ofReal (1 / ((m:ℝ)*η^2))
  let E (k : Fin (slots s)) (j : ℕ) := {xs : Fin m → Point |
    η ≤ |frequency (candidates s j k) xs - μ.real (candidates s j k)|}
  have forSlot (k : Fin (slots s)) : ν (⋃ j, E k j) ≤ M := by
    calc
      _ ≤ ∑' j : ℕ, ν (E k j) := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, μ (candidates s j k) * M := ENNReal.tsum_le_tsum
        (fun _ => frequency_tail μ MeasurableSet.of_discrete hm hη)
      _ = μ (⋃ j, candidates s j k) * M := by
        rw [ENNReal.tsum_mul_right, measure_iUnion (block_disjoint s k) (fun _ => MeasurableSet.of_discrete)]
      _ ≤ 1*M := mul_le_mul_of_nonneg_right (by simpa using measure_mono (μ := μ) (subset_univ (⋃ j, candidates s j k))) zero_le
      _ = M := one_mul _
  change ν (⋃ k, ⋃ j, E k j) ≤ _
  calc
    _ ≤ ∑' k, ν (⋃ j, E k j) := measure_iUnion_le _
    _ ≤ ∑' _k : Fin (slots s), M := ENNReal.tsum_le_tsum forSlot
    _ = (slots s : ℝ≥0∞) * M := by simp
    _ = _ := by
      rw [show (slots s : ℝ) / ((m:ℝ)*η^2) = slots s * (1 / ((m:ℝ)*η^2)) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

noncomputable def stageLearner (s : ℕ) : Learner :=
  fun _ xs => restricted s (best s xs).1 (best s xs).2

theorem empirical_eq {m} (h : Hyp) (xs : Fin m → Point) :
    frequency (support h : Set Point) xs = (hits xs h : ℝ) / m := by
  unfold frequency hits
  congr 1
  simpa only [Set.indicator_apply, Finset.mem_coe] using (Finset.sum_boole (R := ℝ) (fun i => xs i ∈ support h) Finset.univ)

theorem stage_bound (s : ℕ) (μ : Measure Point) [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) :
    Measure.pi (fun _ : Fin m => μ) (deficitEvent (stageLearner s) μ m (3/(s+1:ℝ)))
      ≤ ENNReal.ofReal ((slots s : ℝ) / ((m:ℝ)*(1/(s+1:ℝ))^2)) := by
  let η : ℝ := 1/(s+1:ℝ)
  have hη : 0 < η := by dsimp [η]; positivity
  apply (measure_mono _).trans (uniform_tail s μ hm hη)
  intro xs hx
  obtain ⟨h, hh⟩ := hx
  obtain ⟨v, hv⟩ := approximates μ s h
  let w := best s xs
  by_contra hout
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hout
  have a := (abs_lt.mp (hout v.2 v.1)).1
  have b := (abs_lt.mp (hout w.2 w.1)).2
  change -η < frequency (support (restricted s v.1 v.2) : Set Point) xs - _ at a
  change frequency (support (restricted s w.1 w.2) : Set Point) xs - _ < η at b
  rw [empirical_eq] at a b
  have score := div_le_div_of_nonneg_right
    (show (hits xs (restricted s v.1 v.2) : ℝ) ≤ hits xs (restricted s w.1 w.2) by
      exact_mod_cast best_spec s xs v) (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  change μ.real (support (restricted s w.1 w.2) : Set Point) + 3/(s+1:ℝ) < _ at hh
  change -η < _ - μ.real (support (restricted s v.1 v.2) : Set Point) at a
  change _ - μ.real (support (restricted s w.1 w.2) : Set Point) < η at b
  dsimp only [η] at a b
  rw [show (3:ℝ)/(s+1) = 3*(1/(s+1:ℝ)) by ring] at hh
  linarith only [hh,hv,a,b,score]

end EMX
