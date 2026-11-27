module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace EMX

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable def frequency {X : Type} {m : ℕ} (S : Set X) (xs : Fin m → X) : ℝ :=
  (∑ i, S.indicator (fun _ => (1 : ℝ)) (xs i)) / m

/-- The single-set deviation bound retains the factor μ(S), allowing a countable
union bound for families disjoint within each slot. -/
theorem frequency_tail {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {S : Set X} (hs : MeasurableSet S) {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    Measure.pi (fun _ : Fin m => μ) {xs | η ≤ |frequency S xs - μ.real S|}
      ≤ μ S * ENNReal.ofReal (1 / ((m:ℝ) * η^2)) := by
  classical
  let f := S.indicator (fun _ => (1 : ℝ))
  let ν := Measure.pi (fun _ : Fin m => μ)
  let Y (i : Fin m) (xs : Fin m → X) := f (xs i)
  let Z (xs : Fin m → X) := ∑ i, Y i xs
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hf : MemLp f 2 μ := (memLp_const (1:ℝ)).indicator hs.nullMeasurableSet
  have hY (i) : MemLp (Y i) 2 ν := hf.comp_measurePreserving (measurePreserving_eval _ i)
  have hZ : MemLp Z 2 ν := memLp_finsetSum _ fun i _ => hY i
  have intf : ∫ x, f x ∂μ = μ.real S := integral_indicator_one hs
  have intY (i) : ∫ xs, Y i xs ∂ν = μ.real S := (integral_comp_eval (μ := fun _ : Fin m => μ) (i := i) (f := f) hf.aestronglyMeasurable).trans intf
  have eZ : ∫ xs, Z xs ∂ν = m * μ.real S := by
    rw [show (∫ xs, Z xs ∂ν) = ∑ i, ∫ xs, Y i xs ∂ν from
      integral_finsetSum _ fun i _ => (hY i).integrable (by norm_num)]
    simp [intY]
  have vf : variance f μ ≤ μ.real S := by
    have sqf : f ^ 2 = f := by
      funext x
      by_cases hx : x ∈ S <;> simp [f, hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    simpa only [sqf, intf] using variance_le_expectation_sq hf.aestronglyMeasurable
  have vZ : variance Z ν ≤ m * μ.real S := by
    have h : variance Z ν = ∑ _i : Fin m, variance f μ := by
      convert variance_sum_pi (μ := fun _ : Fin m => μ) (X := fun _ => f) (fun _ => hf) using 2
      funext xs; simp [Z, Y]
    rw [h]
    simpa using mul_le_mul_of_nonneg_left vf hm'.le
  have eventSub : {xs : Fin m → X | η ≤ |frequency S xs - μ.real S|} ⊆
      {xs | (m:ℝ)*η ≤ |Z xs - ∫ xs, Z xs ∂ν|} := by
    intro xs hx
    change η ≤ |Z xs / m - μ.real S| at hx
    change (m:ℝ)*η ≤ |Z xs - ∫ xs, Z xs ∂ν|
    rw [eZ, show Z xs - (m:ℝ)*μ.real S = (m:ℝ)*(Z xs/m - μ.real S) by field_simp,
      abs_mul, abs_of_pos hm']
    exact mul_le_mul_of_nonneg_left hx hm'.le
  calc
    _ ≤ _ := measure_mono (μ := ν) eventSub
    _ ≤ _ := meas_ge_le_variance_div_sq hZ (mul_pos hm' hη)
    _ ≤ ENNReal.ofReal ((m * μ.real S) / ((m:ℝ)*η)^2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right vZ (sq_nonneg _))
    _ = _ := by
      rw [show ((m:ℝ) * μ.real S) / ((m:ℝ)*η)^2 = μ.real S * (1 / ((m:ℝ)*η^2)) by field_simp]
      rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end EMX
