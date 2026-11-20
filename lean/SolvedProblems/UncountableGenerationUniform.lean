module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace UncountableGeneration

/-- The uniform law on m+1 indices, written as a normalized finite sum of point masses. -/
noncomputable def uniformLaw (m : ℕ) : Measure (Fin (m+1)) :=
  ((m+1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j : Fin (m+1), Measure.dirac j

instance uniformLaw_prob (m : ℕ) : IsProbabilityMeasure (uniformLaw m) := by
  refine ⟨?_⟩
  rw [uniformLaw, Measure.smul_apply, Measure.finsetSum_apply]
  simp [smul_eq_mul, ENNReal.inv_mul_cancel]

theorem uniformLaw_integral (m : ℕ) (f : Fin (m+1) → ℝ≥0∞) :
    (∫⁻ j, f j ∂uniformLaw m) = ((m+1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ j, f j := by
  rw [uniformLaw, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp [lintegral_dirac, smul_eq_mul]

end UncountableGeneration
