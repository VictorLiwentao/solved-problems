module

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReluMoments

noncomputable def standardLaplace : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (Real.exp (-|x|)/2)

instance laplaceOpen : standardLaplace.IsOpenPosMeasure := by
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure (μ := (volume : Measure ℝ))
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · exact Filter.Eventually.of_forall fun _ => (ENNReal.ofReal_pos.mpr (by positivity)).ne'

theorem gaussian_open (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : (gaussianReal m v).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' m hv).isOpenPosMeasure

theorem gaussian_envelope (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k * (1+|x|)) (gaussianReal m v) := by
  have h (n : ℕ) : Integrable (fun x : ℝ => |x|^n) (gaussianReal m v) :=
    (memLp_id_gaussianReal' (μ:=m) (v:=v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow'
  simpa only [Pi.add_def,mul_add,mul_one,←pow_succ] using (h k).add (h (k+1))

theorem laplace_abs_moment (k : ℕ) : Integrable (fun x : ℝ => |x|^k) standardLaplace := by
  have hp : IntegrableOn (fun x : ℝ => |x|^k * Real.exp (-|x|)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_rpow (p:=1) (s:=(k:ℝ)) (by linarith [Nat.cast_nonneg (α:=ℝ) k]) zero_lt_one
    apply h.congr_fun _ measurableSet_Ioi
    intro x hx
    simp [abs_of_pos hx,Real.rpow_natCast]
  have ha : Integrable (fun x : ℝ => |x|^k * Real.exp (-|x|)) := by
    rw [← integrableOn_univ,← @Iio_union_Ici _ _ (0 : ℝ),integrableOn_union,integrableOn_Ici_iff_integrableOn_Ioi]
    refine ⟨?_,hp⟩
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def,abs_neg,neg_preimage,neg_Iio,neg_zero] using hp
  unfold standardLaplace
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply (ha.mul_const (1/2 : ℝ)).congr
  filter_upwards with x
  simp only [ENNReal.toReal_ofReal (show 0 ≤ Real.exp (-|x|)/2 by positivity),smul_eq_mul]
  ring

theorem laplace_envelope (k : ℕ) : Integrable (fun x : ℝ => |x|^k * (1+|x|)) standardLaplace := by
  simpa only [Pi.add_def,mul_add,mul_one,←pow_succ] using (laplace_abs_moment k).add (laplace_abs_moment (k+1))

end ReluMoments
