module

public import SolvedProblems.ReluCompression
public import SolvedProblems.ReluNetworkModel

@[expose] public section

open MeasureTheory
open scoped Topology NNReal

namespace ReluMoments

noncomputable def moments {d p j : ℕ} (f : Network d p) (μ : Measure (Vector d))
    (test : Fin j → Vector d → ℝ) (θ : Vector p) : Vector j :=
  fun i => ∫ x, test i x * f.eval θ x ∂μ

theorem integrable_weighted {d p : ℕ} (f : Network d p) (μ : Measure (Vector d))
    (w : Vector d → ℝ) (hw : AEStronglyMeasurable w μ)
    (hi : Integrable (fun x => |w x| * (1+‖x‖)) μ) (θ : Vector p) :
    Integrable (fun x => w x * f.eval θ x) μ := by
  obtain ⟨C,hC,h₀,_⟩ := f.envelope (R:=1+‖θ‖) (by simp)
  apply (hi.const_mul C).mono' (hw.mul (f.continuous_input θ).aestronglyMeasurable)
  filter_upwards with x
  rw [Pi.mul_apply,Real.norm_eq_abs,abs_mul]
  calc |w x| * |f.eval θ x| ≤ |w x| * (C*(1+‖x‖)) :=
         mul_le_mul_of_nonneg_left (h₀ θ (by linarith) x) (abs_nonneg _)
       _ = _ := by ring

theorem moments_locally {d p j : ℕ} (f : Network d p) (μ : Measure (Vector d))
    (test : Fin j → Vector d → ℝ) (hw : ∀ i, AEStronglyMeasurable (test i) μ)
    (hi : ∀ i, Integrable (fun x => |test i x| * (1+‖x‖)) μ) :
    LocallyLipschitz (moments f μ test) := by
  intro θ₀
  obtain ⟨C,hC,_,h₁⟩ := f.envelope (R:=1+‖θ₀‖) (by simp)
  let D (i : Fin j) := ∫ x, |test i x| * (1+‖x‖) ∂μ
  have hD (i) : 0 ≤ D i := integral_nonneg fun _ => by positivity
  let K : ℝ≥0 := ⟨C * ∑ i, D i, mul_nonneg hC (Finset.sum_nonneg fun i _ => hD i)⟩
  refine ⟨K,Metric.ball θ₀ 1,Metric.ball_mem_nhds _ zero_lt_one,?_⟩
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro θ hθ η hη
  have hb (t : Vector p) (ht : t ∈ Metric.ball θ₀ 1) : ‖t‖ ≤ 1+‖θ₀‖ := by
    rw [Metric.mem_ball,dist_eq_norm] at ht
    linarith only [ht,norm_le_norm_add_norm_sub' t θ₀]
  apply (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).mpr
  intro i
  rw [Real.dist_eq,dist_eq_norm]
  let u := fun x => test i x * f.eval θ x - test i x * f.eval η x
  have hui : Integrable u μ :=
    (integrable_weighted f μ (test i) (hw i) (hi i) θ).sub (integrable_weighted f μ (test i) (hw i) (hi i) η)
  change |(∫ x, test i x * f.eval θ x ∂μ) - (∫ x, test i x * f.eval η x ∂μ)| ≤ _
  rw [←integral_sub (integrable_weighted f μ (test i) (hw i) (hi i) θ)
    (integrable_weighted f μ (test i) (hw i) (hi i) η)]
  change ‖∫ x, u x ∂μ‖ ≤ _
  calc ‖∫ x, u x ∂μ‖ ≤ ∫ x, ‖u x‖ ∂μ := norm_integral_le_integral_norm _
       _ ≤ ∫ x, (|test i x| * (1+‖x‖)) * (C*‖θ-η‖) ∂μ := by
         apply integral_mono hui.norm ((hi i).mul_const _)
         intro x
         simp only [u,←mul_sub,Real.norm_eq_abs,abs_mul]
         calc _ ≤ |test i x| * (C*(1+‖x‖)*‖θ-η‖) :=
                mul_le_mul_of_nonneg_left (h₁ θ η (hb θ hθ) (hb η hη) x) (abs_nonneg _)
              _ = _ := by ring
       _ = D i * (C*‖θ-η‖) := integral_mul_const _ _
       _ ≤ (∑ k, D k) * (C*‖θ-η‖) :=
         mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_univ i)) (by positivity)
       _ = (K : ℝ) * ‖θ-η‖ := by change _ = (C * ∑ i, D i) * ‖θ-η‖; ring

/-- For arbitrary scalar ReLU networks with shared indices, almost every fixed
matrix with more than twice the parameter count preserves the complete finite
moment vector for every parameter pair. -/
theorem network_compression {d p j m : ℕ} (hm : 2*p < m) (f : Network d p)
    (μ : Measure (Vector d)) (test : Fin j → Vector d → ℝ)
    (hw : ∀ i, AEStronglyMeasurable (test i) μ)
    (hi : ∀ i, Integrable (fun x => |test i x| * (1+‖x‖)) μ) :
    ∀ᵐ A : Measurements m j ∂volume, ∀ θ η,
      measureVector A (moments f μ test θ) = measureVector A (moments f μ test η) ↔
        moments f μ test θ = moments f μ test η := by
  filter_upwards [compression hm _ (moments_locally f μ test hw hi)] with A hA
  exact fun θ η => ⟨hA θ η,congrArg _⟩

/-- Each coordinate of the compressed vector is one fixed weighted integral.
In particular, a linear combination of polynomial tests is again polynomial. -/
theorem measurement_integral {d p j m : ℕ} (f : Network d p) (μ : Measure (Vector d))
    (test : Fin j → Vector d → ℝ) (hw : ∀ i, AEStronglyMeasurable (test i) μ)
    (hi : ∀ i, Integrable (fun x => |test i x| * (1+‖x‖)) μ)
    (A : Measurements m j) (i : Fin m) (θ : Vector p) :
    measureVector A (moments f μ test θ) i =
      ∫ x, (∑ k, A (i,k) * test k x) * f.eval θ x ∂μ := by
  simp_rw [Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun k _ => (integrable_weighted f μ _ (hw k) (hi k) θ).const_mul (A (i,k)))]
  simp only [integral_const_mul,measureVector,moments]

end ReluMoments
