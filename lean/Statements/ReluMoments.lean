module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Almost-everywhere compression of finite scalar-network moment measurements. -/

namespace ReluMoments

abbrev Vector (p : ℕ) := Fin p → ℝ
abbrev Measurements (m j : ℕ) := (Fin m × Fin j) → ℝ

/-- Apply fixed linear measurements to a finite vector of moments. -/
noncomputable def measureVector {m j : ℕ} (A : Measurements m j) (v : Vector j) : Vector m :=
  fun i => ∑ k, A (i,k) * v k

end ReluMoments

open Set MeasureTheory MeasureTheory.Measure Module Filter
open scoped Topology ENNReal NNReal

namespace ReluMoments

/-- Reconstruct the missing column of a matrix killing `v` from all other columns;
the chart is used only where `v h ≠ 0`. -/
noncomputable def chart {j m : ℕ} (h : Fin (j+1)) (u : Vector (j+1) × Measurements m j) : Measurements m (j+1) :=
  fun ik => h.insertNth (α := fun _ => ℝ) (-(∑ k : Fin j, u.2 (ik.1,k) * u.1 (h.succAbove k)) / u.1 h)
    (fun k : Fin j => u.2 (ik.1,k)) ik.2

abbrev PairDomain (p m j : ℕ) := (Vector p × Vector p) × Measurements m j

def secants {p q m j : ℕ} (f : Vector p → Vector q) (u : PairDomain p m j) : Vector q × Measurements m j :=
  (f u.1.1 - f u.1.2, u.2)

theorem secants_locally {p q m j : ℕ} {f : Vector p → Vector q} (hf : LocallyLipschitz f) :
    LocallyLipschitz (secants (m:=m) (j:=j) f) := by
  have h₁ : LocallyLipschitz (fun u : PairDomain p m j => f u.1.1) := hf.comp (LipschitzWith.prod_fst.comp LipschitzWith.prod_fst).locallyLipschitz
  have h₂ : LocallyLipschitz (fun u : PairDomain p m j => f u.1.2) := hf.comp (LipschitzWith.prod_snd.comp LipschitzWith.prod_fst).locallyLipschitz
  exact (h₁.sub h₂).prodMk LipschitzWith.prod_snd.locallyLipschitz

theorem chart_smooth {j m : ℕ} (h : Fin (j+1)) (u : Vector (j+1) × Measurements m j) (hu : u.1 h ≠ 0) :
    DifferentiableAt ℝ (chart (m:=m) h) u := by
  apply differentiableAt_pi.mpr
  intro ⟨i,k⟩
  induction k using h.succAboveCases with
  | x =>
    simp only [chart, Fin.insertNth_apply_same]
    simp only [div_eq_mul_inv]
    apply DifferentiableAt.fun_mul
    · fun_prop
    · exact DifferentiableAt.fun_inv (by fun_prop) hu
  | p k =>
    simp only [chart, Fin.insertNth_apply_succAbove]
    fun_prop

/-- Matrices destroying a secant through this chart are a null set. The
parameter dimension is 2p + m⨉j, strictly below m⨉(j+1) when m > 2p. -/
theorem chart_null {p j m : ℕ} (hm : 2*p<m) (h : Fin (j+1))
    {f : Vector p → Vector (j+1)} (hf : LocallyLipschitz f) :
    volume (chart h '' (secants (m:=m) (j:=j) f '' {u | (f u.1.1 - f u.1.2) h ≠ 0})) = 0 := by
  let U : Set (PairDomain p m j) := {u | (f u.1.1-f u.1.2) h ≠ 0}
  let g := secants (m:=m) (j:=j) f
  have hs : DifferentiableOn ℝ (chart (m:=m) h) (g '' U) := by
    rintro _ ⟨u,hu,rfl⟩
    exact (chart_smooth h (g u) hu).differentiableWithinAt
  have hdim : dimH (g '' U) ≤ dimH (Set.univ : Set (PairDomain p m j)) := by
    apply (dimH_mono (Set.image_subset_range g U)).trans
    exact dimH_range_le_of_locally_lipschitzOn (secants_locally hf)
  have hd : finrank ℝ (PairDomain p m j) < Fintype.card (Fin m × Fin (j+1)) := by
    simp only [PairDomain, Vector, Measurements, Module.finrank_prod, Module.finrank_pi,
      Fintype.card_fin, Fintype.card_prod]
    nlinarith only [hm]
  rw [Real.dimH_univ_eq_finrank] at hdim
  rw [← hausdorffMeasure_pi_real]
  apply hausdorffMeasure_of_dimH_lt (d := Fintype.card (Fin m × Fin (j+1)))
  exact hs.dimH_image_le.trans_lt (hdim.trans_lt (by exact_mod_cast hd))

/-- Almost every matrix with more than 2p rows is injective on the entire image
of any locally Lipschitz p-parameter moment map, with no global boundedness or
smoothness assumption. -/
theorem compression {p j m : ℕ} (hm : 2*p<m) (f : Vector p → Vector j) (hf : LocallyLipschitz f) :
    ∀ᵐ A : Measurements m j ∂volume, ∀ x y, measureVector A (f x) = measureVector A (f y) → f x = f y := by
  classical
  cases j with
  | zero => exact Filter.Eventually.of_forall fun _ _ _ _ => funext (fun i => Fin.elim0 i)
  | succ j =>
    let bad (h : Fin (j+1)) := chart h '' (secants (m:=m) (j:=j) f '' {u | (f u.1.1-f u.1.2) h ≠ 0})
    have hz : volume (⋃ h, bad h) = 0 := measure_iUnion_null (fun h => chart_null hm h hf)
    rw [ae_iff]
    apply measure_mono_null _ hz
    intro A hA
    change ¬(∀ x y, measureVector A (f x) = measureVector A (f y) → f x = f y) at hA
    push Not at hA
    obtain ⟨x,y,he,hne⟩ := hA
    obtain ⟨h,hd⟩ : ∃ h, (f x-f y) h ≠ 0 := by
      by_contra! hzero
      apply hne
      ext i
      exact sub_eq_zero.mp (hzero i)
    let B : Measurements m j := fun ik => A (ik.1,h.succAbove ik.2)
    refine Set.mem_iUnion.mpr ⟨h, _, ⟨((x,y),B), hd, rfl⟩, ?_⟩
    ext ⟨i,k⟩
    induction k using h.succAboveCases with
    | x =>
      simp only [chart, Fin.insertNth_apply_same, secants, B, Pi.sub_apply]
      apply (div_eq_iff (show f x h - f y h ≠ 0 from hd)).mpr
      have hk : (∑ k, A (i,k) * (f x k - f y k)) = 0 := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (congrFun he i)
      rw [Fin.sum_univ_succAbove _ h] at hk
      linarith
    | p k => simp [chart,secants,B]

end ReluMoments

namespace ReluMoments

/-- Scalar coordinates of feedforward affine/ReLU networks. Sharing a parameter
is represented by reusing its index. A weight times a previous coordinate and
addition realize each affine layer and bias, followed by the optional gate. -/
inductive Network (d p : ℕ) where
  | constant (r : ℝ)
  | input (i : Fin d)
  | parameter (i : Fin p)
  | add (f g : Network d p)
  | scale (i : Fin p) (f : Network d p)
  | relu (f : Network d p)

noncomputable def Network.eval {d p : ℕ} : Network d p → Vector p → Vector d → ℝ
  | .constant r, _, _ => r
  | .input i, _, x => x i
  | .parameter i, θ, _ => θ i
  | .add f g, θ, x => f.eval θ x + g.eval θ x
  | .scale i f, θ, x => θ i * f.eval θ x
  | .relu f, θ, x => max (f.eval θ x) 0

theorem Network.continuous_input {d p : ℕ} (f : Network d p) (θ : Vector p) : Continuous (f.eval θ) := by
  induction f with
  | constant _ | parameter _ => exact continuous_const
  | input i => exact continuous_apply i
  | add _ _ hf hg => exact hf.add hg
  | scale _ _ hf => exact continuous_const.mul hf
  | relu _ hf => exact hf.max continuous_const

/-- Bounded parameters give a common linear growth bound in the input and a
local parameter Lipschitz bound with the same integrable envelope. -/
theorem Network.envelope {d p : ℕ} (f : Network d p) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ : Vector p, ‖θ‖ ≤ R → ∀ x, |f.eval θ x| ≤ C*(1+‖x‖)) ∧
      (∀ θ η : Vector p, ‖θ‖ ≤ R → ‖η‖ ≤ R → ∀ x,
        |f.eval θ x-f.eval η x| ≤ C*(1+‖x‖)*‖θ-η‖) := by
  induction f with
  | constant c =>
    refine ⟨|c|,abs_nonneg _,fun θ _ x => ?_, fun θ η _ _ x => ?_⟩
    · change |c| ≤ |c| *(1+‖x‖)
      nlinarith only [mul_nonneg (abs_nonneg c) (norm_nonneg x)]
    · simp [Network.eval]; positivity
  | input i =>
    refine ⟨1,by norm_num,fun θ _ x => ?_,fun θ η _ _ x => ?_⟩
    · simpa only [Network.eval,one_mul,←Real.norm_eq_abs] using (norm_le_pi_norm x i).trans (by linarith : ‖x‖ ≤ 1+‖x‖)
    · simp [Network.eval]; positivity
  | parameter i =>
    refine ⟨R,by linarith,fun θ hθ x => ?_,fun θ η _ _ x => ?_⟩
    · change |θ i| ≤ _
      have h := (norm_le_pi_norm θ i).trans hθ
      rw [Real.norm_eq_abs] at h
      nlinarith only [h,mul_nonneg (show 0≤R by linarith) (norm_nonneg x)]
    · change |θ i - η i| ≤ _
      have h : |θ i-η i| ≤ ‖θ-η‖ := norm_le_pi_norm (θ-η) i
      apply h.trans
      have hc : 1 ≤ R*(1+‖x‖) := by nlinarith only [hR,mul_nonneg (show 0≤R by linarith) (norm_nonneg x)]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (θ-η))]
  | add f g hf hg =>
    obtain ⟨C,hC,hf0,hf1⟩ := hf
    obtain ⟨D,hD,hg0,hg1⟩ := hg
    refine ⟨C+D,add_nonneg hC hD,fun θ hθ x => ?_,fun θ η hθ hη x => ?_⟩
    · calc |f.eval θ x + g.eval θ x| ≤ _ := abs_add_le ..
           _ ≤ _ := by linarith only [hf0 θ hθ x, hg0 θ hθ x]
    · change |(_ + _) - (_ + _)| ≤ _
      rw [show f.eval θ x + g.eval θ x - (f.eval η x + g.eval η x) =
        (f.eval θ x-f.eval η x)+(g.eval θ x-g.eval η x) by ring]
      apply (abs_add_le ..).trans
      linarith only [hf1 θ η hθ hη x, hg1 θ η hθ hη x]
  | scale i f hf =>
    obtain ⟨C,hC,hf0,hf1⟩ := hf
    refine ⟨(R+1)*C,mul_nonneg (by linarith) hC,fun θ hθ x => ?_,fun θ η hθ hη x => ?_⟩
    · change |θ i * _| ≤ _
      rw [abs_mul]
      have hθ' : |θ i| ≤ R := (norm_le_pi_norm θ i).trans hθ
      have h := mul_le_mul hθ' (hf0 θ hθ x) (abs_nonneg _) (by linarith : 0≤R)
      nlinarith only [h,mul_nonneg hC (by positivity : 0≤1+‖x‖)]
    · change |θ i * f.eval θ x - η i * f.eval η x| ≤ _
      rw [show θ i * f.eval θ x - η i * f.eval η x =
        θ i*(f.eval θ x-f.eval η x) + (θ i-η i)*f.eval η x by ring]
      apply (abs_add_le ..).trans
      rw [abs_mul, abs_mul]
      have hθ' : |θ i| ≤ R := (norm_le_pi_norm θ i).trans hθ
      have hdiff : |θ i-η i| ≤ ‖θ-η‖ := norm_le_pi_norm (θ-η) i
      have h₁ := mul_le_mul hθ' (hf1 θ η hθ hη x) (abs_nonneg _) (by linarith : 0≤R)
      have h₂ := mul_le_mul hdiff (hf0 η hη x) (abs_nonneg _) (norm_nonneg _)
      linarith only [h₁,h₂]
  | relu f hf =>
    obtain ⟨C,hC,hf0,hf1⟩ := hf
    refine ⟨C,hC,fun θ hθ x => ?_,fun θ η hθ hη x => ?_⟩
    · apply le_trans _ (hf0 θ hθ x)
      change |max _ 0| ≤ _
      rw [abs_of_nonneg (le_max_right ..)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · exact (abs_max_sub_max_le_abs _ _ 0).trans (hf1 θ η hθ hη x)

end ReluMoments

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
