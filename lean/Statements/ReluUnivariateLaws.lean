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
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! Univariate product-Laplace and Gaussian identification and generic compression. -/

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

open Polynomial
open scoped Polynomial

namespace ReluMoments

/-- Two points lie in the same open interval of the complement of finitely many cuts. -/
def SameCell (s : Finset ℝ) (x y : ℝ) : Prop :=
  x ∉ s ∧ y ∉ s ∧ ∀ c ∈ s, (x < c ↔ y < c)

private theorem sign_uniform (s : Set ℝ) (g : ℝ → ℝ)
    (h : ∀ x ∈ s, ∀ y ∈ s, 0 ≤ g x * g y) :
    (∀ x ∈ s, 0 ≤ g x) ∨ (∀ x ∈ s, g x ≤ 0) := by
  by_cases hp : ∀ x ∈ s, 0 ≤ g x
  · exact .inl hp
  · push Not at hp
    obtain ⟨x,hx,hneg⟩ := hp
    refine .inr fun y hy => ?_
    by_contra! hh
    exact (not_lt_of_ge (h x hx y hy)) (mul_neg_of_neg_of_pos hneg hh)

/-- A function of constant weak sign on every complementary interval has a
sign-matching polynomial of degree at most twice the number of cuts. Its real
zero set is exactly the given cuts, including cuts where the sign is unchanged. -/
theorem exists_sign_polynomial (s : Finset ℝ) (g : ℝ → ℝ)
    (hs : ∀ x y, SameCell s x y → 0 ≤ g x * g y) :
    ∃ q : ℝ[X], q.natDegree ≤ 2*s.card ∧
      (∀ x, q.eval x = 0 ↔ x ∈ s) ∧ (∀ x, 0 ≤ q.eval x * g x) ∧
      ∀ x y, (∀ c ∈ s, c < x) → (∀ c ∈ s, c < y) → 0 ≤ q.eval x * q.eval y := by
  classical
  induction s using Finset.induction_on_max generalizing g with
  | empty =>
    rcases sign_uniform Set.univ g (fun x _ y _ => hs x y (by simp [SameCell])) with hp | hn
    · exact ⟨1,by simp,by simp,fun x => by simpa using hp x trivial,by simp⟩
    · exact ⟨-1,by simp,by simp,fun x => by simpa using hn x trivial,by simp⟩
  | insert c s hmax ih =>
    let left := fun x => if x < c then g x else 0
    have hleft (x y) (hxy : SameCell s x y) : 0 ≤ left x * left y := by
      by_cases hx : x < c <;> by_cases hy : y < c <;> simp [left,hx,hy]
      exact hs x y ⟨by simp [hx.ne,hxy.1],by simp [hy.ne,hxy.2.1],
        fun k hk => by rcases Finset.mem_insert.mp hk with rfl|hk; exact iff_of_true hx hy; exact hxy.2.2 k hk⟩
    obtain ⟨q,hd,hzero,hweak,htail⟩ := ih left hleft
    have hw x (hx : x < c) : 0 ≤ q.eval x * g x := by simpa [left,hx] using hweak x
    have ht (x y : ℝ) (hx : c < x) (hy : c < y) :
        0 ≤ (q.eval x*g x) * (q.eval y*g y) := by
      have hq := htail x y (fun k hk => (hmax k hk).trans hx) (fun k hk => (hmax k hk).trans hy)
      have hnot (t : ℝ) (ht : c < t) (k : ℝ) (hk : k ∈ insert c s) : k < t := by
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact ht
        · exact (hmax _ hk).trans ht
      have hg := hs x y ⟨fun h => (hnot _ hx _ h).false,fun h => (hnot _ hy _ h).false,
        fun k hk => iff_of_false (not_lt_of_ge (hnot _ hx _ hk).le) (not_lt_of_ge (hnot _ hy _ hk).le)⟩
      nlinarith only [mul_nonneg hq hg]
    have hc : c ∉ s := fun hc => (hmax c hc).false
    have hfactor : (X-C c : ℝ[X]).natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    have hfactor' : (C c-X : ℝ[X]).natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    rcases sign_uniform (Set.Ioi c) (fun x => q.eval x*g x) (fun x hx y hy => ht x y hx hy) with hp | hn
    · refine ⟨q * (X-C c)^2,?_,?_,?_,?_⟩
      · rw [Finset.card_insert_of_notMem hc]
        have hk := natDegree_pow_le (p := (X-C c : ℝ[X])) (n := 2)
        exact (natDegree_mul_le).trans (by omega)
      · intro x
        simp [hzero,sub_eq_zero,or_comm]
      · intro x
        have hmul : 0 ≤ (x-c)^2 := sq_nonneg _
        simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C]
        rcases lt_trichotomy x c with hx|rfl|hx
        · nlinarith only [mul_nonneg hmul (hw x hx)]
        · simp
        · nlinarith only [mul_nonneg hmul (hp x hx)]
      · intro x y hx hy
        have hq := htail x y (fun k hk => hx k (Finset.mem_insert_of_mem hk))
          (fun k hk => hy k (Finset.mem_insert_of_mem hk))
        simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C]
        nlinarith only [mul_nonneg hq (mul_nonneg (sq_nonneg (x-c)) (sq_nonneg (y-c)))]
    · refine ⟨q * (C c-X),?_,?_,?_,?_⟩
      · rw [Finset.card_insert_of_notMem hc]
        exact natDegree_mul_le.trans (by omega)
      · intro x
        simp [hzero,sub_eq_zero,or_comm,eq_comm]
      · intro x
        simp only [eval_mul,eval_sub,eval_X,eval_C]
        rcases lt_trichotomy x c with hx|rfl|hx
        · nlinarith only [mul_nonneg (sub_nonneg.mpr hx.le) (hw x hx)]
        · simp
        · nlinarith only [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx.le) (hn x hx)]
      · intro x y hx hy
        have hq := htail x y (fun k hk => hx k (Finset.mem_insert_of_mem hk))
          (fun k hk => hy k (Finset.mem_insert_of_mem hk))
        have hprod := mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (hx c (Finset.mem_insert_self _ _)).le)
          (sub_nonpos.mpr (hy c (Finset.mem_insert_self _ _)).le)
        simp only [eval_mul,eval_sub,eval_X,eval_C]
        nlinarith only [mul_nonneg hq hprod]

end ReluMoments

namespace ReluMoments

abbrev Line := ℝ × ℝ

def Line.value (l : Line) (x : ℝ) : ℝ := l.1*x+l.2

def Line.sub (l k : Line) : Line := (l.1-k.1,l.2-k.2)

def Line.zero : Line := (0,0)

noncomputable def lineRoot (l : Line) : ℝ := -l.2/l.1

theorem line_same_sign {s : Finset Line} {x y : ℝ} (h : SameCell (s.image lineRoot) x y)
    (l : Line) (hl : l ∈ s) : (0 ≤ l.value x ↔ 0 ≤ l.value y) := by
  by_cases hz : l.1 = 0
  · simp [Line.value,hz]
  have hm : lineRoot l ∈ s.image lineRoot := Finset.mem_image_of_mem _ hl
  have hx : x ≠ lineRoot l := fun e => h.1 (e ▸ hm)
  have hy : y ≠ lineRoot l := fun e => h.2.1 (e ▸ hm)
  have hxy := h.2.2 _ hm
  have heq (t : ℝ) : l.value t = l.1*(t-lineRoot l) := by
    simp only [Line.value,lineRoot]
    field_simp
    ring
  rw [heq,heq]
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simp only [mul_nonneg_iff,not_le_of_gt hneg,hneg.le,false_and,true_and,false_or,sub_nonpos]
    exact ⟨fun h => (hxy.mp (lt_of_le_of_ne h hx)).le,fun h => (hxy.mpr (lt_of_le_of_ne h hy)).le⟩
  · simp only [mul_nonneg_iff_of_pos_left hpos,sub_nonneg]
    exact ⟨fun h => le_of_not_gt (mt hxy.mpr (not_lt_of_ge h)),fun h => le_of_not_gt (mt hxy.mp (not_lt_of_ge h))⟩

end ReluMoments

namespace ReluMoments

/-- One affine form in the real input and all previous hidden coordinates. -/
structure GateAffine (n : ℕ) where
  direct : Line
  weight : Fin n → ℝ

noncomputable def GateAffine.eval {n : ℕ} (a : GateAffine n) (x : ℝ) (v : Fin n → ℝ) : ℝ :=
  a.direct.value x + ∑ i, a.weight i * v i

noncomputable def GateAffine.onLines {n : ℕ} (a : GateAffine n) (v : Fin n → Line) : Line :=
  (a.direct.1 + ∑ i, a.weight i * (v i).1,a.direct.2 + ∑ i, a.weight i * (v i).2)

theorem GateAffine.eval_onLines {n : ℕ} (a : GateAffine n) (v : Fin n → Line) (x : ℝ) :
    a.eval x (fun i => (v i).value x) = (a.onLines v).value x := by
  simp only [eval,onLines,Line.value,add_mul,Finset.sum_mul,mul_add,Finset.sum_add_distrib,mul_assoc]
  ring

/-- A feedforward computation in a topological order. One constructor adds exactly
one scalar ReLU; later gates may reuse its output any number of times. -/
inductive Circuit : ℕ → Type where
  | empty : Circuit 0
  | append {n : ℕ} (prev : Circuit n) (a : GateAffine n) : Circuit (n+1)

noncomputable def Circuit.values {n : ℕ} (b : Circuit n) (x : ℝ) : Fin n → ℝ :=
  match b with
  | .empty => Fin.elim0
  | .append b a => Fin.snoc (α:=fun _ => ℝ) (b.values x) (max (a.eval x (b.values x)) 0)

noncomputable def Circuit.maskLines {n : ℕ} (b : Circuit n) (σ : Fin n → Bool) : Fin n → Line :=
  match b with
  | .empty => Fin.elim0
  | @append k prev a =>
    let v := prev.maskLines (Fin.init σ)
    Fin.snoc (α:=fun _ => Line) v (if σ (Fin.last k) then a.onLines v else Line.zero)

noncomputable def Circuit.tests {n : ℕ} (b : Circuit n) : Finset Line :=
  match b with
  | .empty => ∅
  | @append k prev a => prev.tests ∪ Finset.univ.image (fun σ : Fin k → Bool => a.onLines (prev.maskLines σ))

theorem Circuit.card_tests {n : ℕ} (b : Circuit n) : b.tests.card + 1 ≤ 2^n := by
  induction b with
  | empty => simp [tests]
  | @append k prev a ih =>
    have h : (Finset.univ.image (fun σ : Fin k → Bool => a.onLines (prev.maskLines σ))).card ≤ 2^k := by
      simpa using (Finset.card_image_le (s:=Finset.univ) (f:=fun σ : Fin k → Bool => a.onLines (prev.maskLines σ)))
    have hu := Finset.card_union_le prev.tests (Finset.univ.image (fun σ : Fin k → Bool => a.onLines (prev.maskLines σ)))
    simp only [tests]
    rw [pow_succ]
    omega

def Circuit.realizesMaskAt {n : ℕ} (b : Circuit n) (σ : Fin n → Bool) (x : ℝ) : Prop :=
  ∀ i, b.values x i = (b.maskLines σ i).value x

theorem Circuit.append_mask {n : ℕ} (b : Circuit n) (a : GateAffine n)
    (σ : Fin n → Bool) (x : ℝ) (h : b.realizesMaskAt σ x) (active : Bool)
    (he : max ((a.onLines (b.maskLines σ)).value x) 0 =
      (if active then a.onLines (b.maskLines σ) else Line.zero).value x) :
    (b.append a).realizesMaskAt (Fin.snoc (α:=fun _ => Bool) σ active) x := by
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [values,maskLines,Fin.snoc_last,Fin.init_snoc]
    have hv : b.values x = fun i => (b.maskLines σ i).value x := funext h
    rw [hv,a.eval_onLines]
    exact he
  | cast i =>
    simpa only [values,maskLines,Fin.snoc_castSucc,Fin.init_snoc] using h i

theorem Circuit.common_mask {n : ℕ} (b : Circuit n) {x y : ℝ}
    (ht : ∀ l ∈ b.tests, 0 ≤ l.value x ↔ 0 ≤ l.value y) :
    ∃ σ, b.realizesMaskAt σ x ∧ b.realizesMaskAt σ y := by
  induction b with
  | empty => exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | @append k prev a ih =>
    obtain ⟨σ,hx,hy⟩ := ih (fun l hl => ht l (Finset.mem_union_left _ hl))
    let l := a.onLines (prev.maskLines σ)
    have hs : 0 ≤ l.value x ↔ 0 ≤ l.value y := ht l
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ σ)))
    by_cases hp : 0 ≤ l.value x
    · exact ⟨Fin.snoc σ true,prev.append_mask a σ x hx true (max_eq_left hp),
        prev.append_mask a σ y hy true (max_eq_left (hs.mp hp))⟩
    · refine ⟨Fin.snoc σ false,prev.append_mask a σ x hx false ?_,prev.append_mask a σ y hy false ?_⟩
      · rw [max_eq_right (le_of_not_ge hp)]; simp [Line.zero,Line.value]
      · rw [max_eq_right (le_of_not_ge (mt hs.mpr hp))]; simp [Line.zero,Line.value]

noncomputable def Circuit.out {n : ℕ} (b : Circuit n) (a : GateAffine n) (x : ℝ) : ℝ :=
  a.eval x (b.values x)

theorem Circuit.out_on_mask {n : ℕ} (b : Circuit n) (a : GateAffine n)
    {σ : Fin n → Bool} {x : ℝ} (h : b.realizesMaskAt σ x) :
    b.out a x = (a.onLines (b.maskLines σ)).value x := by
  have hh : b.values x = fun i => (b.maskLines σ i).value x := funext h
  rw [out,hh,a.eval_onLines]

/-- The cut count is uniform in all real weights and counts shared gates once. -/
theorem Circuit.sign_cuts {n m : ℕ} (b : Circuit n) (c : Circuit m) (a : GateAffine n) (a' : GateAffine m) :
    ∃ s : Finset ℝ, s.card ≤ 2^n + 2^m + 2^n*2^m ∧
      ∀ x y, SameCell s x y → 0 ≤ (b.out a x - c.out a' x) * (b.out a y - c.out a' y) := by
  let l (σ : Fin n → Bool) := a.onLines (b.maskLines σ)
  let l' (τ : Fin m → Bool) := a'.onLines (c.maskLines τ)
  let diffs := Finset.image₂ (fun σ τ => (l σ).sub (l' τ)) Finset.univ Finset.univ
  let all := b.tests ∪ c.tests ∪ diffs
  refine ⟨all.image lineRoot,Finset.card_image_le.trans ?_,?_⟩
  · have hdiff : diffs.card ≤ 2^n * 2^m := by simpa [diffs] using
        (Finset.card_image₂_le (fun σ τ => (l σ).sub (l' τ)) Finset.univ Finset.univ)
    exact (Finset.card_union_le ..).trans (Nat.add_le_add ((Finset.card_union_le ..).trans
      (Nat.add_le_add ((Nat.le_succ _).trans b.card_tests) ((Nat.le_succ _).trans c.card_tests))) hdiff)
  · intro x y hxy
    obtain ⟨σ,hx,hy⟩ := b.common_mask (fun l hl => line_same_sign hxy l
      (Finset.mem_union_left _ (Finset.mem_union_left _ hl)))
    obtain ⟨τ,hx',hy'⟩ := c.common_mask (fun l hl => line_same_sign hxy l
      (Finset.mem_union_left _ (Finset.mem_union_right _ hl)))
    have hd := line_same_sign hxy ((l σ).sub (l' τ)) (Finset.mem_union_right _
      (Finset.mem_image₂_of_mem (Finset.mem_univ σ) (Finset.mem_univ τ)))
    have hval (z : ℝ) : ((l σ).sub (l' τ)).value z = (l σ).value z - (l' τ).value z := by
      simp [Line.value,Line.sub]; ring
    rw [hval,hval,←b.out_on_mask a hx,←c.out_on_mask a' hx',←b.out_on_mask a hy,←c.out_on_mask a' hy'] at hd
    by_cases h : 0 ≤ b.out a x - c.out a' x
    · exact mul_nonneg h (hd.mp h)
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h) (le_of_not_ge (mt hd.mpr h))

end ReluMoments

open MeasureTheory Polynomial
open scoped Polynomial

namespace ReluMoments

/-- Ordinary monomial moments through twice the number of sign cuts determine
a continuous function with these sign cuts under any full-support input law. -/
theorem zero_of_moments (μ : Measure ℝ) [μ.IsOpenPosMeasure] (g : ℝ → ℝ) (hg : Continuous g)
    (s : Finset ℝ) (hs : ∀ x y, SameCell s x y → 0 ≤ g x*g y)
    (hi : ∀ k ≤ 2*s.card, Integrable (fun x => x^k * g x) μ)
    (hz : ∀ k ≤ 2*s.card, ∫ x, x^k * g x ∂μ = 0) : g = 0 := by
  classical
  obtain ⟨q,hd,hroots,hpos,_⟩ := exists_sign_polynomial s g hs
  let v (k : ℕ) (x : ℝ) := q.coeff k * (x^k * g x)
  let indices := Finset.range (q.natDegree+1)
  have hki (k) (hk : k ∈ indices) : k ≤ 2*s.card := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hd
  have hvi (k) (hk : k ∈ indices) : Integrable (v k) μ := (hi k (hki k hk)).const_mul _
  have heq (x : ℝ) : q.eval x * g x = ∑ k ∈ indices, v k x := by
    simp only [indices,v,q.eval_eq_sum_range x,Finset.sum_mul,mul_assoc]
  have hqi : Integrable (fun x => q.eval x * g x) μ := by
    simp_rw [heq]
    exact integrable_finsetSum _ hvi
  have hqz : (∫ x, q.eval x * g x ∂μ) = 0 := by
    simp_rw [heq]
    rw [integral_finsetSum _ hvi]
    apply Finset.sum_eq_zero
    intro k hk
    rw [show (∫ x, v k x ∂μ) = q.coeff k * ∫ x, x^k * g x ∂μ from integral_const_mul _ _,hz k (hki k hk),mul_zero]
  have hall (x : ℝ) : q.eval x * g x = 0 := by
    by_contra hne
    have h := integral_pos_of_integrable_nonneg_nonzero (q.continuous.mul hg) hqi hpos hne
    exact (ne_of_gt h) hqz
  apply Continuous.ext_on (dense_univ.sdiff_finset s) hg continuous_const
  intro x hx
  exact (mul_eq_zero.mp (hall x)).resolve_left (fun h => hx.2 ((hroots x).mp h))

end ReluMoments

open MeasureTheory

namespace ReluMoments

theorem GateAffine.continuous_eval {n : ℕ} (a : GateAffine n) {v : ℝ → Fin n → ℝ}
    (hv : ∀ i, Continuous (fun x => v x i)) : Continuous fun x => a.eval x (v x) := by
  unfold GateAffine.eval Line.value
  fun_prop (disch := solve_by_elim)

theorem Circuit.continuous_values {n : ℕ} (b : Circuit n) :
    ∀ i, Continuous (fun x => b.values x i) := by
  induction b with
  | empty => exact fun i => i.elim0
  | append prev a ih =>
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [values,Fin.snoc_last] using (a.continuous_eval ih).max continuous_const
    | cast i => simpa only [values,Fin.snoc_castSucc] using ih i

theorem Circuit.continuous_out {n : ℕ} (b : Circuit n) (a : GateAffine n) : Continuous (b.out a) :=
  a.continuous_eval b.continuous_values

theorem Circuit.integrable_out {n : ℕ} (b : Circuit n) (a : GateAffine n) (μ : Measure ℝ) (k : ℕ)
    (hi : Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ) :
    Integrable (fun x => x^k * b.out a x) μ := by
  let coeff (σ : Fin n → Bool) := |(a.onLines (b.maskLines σ)).1| + |(a.onLines (b.maskLines σ)).2|
  let C := ∑ σ, coeff σ
  have hh (x : ℝ) : |b.out a x| ≤ C*(1+|x|) := by
    obtain ⟨σ,hx,_⟩ := b.common_mask (x:=x) (y:=x) (fun _ _ => Iff.rfl)
    rw [b.out_on_mask a hx]
    have hle : coeff σ ≤ C := Finset.single_le_sum (f:=coeff) (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ σ)
    let l := a.onLines (b.maskLines σ)
    change |l.1*x+l.2| ≤ _
    apply (abs_add_le ..).trans
    rw [abs_mul]
    calc _ ≤ (|l.1|+|l.2|)*(1+|x|) := by nlinarith only [abs_nonneg l.1,mul_nonneg (abs_nonneg l.2) (abs_nonneg x)]
         _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
  apply (hi.const_mul C).mono' ((continuous_id.pow k).mul (b.continuous_out a)).aestronglyMeasurable
  filter_upwards with x
  change |x^k*b.out a x| ≤ _
  rw [abs_mul,abs_pow]
  calc _ ≤ |x|^k*(C*(1+|x|)) := mul_le_mul_of_nonneg_left (hh x) (by positivity)
       _ = _ := by ring

theorem circuit_identification {n m : ℕ} (b : Circuit n) (c : Circuit m) (a : GateAffine n) (a' : GateAffine m)
    (μ : Measure ℝ) [μ.IsOpenPosMeasure] (D : ℕ) (hD : 2*(2^n+2^m+2^n*2^m) ≤ D)
    (hi : ∀ k ≤ D, Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ) :
    (∀ k ≤ D, (∫ x, x^k*b.out a x ∂μ) = ∫ x, x^k*c.out a' x ∂μ) ↔ b.out a = c.out a' := by
  constructor
  · intro h
    obtain ⟨s,hc,hs⟩ := b.sign_cuts c a a'
    have hki (k) (hk : k ≤ 2*s.card) : k ≤ D := by omega
    have hd (k) (hk : k ≤ 2*s.card) : Integrable (fun x => x^k * (b.out a x - c.out a' x)) μ := by
      simp_rw [mul_sub]
      exact (b.integrable_out a μ k (hi k (hki k hk))).sub (c.integrable_out a' μ k (hi k (hki k hk)))
    have hz (k) (hk : k ≤ 2*s.card) : ∫ x, x^k * (b.out a x - c.out a' x) ∂μ = 0 := by
      simp_rw [mul_sub]
      rw [integral_sub (b.integrable_out a μ k (hi k (hki k hk))) (c.integrable_out a' μ k (hi k (hki k hk)))]
      exact sub_eq_zero.mpr (h _ (hki _ hk))
    have hr := zero_of_moments μ _ ((b.continuous_out a).sub (c.continuous_out a')) s hs hd hz
    funext x
    exact sub_eq_zero.mp (congrFun hr x)
  · intro he k _
    rw [he]

def faceBound (h : ℕ) : ℕ := 4^(2*h+1)
def laplaceDegree (h : ℕ) : ℕ := let N := faceBound h; N*(2*N+1)-1
def gaussianDegree (h : ℕ) : ℕ := let S := 2*faceBound h; S*(S-1)/2+S-1

theorem display_degrees {n m h : ℕ} (hn : n ≤ h) (hm : m ≤ h) :
    2*(2^n+2^m+2^n*2^m) ≤ laplaceDegree h ∧ 2*(2^n+2^m+2^n*2^m) ≤ gaussianDegree h := by
  let t : ℕ := 4^h
  let N := faceBound h
  have h1 : 1 ≤ t := Nat.one_le_pow _ _ (by decide)
  have hbase : 2^h ≤ t := Nat.pow_le_pow_left (by decide) _
  have hₙ := (Nat.pow_le_pow_right (by decide : 0 < 2) hn).trans hbase
  have hₘ := (Nat.pow_le_pow_right (by decide : 0 < 2) hm).trans hbase
  have hN : N = 4*t*t := by simp [N,faceBound,t,pow_succ,Nat.mul_comm 2 h,pow_mul]; ring
  have hNN : 0 < N := by dsimp [N,faceBound]; positivity
  have hc : 2^n+2^m+2^n*2^m ≤ N := by
    rw [hN]
    nlinarith only [hₙ,hₘ,Nat.mul_le_mul hₙ hₘ,Nat.mul_le_mul h1 h1,Nat.mul_le_mul_left t h1]
  change _ ≤ N*(2*N+1)-1 ∧ _ ≤ (2*N)*(2*N-1)/2+2*N-1
  have hp : 2 ≤ (2*N)*(2*N-1) := by
    have h2 : 1 ≤ 2*N-1 := by omega
    nlinarith only [Nat.mul_le_mul (show 2 ≤ 2*N by omega) h2]
  have hq : 1 ≤ (2*N)*(2*N-1)/2 := by omega
  have hr : 2*N+1 ≤ N*(2*N+1) := by nlinarith only [Nat.mul_le_mul_right (2*N+1) (show 1≤N by omega)]
  omega

end ReluMoments

namespace ReluMoments

/-- Optional weight indices allow arbitrary sparse or fully connected
architectures. Repeated indices denote shared parameters. -/
structure IndexedAffine (n p : ℕ) where
  input : Option (Fin p)
  bias : Option (Fin p)
  weight : Fin n → Option (Fin p)

def IndexedAffine.coeff {p : ℕ} (θ : Vector p) (i : Option (Fin p)) : ℝ :=
  i.elim 0 θ

noncomputable def IndexedAffine.instantiate {n p : ℕ} (a : IndexedAffine n p) (θ : Vector p) : GateAffine n :=
  ⟨(coeff θ a.input,coeff θ a.bias),fun i => coeff θ (a.weight i)⟩

def weightExpr {p : ℕ} (i : Option (Fin p)) (f : Network 1 p) : Network 1 p :=
  i.elim (.constant 0) (fun k => .scale k f)

theorem weightExpr_eval {p : ℕ} (i : Option (Fin p)) (f : Network 1 p) (θ : Vector p) (x : ℝ) :
    (weightExpr i f).eval θ (fun _ => x) = IndexedAffine.coeff θ i * f.eval θ (fun _ => x) := by
  cases i <;> simp [weightExpr,IndexedAffine.coeff,Network.eval]

def sumExpr {p : ℕ} : {n : ℕ} → (Fin n → Network 1 p) → Network 1 p
  | 0, _ => .constant 0
  | n+1, f => (sumExpr (Fin.init f)).add (f (Fin.last n))

theorem sumExpr_eval {p n : ℕ} (f : Fin n → Network 1 p) (θ : Vector p) (x : ℝ) :
    (sumExpr f).eval θ (fun _ => x) = ∑ i, (f i).eval θ (fun _ => x) := by
  induction n with
  | zero => simp [sumExpr,Network.eval]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,sumExpr,Network.eval,ih]
    rfl

def IndexedAffine.makeExpr {n p : ℕ} (a : IndexedAffine n p) (v : Fin n → Network 1 p) : Network 1 p :=
  ((weightExpr a.input (.input 0)).add (a.bias.elim (.constant 0) .parameter)).add
    (sumExpr (fun i => weightExpr (a.weight i) (v i)))

theorem IndexedAffine.makeExpr_eval {n p : ℕ} (a : IndexedAffine n p) (v : Fin n → Network 1 p) (θ : Vector p) (x : ℝ) :
    (a.makeExpr v).eval θ (fun _ => x) = (a.instantiate θ).eval x (fun i => (v i).eval θ (fun _ => x)) := by
  simp only [makeExpr,Network.eval,weightExpr_eval,sumExpr_eval,GateAffine.eval,instantiate,Line.value]
  cases a.bias <;> rfl

inductive IndexedCircuit (p : ℕ) : ℕ → Type where
  | empty : IndexedCircuit p 0
  | append {n : ℕ} (prev : IndexedCircuit p n) (a : IndexedAffine n p) : IndexedCircuit p (n+1)

noncomputable def IndexedCircuit.instantiate {n p : ℕ} (b : IndexedCircuit p n) (θ : Vector p) : Circuit n :=
  match b with
  | .empty => .empty
  | .append prev a => .append (prev.instantiate θ) (a.instantiate θ)

def IndexedCircuit.exprs {n p : ℕ} (b : IndexedCircuit p n) : Fin n → Network 1 p :=
  match b with
  | .empty => Fin.elim0
  | .append prev a => Fin.snoc (α:=fun _ => Network 1 p) prev.exprs (.relu (a.makeExpr prev.exprs))

theorem IndexedCircuit.eval_exprs {p n : ℕ} (b : IndexedCircuit p n) (θ : Vector p) (x : ℝ) :
    ∀ i, (b.exprs i).eval θ (fun _ => x) = (b.instantiate θ).values x i := by
  induction b with
  | empty => exact fun i => i.elim0
  | append prev a ih =>
    intro i
    induction i using Fin.lastCases with
    | cast i => simpa only [exprs,instantiate,Circuit.values,Fin.snoc_castSucc] using ih i
    | last =>
      simp only [exprs,instantiate,Circuit.values,Fin.snoc_last,Network.eval,a.makeExpr_eval]
      rw [show (fun i => (prev.exprs i).eval θ (fun _ => x)) = _ from funext ih]

theorem IndexedCircuit.eval_output {p n : ℕ} (b : IndexedCircuit p n) (a : IndexedAffine n p) (θ : Vector p) (x : ℝ) :
    (a.makeExpr b.exprs).eval θ (fun _ => x) = (b.instantiate θ).out (a.instantiate θ) x := by
  rw [a.makeExpr_eval,Circuit.out,show (fun i => (b.exprs i).eval θ (fun _ => x)) = _ from funext (b.eval_exprs θ x)]

end ReluMoments

open MeasureTheory
open scoped Topology

namespace ReluMoments

noncomputable def polynomialObservations {p n m : ℕ} (b : IndexedCircuit p n) (a : IndexedAffine n p)
    (μ : Measure ℝ) (D : ℕ) (A : Measurements m (D+1)) (θ : Vector p) : Vector m :=
  fun i => ∫ x, (∑ k : Fin (D+1), A (i,k)*x^k.val) * (b.instantiate θ).out (a.instantiate θ) x ∂μ

/-- Almost every fixed list of 2P+1 polynomial measurements identifies every
realized function of a shared, P-parameter architecture on the real line. -/
theorem circuit_compression {p n : ℕ} (b : IndexedCircuit p n) (a : IndexedAffine n p)
    (μ : Measure ℝ) [μ.IsOpenPosMeasure] (D : ℕ) (hD : 2*(2^n+2^n+2^n*2^n) ≤ D)
    (hi : ∀ k ≤ D, Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ) :
    ∀ᵐ A : Measurements (2*p+1) (D+1) ∂volume, ∀ θ η,
      polynomialObservations b a μ D A θ = polynomialObservations b a μ D A η ↔
        (b.instantiate θ).out (a.instantiate θ) = (b.instantiate η).out (a.instantiate η) := by
  let e : ℝ → Vector 1 := fun x _ => x
  have he : Continuous e := continuous_pi fun _ => continuous_id
  let ν := μ.map e
  let t (k : Fin (D+1)) (z : Vector 1) := z 0 ^ k.val
  let f := a.makeExpr b.exprs
  have ht (k) : Continuous (t k) := (continuous_apply 0).pow _
  have hwt (k : Fin (D+1)) : Integrable (fun z => |t k z| * (1+‖z‖)) ν := by
    apply (integrable_map_measure ((ht k).abs.mul (continuous_const.add continuous_norm)).aestronglyMeasurable
      he.aemeasurable).mpr
    change Integrable (fun x : ℝ => |x^k.val| * (1+‖fun _ : Fin 1 => x‖)) μ
    simpa only [abs_pow,pi_norm_const,Real.norm_eq_abs] using hi k.val (by omega)
  have hc := network_compression (m:=2*p+1) (by omega) f ν t
    (fun k => (ht k).aestronglyMeasurable) hwt
  have hu (θ : Vector p) (k : Fin (D+1)) : moments f ν t θ k =
      ∫ x, x^k.val * (b.instantiate θ).out (a.instantiate θ) x ∂μ := by
    rw [moments,show ν = μ.map e from rfl,integral_map (f:=fun z => t k z * f.eval θ z) he.aemeasurable ((ht k).mul (f.continuous_input θ)).aestronglyMeasurable]
    simp only [e,t,f,b.eval_output]
  have hm (A : Measurements (2*p+1) (D+1)) (θ : Vector p) :
      measureVector A (moments f ν t θ) = polynomialObservations b a μ D A θ := by
    funext i
    rw [measurement_integral f ν t (fun k => (ht k).aestronglyMeasurable) hwt]
    have hw : Continuous (fun z => (∑ k, A (i,k) * t k z)*f.eval θ z) := by
      apply Continuous.mul _ (f.continuous_input θ)
      fun_prop (disch := solve_by_elim)
    rw [show ν = μ.map e from rfl,integral_map he.aemeasurable hw.aestronglyMeasurable]
    simp only [polynomialObservations,e,t,f,b.eval_output]
  filter_upwards [hc] with A hA
  intro θ η
  rw [←hm,←hm,hA]
  constructor
  · intro hh
    apply (circuit_identification _ _ _ _ μ D hD hi).mp
    intro k hk
    let i : Fin (D+1) := ⟨k,by omega⟩
    simpa only [hu] using congrFun hh i
  · intro hh
    funext k
    rw [hu,hu,hh]

end ReluMoments

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

open MeasureTheory ProbabilityTheory

namespace ReluMoments

/-- For any two scalar real-input feedforward networks with at most h hidden
gates each, the draft's two displayed lists of ordinary moments both determine
the realized function everywhere, separately for their respective laws. -/
theorem univariate_laws {n m h : ℕ} (hn : n ≤ h) (hm : m ≤ h)
    (b : Circuit n) (c : Circuit m) (a : GateAffine n) (a' : GateAffine m) :
    ((∀ k ≤ laplaceDegree h, (∫ x, x^k*b.out a x ∂standardLaplace) =
      ∫ x, x^k*c.out a' x ∂standardLaplace) ↔ b.out a = c.out a') ∧
    ((∀ k ≤ gaussianDegree h, (∫ x, x^k*b.out a x ∂(gaussianReal 0 1)) =
      ∫ x, x^k*c.out a' x ∂(gaussianReal 0 1)) ↔ b.out a = c.out a') := by
  let : (gaussianReal 0 1).IsOpenPosMeasure := gaussian_open _ one_ne_zero
  exact ⟨circuit_identification b c a a' _ _ (display_degrees hn hm).1 (fun k _ => laplace_envelope k),
    circuit_identification b c a a' _ _ (display_degrees hn hm).2 (fun k _ => gaussian_envelope _ _ k)⟩

/-- Each law separately admits almost every fixed list of 2P+1 polynomial
tests from the corresponding displayed degree range, uniformly in all
parameters and with pointwise agreement on the entire real line. -/
theorem univariate_compressed_laws {p h : ℕ} (b : IndexedCircuit p h) (a : IndexedAffine h p) :
    (∀ᵐ A : Measurements (2*p+1) (laplaceDegree h+1) ∂volume, ∀ θ η,
      polynomialObservations b a standardLaplace (laplaceDegree h) A θ =
        polynomialObservations b a standardLaplace (laplaceDegree h) A η ↔
      (b.instantiate θ).out (a.instantiate θ) = (b.instantiate η).out (a.instantiate η)) ∧
    (∀ᵐ A : Measurements (2*p+1) (gaussianDegree h+1) ∂volume, ∀ θ η,
      polynomialObservations b a (gaussianReal 0 1) (gaussianDegree h) A θ =
        polynomialObservations b a (gaussianReal 0 1) (gaussianDegree h) A η ↔
      (b.instantiate θ).out (a.instantiate θ) = (b.instantiate η).out (a.instantiate η)) := by
  let : (gaussianReal 0 1).IsOpenPosMeasure := gaussian_open _ one_ne_zero
  have hdeg := display_degrees (n:=h) (m:=h) (h:=h) le_rfl le_rfl
  exact ⟨circuit_compression b a _ _ hdeg.1 (fun k _ => laplace_envelope k),
    circuit_compression b a _ _ hdeg.2 (fun k _ => gaussian_envelope _ _ k)⟩

end ReluMoments
