module

public import SolvedProblems.ReluVectors
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Tactic.Linarith

@[expose] public section

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
