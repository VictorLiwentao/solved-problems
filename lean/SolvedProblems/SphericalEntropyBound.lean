module

public import SolvedProblems.SphericalEntropyDesign

@[expose] public section

open Finset MeasureTheory
open scoped RealInnerProductSpace

namespace SphericalEntropy

theorem design_potential {s N t} {α : ℝ} (ha : 0≤α) (X : Fin (N+1) → Sphere s) (hd : IsDesign t X)
    (x : Sphere s) :
    |averageKernel α X x - 1| ≤
      2*(α^(t+1)/((t+1).factorial:ℝ)*Real.exp α)/partition α x := by
  let k := t+1
  let P (y : Sphere s) := taylor k (α*⟪x.val,y.val⟫)
  let err := α^k/(k.factorial:ℝ)*Real.exp α
  have hex : mean (fun i => P (X i)) = ∫ y, P y ∂(surface s) := by
    simpa [taylorPolynomial_eval,P,k] using hd (taylorPolynomial k α x) (taylorPolynomial_degree t α x)
  have he (y : Sphere s) : |kernel α x y - P y|≤err := by
    apply taylor_error
    rw [abs_mul,abs_of_nonneg ha]
    exact mul_le_of_le_one_right ha (inner_bound x y)
  have hmc := abs_mean_le fun i => he (X i)
  rw [mean_sub,hex] at hmc
  have hcont : Continuous P := by unfold P taylor; fun_prop
  have hk := (kernel_continuous α x).integrable_of_hasCompactSupport (μ:=surface s) (HasCompactSupport.of_compactSpace _)
  have hp := hcont.integrable_of_hasCompactSupport (μ:=surface s) (HasCompactSupport.of_compactSpace _)
  have hi := norm_integral_le_of_norm_le_const (μ:=surface s) (f:=fun y => kernel α x y-P y) (Filter.Eventually.of_forall fun y =>
    (show ‖kernel α x y-P y‖≤err by simpa [Real.norm_eq_abs] using he y))
  rw [integral_sub hk hp,Real.norm_eq_abs,(show (surface s).real Set.univ=1 by simp),mul_one,abs_sub_comm] at hi
  have hpair := abs_sub_le (mean fun i => kernel α x (X i)) (∫ y, P y ∂surface s) (partition α x)
  have ht : |(mean fun i => kernel α x (X i))-partition α x|≤2*err := by
    unfold partition at hpair ⊢
    linarith
  unfold averageKernel
  rw [div_sub_one (partition_pos _ _).ne',abs_div,abs_of_pos (partition_pos _ _)]
  exact div_le_div_of_nonneg_right ht (partition_pos _ _).le

/-- The simultaneous factorial upper bound on the empirical quadratic and
cross-entropy gaps of any actual equal-weight spherical design. -/
theorem design_gaps {s N t} {α : ℝ} (ha : 0≤α) (X : Fin (N+1) → Sphere s) (hd : IsDesign t X)
    (x : Sphere s) :
    lossGap α X ≤ energyGap α X ∧
      |energyGap α X| ≤ 2*(α^(t+1)/((t+1).factorial:ℝ)*Real.exp α)/partition α x := by
  refine ⟨loss_le_energy ..,?_⟩
  have h := abs_mean_le fun i => (design_potential ha X hd (X i)).trans_eq (by rw [partition_invariant α (X i) x])
  simpa [energyGap,mean_sub] using h

end SphericalEntropy
