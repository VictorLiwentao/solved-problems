module

public import SolvedProblems.SphericalEntropySurface
public import SolvedProblems.SphericalEntropyTaylor
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

open Finset MeasureTheory
open scoped RealInnerProductSpace

namespace SphericalEntropy

noncomputable def mean {N : ℕ} (v : Fin (N+1) → ℝ) := (N+1:ℝ)⁻¹ * ∑ i, v i

@[simp] theorem mean_const (N : ℕ) (a : ℝ) : mean (fun _ : Fin (N+1) => a) = a := by
  simp [mean,←mul_assoc,inv_mul_cancel₀ (show (N+1:ℝ)≠0 by positivity)]

theorem mean_mono {N : ℕ} {f g : Fin (N+1) → ℝ} (h : ∀ i, f i≤g i) : mean f≤mean g :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => h i) (by positivity)

theorem mean_sub {N : ℕ} (f g : Fin (N+1) → ℝ) : mean (fun i => f i-g i) = mean f - mean g := by
  simp [mean,sum_sub_distrib,mul_sub]

theorem abs_mean_le {N : ℕ} {f : Fin (N+1) → ℝ} {a : ℝ} (h : ∀ i, |f i|≤a) : |mean f|≤a := by
  apply abs_le.mpr
  constructor
  · simpa using (mean_mono fun i => (abs_le.mp (h i)).1)
  · simpa using (mean_mono fun i => (abs_le.mp (h i)).2)

noncomputable def averageKernel {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) (x : Sphere s) : ℝ :=
  mean (fun i => kernel α x (X i)) / partition α x

noncomputable def energyGap {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) : ℝ :=
  mean (fun i => averageKernel α X (X i)) - 1

noncomputable def lossGap {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) : ℝ :=
  mean (fun i => Real.log (averageKernel α X (X i)))

theorem averageKernel_pos {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) (x) : 0<averageKernel α X x := by
  unfold averageKernel mean
  apply div_pos _ (partition_pos _ _)
  apply mul_pos (by positivity)
  exact sum_pos (fun i _ => Real.exp_pos _) univ_nonempty

/-- The tangent line to log at one bounds tied cross-entropy by its quadratic pair energy. -/
theorem loss_le_energy {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) : lossGap α X ≤ energyGap α X := by
  have h := mean_mono fun i => Real.log_le_sub_one_of_pos (averageKernel_pos α X (X i))
  simpa [lossGap,energyGap,mean_sub] using h

/-- Equal-weight nodes integrate every ambient polynomial of degree at most t
exactly against normalized spherical surface measure. -/
def IsDesign {s N} (t : ℕ) (X : Fin (N+1) → Sphere s) : Prop :=
  ∀ p : MvPolynomial (Fin (s+1)) ℝ, p.totalDegree≤t →
    mean (fun i => MvPolynomial.eval (X i).val p) =
      ∫ y : Sphere s, MvPolynomial.eval y.val p ∂(surface s)

noncomputable def dotPolynomial {s} (α : ℝ) (x : Sphere s) : MvPolynomial (Fin (s+1)) ℝ :=
  ∑ i, MvPolynomial.C (α*x.val i)*MvPolynomial.X i

theorem dotPolynomial_degree {s} (α : ℝ) (x : Sphere s) : (dotPolynomial α x).totalDegree≤1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X])

theorem dotPolynomial_eval {s} (α : ℝ) (x y : Sphere s) :
    MvPolynomial.eval y.val (dotPolynomial α x) = α*⟪x.val,y.val⟫ := by
  simp [dotPolynomial,PiLp.inner_apply,mul_sum,mul_assoc,mul_comm (x.val _) (y.val _)]

noncomputable def taylorPolynomial {s} (k : ℕ) (α : ℝ) (x : Sphere s) : MvPolynomial (Fin (s+1)) ℝ :=
  ∑ j ∈ range k, MvPolynomial.C ((j.factorial:ℝ)⁻¹) * (dotPolynomial α x)^j

theorem taylorPolynomial_degree {s} (t : ℕ) (α : ℝ) (x : Sphere s) :
    (taylorPolynomial (t+1) α x).totalDegree ≤ t := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  exact (MvPolynomial.totalDegree_pow ..).trans ((Nat.mul_le_mul_left j (dotPolynomial_degree α x)).trans (by simpa using Nat.le_of_lt_succ (mem_range.mp hj)))

theorem taylorPolynomial_eval {s} (k : ℕ) (α : ℝ) (x y : Sphere s) :
    MvPolynomial.eval y.val (taylorPolynomial k α x) = taylor k (α*⟪x.val,y.val⟫) := by
  simp [taylorPolynomial,taylor,dotPolynomial_eval,div_eq_inv_mul]

end SphericalEntropy
