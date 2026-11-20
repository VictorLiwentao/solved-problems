module

public import SolvedProblems.FussRootCoefficients
public import SolvedProblems.FussPolynomialModel
public import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Tactic.Linarith

@[expose] public section

namespace FussDyck

open Polynomial
open scoped Polynomial

/-- Each differentiation preserves containment of the zero set in a fixed convex set,
as long as the differentiated polynomial has positive degree. -/
private theorem iterated_roots (S : Set ℂ) (hS : Convex ℝ S) (d : ℕ) :
    ∀ (p : ℂ[X]), p ≠ 0 → d ≤ p.natDegree → p.rootSet ℂ ⊆ S →
      ∀ w, (derivative^[d] p).eval w = 0 → w ∈ S := by
  induction d with
  | zero =>
    intro p hp _ hr w hw
    apply hr
    exact mem_rootSet.mpr ⟨hp, by simpa [coe_aeval_eq_eval] using hw⟩
  | succ d ih =>
    intro p _ hd hr w hw
    have hd' : 0 < p.natDegree := by omega
    rw [Function.iterate_succ_apply] at hw
    apply ih p.derivative (derivative_ne_zero.mpr hd'.ne') (by simp; omega) _ w hw
    exact (rootSet_derivative_subset_convexHull_rootSet (P := p)
      (natDegree_pos_iff_degree_pos.mp hd')).trans (convexHull_min hr hS)

/-- The segment between the two auxiliary roots can contain zero only when the
variable parameter is itself real and nonpositive. -/
private theorem zero_on_segment {z : ℂ} (hz : 0 ∈ segment ℝ (-z) (-1 : ℂ)) :
    z.im = 0 ∧ z.re ≤ 0 := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := hz
  have hre := congrArg Complex.re he
  have him : a = 0 ∨ z.im = 0 := by simpa using congrArg Complex.im he
  simp at hre
  have ha' : 0 < a := by
    apply lt_of_le_of_ne ha
    intro ha0
    subst a
    simp at hre hab
    linarith
  constructor
  · exact him.resolve_left ha'.ne'
  · by_contra! h
    nlinarith [mul_pos ha' h]

/-- Every complex root of the explicit fixed-peak factor lies on the nonpositive
real axis, including parameter choices with just one peak or no excess steps. -/
theorem shape_roots {k s : ℕ} (hk : 0 < k) {z : ℂ} (hz : (shapePoly k s).IsRoot z) :
    z.im = 0 ∧ z.re ≤ 0 := by
  change (shapePoly k s).eval z = 0 at hz
  simp only [shapePoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at hz
  by_cases hs : s = 0
  · subst s
    simp [hCoeff, Finset.sum_ite_eq'] at hz
  have hs' : 0 < s := Nat.pos_of_ne_zero hs
  let p : ℂ[X] := (X+1)^(s-1) * (X+C z)^k
  have f : (X+1 : ℂ[X]) ≠ 0 := by simpa using (X_add_C_ne_zero (1:ℂ))
  have g : (X+C z : ℂ[X]) ≠ 0 := X_add_C_ne_zero z
  have pn : p ≠ 0 := mul_ne_zero (pow_ne_zero _ f) (pow_ne_zero _ g)
  have pd : p.natDegree = s-1+k := by
    simp [p, natDegree_mul (pow_ne_zero _ f) (pow_ne_zero _ g), natDegree_pow]
  have coeff : p.coeff (k-1) = 0 := (auxiliary_coefficient k s z hk hs').trans hz
  have root : (derivative^[k-1] p).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [coeff]
  apply zero_on_segment
  apply iterated_roots (segment ℝ (-z) (-1)) (convex_segment _ _) (k-1) p pn
    (by rw [pd]; omega) _ 0 root
  intro w hw
  have eq := (mem_rootSet.mp hw).2
  rw [coe_aeval_eq_eval] at eq
  have he : (w+1)^(s-1) * (w+z)^k = 0 := by simpa [p] using eq
  rcases mul_eq_zero.mp he with e | e
  · have h : w+1 = 0 := by
      by_contra h
      exact pow_ne_zero _ h e
    rw [eq_neg_of_add_eq_zero_left h]
    exact right_mem_segment _ _ _
  · have h : w+z = 0 := by
      by_contra h
      exact pow_ne_zero _ h e
    rw [eq_neg_of_add_eq_zero_left h]
    exact left_mem_segment _ _ _

end FussDyck
