module

public import SolvedProblems.SymmetricERMCompression
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace SymmetricERM

open scoped Classical

/-- Every empirical minimizer on this finite class has a finite distribution-free
threshold. Thus the separation compares ordinary sample complexities. -/
theorem finite_threshold {B r} {A : Learner B r} (hA : ERM A) :
    ∃ n : ℕ, Threshold A n := by
  classical
  let C := Fintype.card (Code B r)
  have hC : (0 : ℝ) < C := by
    have : 0 < C := @Fintype.card_pos_iff (Code B r) _ |>.mpr ⟨emptyCode B r⟩
    exact_mod_cast this
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1/4 / C by positivity)
    (show (3/4:ℝ) < 1 by norm_num)
  refine ⟨n, ?_⟩
  intro m hm p hp t
  let mass (c : Code B r) (xs : Fin m → Point B r) : ℝ :=
    if (1/4:ℝ) < risk p t c then ∏ i, hit p t c (xs i) else 0
  have nonneg c xs : 0 ≤ mass c xs := by unfold mass; split <;>
    first | exact Finset.prod_nonneg fun _ _ => hit_nonnegative hp _ _ _ | exact le_rfl
  unfold failure
  calc
    _ ≤ ∑ xs : Fin m → Point B r, ∑ c : Code B r, mass c xs := by
      apply Finset.sum_le_sum
      intro xs _
      let c := A m (observe t xs)
      change (if (1/4:ℝ) < risk p t c then _ else _) ≤ _
      split
      · rename_i h
        have he : mass c xs = ∏ i, p (xs i) := by
          have each (i) : hit p t c (xs i) = p (xs i) := ite_eq_left (erm_fits hA t xs i)
          simp only [mass, ite_eq_left h, each]
        exact he.ge.trans (Finset.single_le_sum
          (f := fun c' : Code B r => mass c' xs) (fun c' _ => nonneg c' xs) (Finset.mem_univ c))
      · exact Finset.sum_nonneg (fun _ _ => nonneg _ _)
    _ = ∑ c : Code B r, ∑ xs : Fin m → Point B r, mass c xs := Finset.sum_comm
    _ ≤ ∑ _c : Code B r, (3/4:ℝ)^m := by
      apply Finset.sum_le_sum
      intro c _
      by_cases h : (1/4:ℝ) < risk p t c
      · simp only [mass, ite_eq_left h]
        rw [← Fintype.sum_pow]
        apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hit_nonnegative hp _ _ _)
        linarith [hit_risk hp t c]
      · simp only [mass, ite_eq_right h, Finset.sum_const_zero]
        positivity
    _ = (3/4:ℝ)^m * C := by simp [C, mul_comm]
    _ ≤ 1/4 := by
      apply (le_div_iff₀ hC).mp
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm).trans hn.le

end SymmetricERM
