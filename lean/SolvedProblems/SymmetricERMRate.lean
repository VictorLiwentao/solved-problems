module

public import SolvedProblems.SymmetricERMCompression
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace SymmetricERM

open scoped Classical

/-- Paying a factor of eight per retained index lets the binomial theorem sum over
all index sets, without any rounding conventions for binomial-tail estimates. -/
theorem index_weight (B m : ℕ) :
    (∑ I : Finset (Fin m), if I.card ≤ B then (3/4 : ℝ) ^ (m - I.card) else 0)
      ≤ 8^B * (7/8 : ℝ)^m := by
  classical
  have expand :
      (∑ I : Finset (Fin m), (1/8 : ℝ)^I.card * (3/4 : ℝ)^(m-I.card)) = (7/8 : ℝ)^m := by
    simpa only [Finset.prod_const, Finset.card_univ, Finset.card_compl, Fintype.card_fin, show (1/8:ℝ) + 3/4 = 7/8 by norm_num] using
      (Fintype.prod_add (fun _ : Fin m => (1/8 : ℝ)) (fun _ => (3/4 : ℝ))).symm
  rw [← expand, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  by_cases h : I.card ≤ B
  · rw [ite_eq_left h, ← mul_assoc]
    apply le_mul_of_one_le_left (by positivity)
    have hi : (1 : ℝ) = 8^I.card * (1/8 : ℝ)^I.card := by rw [← mul_pow]; norm_num
    exact hi.le.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (by positivity))
  · rw [ite_eq_right h]
    positivity

theorem perm_count (r : ℕ) :
    Fintype.card (Equiv.Perm (Label r)) ≤ 2^(4^r) := by
  rw [Fintype.card_perm, Fintype.card_finset, Fintype.card_fin]
  apply (Nat.factorial_le_pow _).trans
  rw [← Nat.pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  calc
    r * 2^r ≤ 2^r * 2^r := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
    _ = 4^r := by rw [← Nat.mul_pow]

theorem good_upper (r : ℕ) : Threshold (@good (4^r) r) (64 * 4^r) := by
  intro m hm p hp t
  let B := 4^r
  have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
  calc
    _ ≤ _ := compression_bound hp t
    _ ≤ ((2 : ℝ)^B) * (8^B * (7/8 : ℝ)^m) := by
      apply mul_le_mul _ (index_weight _ _) _ (by positivity)
      · exact_mod_cast perm_count r
      · apply Finset.sum_nonneg
        intro I _
        split <;> positivity
    _ ≤ 2^B * (8^B * (7/8 : ℝ)^(64 * B)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ = (16 * (7/8 : ℝ)^64)^B := by rw [pow_mul, mul_pow, ← mul_assoc, ← mul_pow]; norm_num
    _ ≤ (1/4 : ℝ)^B := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ ≤ 1/4 := by simpa using (pow_le_pow_of_le_one (a := (1/4 : ℝ)) (by norm_num) (by norm_num) hB)

end SymmetricERM
