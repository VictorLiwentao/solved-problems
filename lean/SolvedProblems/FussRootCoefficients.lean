module

public import SolvedProblems.FussModel
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Coeff

public section

namespace FussDyck

open Polynomial

/-- Extracting degree k-1 in the auxiliary variable leaves one summand for each
possible positive number of long vertical runs. -/
theorem auxiliary_coefficient {R : Type*} [CommSemiring R] (k s : ℕ) (z : R)
    (hk : 0 < k) (hs : 0 < s) :
    (((X+1)^(s-1) * (X+C z)^k : Polynomial R).coeff (k-1)) =
      ∑ j ∈ Finset.range (k+1), (hCoeff k s j : R) * z^j := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have step : (k-1).succ = k := by omega
  rw [step, Finset.sum_range_succ' (f := fun j ↦ (hCoeff k s j : R) * z^j)]
  simp only [hCoeff, Nat.ne_of_gt hs, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel,
    Nat.cast_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have h : j < k := Finset.mem_range.mp hj
  rw [coeff_X_add_one_pow, coeff_X_add_C_pow]
  have sub : k - 1 - j = k - (j+1) := by omega
  have expo : k - (k-1-j) = j+1 := by omega
  rw [expo, sub, Nat.choose_symm (by omega : j+1 ≤ k), Nat.cast_mul]
  ac_rfl

end FussDyck
