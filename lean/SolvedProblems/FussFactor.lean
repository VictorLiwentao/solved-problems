module

public import SolvedProblems.FussPolynomialModel
import SolvedProblems.FussAppend
import SolvedProblems.FussCycle
import SolvedProblems.FussFree
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

public section

namespace FussDyck

open Polynomial
open scoped Polynomial

theorem scaled_count {m n : Nat} (hm : 0 < m) (hn : 0 < n) (k j : Nat) :
    (m*n+1) * pathCount m n k j = freeCount n (m*n+1) k j := by
  rw [append_count hm]
  exact cycle_count hn (Nat.succ_pos _) ((Nat.coprime_mul_right_add_right _ _ _).mpr
    (Nat.coprime_one_right _)) k j

theorem coefficient_formula {m n k : Nat} (hm : 0 < m) (hn : 0 < n) (hk : k ≤ n) (j : Nat) :
    (m*n+1) * pathCount m n k j = (m*n+1).choose k * hCoeff k (n-k) j :=
  (scaled_count hm hn _ _).trans (free_formula hk j)

theorem infeasible_count {m n k j : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : k = 0 ∨ n < k ∨ k < j) : pathCount m n k j = 0 := by
  have bad : n < k ∨ (0 < n ∧ k = 0) ∨ n < k+j ∨ k < j := by
    rcases h with h|h|h <;> omega
  have hz := (scaled_count hm hn k j).trans (free_zero bad)
  exact (Nat.mul_eq_zero.mp hz).resolve_left (Nat.succ_ne_zero _)

theorem factor_positive {m n k : Nat} (hm : 0 < m) (hk : k ≤ n) : 0 < prefactor m n k := by
  have hmn : n ≤ m*n := by simpa using Nat.mul_le_mul_right n (show 1 ≤ m from hm)
  have hc := Nat.choose_pos (show k ≤ m*n+1 by omega)
  unfold prefactor
  positivity

theorem factorization {m n k : Nat} (hm : 0 < m) (hn : 0 < n) (hk : k ≤ n) :
    pathPoly m n k = C (prefactor m n k : ℂ) * shapePoly k (n-k) := by
  unfold pathPoly shapePoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : ((m*n+1 : Nat) : ℂ) * (pathCount m n k j : ℂ) =
      (((m*n+1).choose k : Nat) : ℂ) * (hCoeff k (n-k) j : ℂ) := by
    exact_mod_cast coefficient_formula hm hn hk j
  have hB : ((m*n+1 : Nat) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (m*n))
  have hh : (pathCount m n k j : ℂ) = (prefactor m n k : ℂ) * hCoeff k (n-k) j := by
    simp only [prefactor,Complex.ofReal_div,Complex.ofReal_natCast]
    field_simp [hB]
    linear_combination h
  rw [← mul_assoc,← C_mul,hh]

end FussDyck
