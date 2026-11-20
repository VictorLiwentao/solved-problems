module

public import SolvedProblems.FussFactor
public import Mathlib.Algebra.Polynomial.Roots
import SolvedProblems.FussRoots

public section

namespace FussDyck

open Polynomial
open scoped Polynomial

/-- The counts and roots of the fixed-peak Fuss–Dyck polynomials. The multiset
equality preserves the multiplicity of every zero under a change of Fuss slope. -/
theorem peakTheorem {m n : Nat} (hm : 0 < m) (hn : 0 < n) (k : Nat) :
    (∀ j, (k = 0 ∨ n < k ∨ k < j) → pathCount m n k j = 0) ∧
    (0 < k → k ≤ n →
      (∀ j, (m*n+1) * pathCount m n k j = (m*n+1).choose k * hCoeff k (n-k) j) ∧
      0 < prefactor m n k ∧
      pathPoly m n k = C (prefactor m n k : ℂ) * shapePoly k (n-k) ∧
      (∀ z : ℂ, (pathPoly m n k).IsRoot z → z.im = 0 ∧ z.re ≤ 0) ∧
      ∀ m' : Nat, 0 < m' → (pathPoly m n k).roots = (pathPoly m' n k).roots) := by
  refine ⟨fun _ => infeasible_count hm hn,?_⟩
  intro hk hkn
  have fact := factorization hm hn hkn
  have pos := factor_positive hm hkn
  have ne : (prefactor m n k : ℂ) ≠ 0 := by exact_mod_cast pos.ne'
  refine ⟨coefficient_formula hm hn hkn,pos,fact,?_,?_⟩
  · intro z hz
    rw [fact] at hz
    apply shape_roots hk
    simpa [Polynomial.IsRoot,ne] using hz
  · intro m' hm'
    have pos' := factor_positive hm' hkn
    have ne' : (prefactor m' n k : ℂ) ≠ 0 := by exact_mod_cast pos'.ne'
    rw [fact,factorization hm' hn hkn,roots_C_mul _ ne,roots_C_mul _ ne']

end FussDyck
