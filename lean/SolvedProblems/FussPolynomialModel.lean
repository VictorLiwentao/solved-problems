module

public import SolvedProblems.FussModel
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

namespace FussDyck

open Polynomial
open scoped Polynomial

/-- The common shape of the peak polynomial after removing the slope-dependent factor. -/
noncomputable def shapePoly (k s : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (k+1), C (hCoeff k s j : ℂ) * X^j

/-- The coefficient of X to the j counts actual paths with j long vertical runs. -/
noncomputable def pathPoly (m n k : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (k+1), C (pathCount m n k j : ℂ) * X^j

noncomputable def prefactor (m n k : ℕ) : ℝ :=
  ((m*n+1).choose k : ℝ) / (m*n+1 : ℕ)

end FussDyck
