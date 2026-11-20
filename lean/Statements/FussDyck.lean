module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace FussDyck

/-- The number of north steps immediately before each successive east step.
Expanding entry vᵢ into vᵢ north steps followed by one east step recovers the path.
For m > 0, a path to (m*n,n) above x = m*y must end in an east step:
its predecessor cannot be (m*n,n-1). -/
abbrev Word (n b : Nat) := Fin b → Fin (n+1)

def prefixN (v : Word n b) (t : Nat) : Nat :=
  @List.sum Nat instAddNat Nat.instAddMonoid.toAddZeroClass.toAddZero.toZero
    ((List.ofFn (fun i => (v i).val)).take t)

def positions (v : Word n b) (h : Nat) : Finset (Fin b) :=
  Finset.univ.filter (fun i => h < (v i).val)

/-- Each positive run ends in one NE and each run of length at least two
ends in one NNE. The first condition fixes the total number of north steps. -/
def Stats (v : Word n b) (k j : Nat) :=
  prefixN v b = n ∧ (positions v 0).card = k ∧ (positions v 1).card = j

/-- At the end of each east step x = t and y is the number of north steps so far. -/
def FussPath (m : Nat) (v : Word n (m*n)) := ∀ t ≤ m*n, t ≤ m * prefixN v t

noncomputable def pathCount (m n k j : Nat) : Nat := by
  classical
  exact Fintype.card {v : Word n (m*n) // Stats v k j ∧ FussPath m v}

def hCoeff (k s j : Nat) : Nat :=
  if s = 0 then if j = 0 then 1 else 0
  else if j = 0 then 0 else k.choose j * (s-1).choose (j-1)


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

/-- The counts and roots of the fixed-peak Fuss–Dyck polynomials. The multiset
equality preserves the multiplicity of every zero under a change of Fuss slope. -/
theorem peakTheorem {m n : Nat} (hm : 0 < m) (hn : 0 < n) (k : Nat) :
    (∀ j, (k = 0 ∨ n < k ∨ k < j) → pathCount m n k j = 0) ∧
    (0 < k → k ≤ n →
      (∀ j, (m*n+1) * pathCount m n k j = (m*n+1).choose k * hCoeff k (n-k) j) ∧
      0 < prefactor m n k ∧
      pathPoly m n k = C (prefactor m n k : ℂ) * shapePoly k (n-k) ∧
      (∀ z : ℂ, (pathPoly m n k).IsRoot z → z.im = 0 ∧ z.re ≤ 0) ∧
      ∀ m' : Nat, 0 < m' → (pathPoly m n k).roots = (pathPoly m' n k).roots) := by sorry

end FussDyck
