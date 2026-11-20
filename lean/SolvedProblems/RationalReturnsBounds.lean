module

public import SolvedProblems.RationalReturnsModel
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace RationalReturns

/-- Required and allowed physical columns in the horizontal interval [L,U). -/
def mandatory (d k L U : ℕ) : Finset ℕ :=
  ((Finset.range k).image (· * d)) ∩ Finset.Ico L U

def allowed (d k L U : ℕ) : Finset ℕ := (Finset.Ico L U).erase (k*d)

/-- The number of columns in the finite set strictly before the arrival at c. -/
def before (A : Finset ℕ) (c : ℕ) : ℕ := (A.filter (· < c)).card

/-- Required north steps since the segment's initial height, before column c. -/
def demand (m n i c : ℕ) : ℕ := (n*c + m-1)/m-i

/-- Each residual step must precede every arrival still demanding that step.
The minimum gives the tightest rank bound and defaults to the number of
allowed columns when no arrival makes such a demand. Ranks in Lean start at zero. -/
def flag (A B : Finset ℕ) (D : ℕ → ℕ) (L U h : ℕ) : ℕ :=
  (insert A.card (((Finset.Icc L U).filter (fun c => before B c + h < D c)).image (before A))).min'
    (Finset.insert_nonempty _ _)

/-- The determinant in the segment formula. Below its subdiagonal the lower
binomial index is negative, which contributes zero. -/
def binomialDet {r : ℕ} (b : Fin r → ℕ) : ℤ :=
  (Matrix.of fun h v : Fin r =>
    if h.val ≤ v.val+1 then ((b h).choose (v.val+1-h.val) : ℤ) else 0).det

/-- Explicit binomial determinant or zero in either infeasible case. -/
def determinantEntry (m n d k i j : ℕ) : ℤ :=
  let L := edge m n i
  let U := edge m n j
  let B := mandatory d k L U
  let A := allowed d k L U
  let R := j-i-B.card
  if B.card ≤ j-i ∧ ∀ c ∈ Finset.Icc L U, demand m n i c ≤ before B c + R then
    binomialDet (fun h : Fin R => flag A B (demand m n i) L U h.val)
  else 0

/-- The segment kernel has a zero diagonal and uses only boundary coordinates,
column ranks and binomial determinants. -/
def determinantMatrix (m n d k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  fun i j => if i < j then determinantEntry m n d k i.val j.val else 0

end RationalReturns
