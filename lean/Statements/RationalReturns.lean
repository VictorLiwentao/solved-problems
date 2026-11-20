module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace RationalReturns

/-- Column of the diagonal boundary at the start of row i. -/
def edge (m n i : ℕ) : ℕ := i*m/n

/-- The run condition forces one or more north steps at each of these columns. -/
def required (d k c : ℕ) : Prop := ∃ q < k, q*d = c

abbrev Word (m t : ℕ) := Fin t → Fin m

/-- A path between two boundary arrivals, encoded by the column of its north
step on each intervening row. All columns use the original rectangle coordinates. -/
def Valid (m n d k i j : ℕ) (w : Word m (j-i)) : Prop :=
  Monotone w ∧
  (∀ r, edge m n i ≤ (w r).val ∧ (w r).val ≤ edge m n (i+r.val)) ∧
  (∀ r, (w r).val ≠ k*d) ∧
  ∀ c, edge m n i ≤ c → c < edge m n j → required d k c → ∃ r, (w r).val = c

abbrev Segment (m n d k i j : ℕ) := {w : Word m (j-i) // Valid m n d k i j w}

noncomputable def segmentCount (m n d k i j : ℕ) : ℕ := by
  classical
  exact Fintype.card (Segment m n d k i j)

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

/-- The columns of successive north steps form a rational Dyck path if they
are weakly increasing and each step starts above the line between the endpoints. -/
def IsPath {m n : ℕ} (w : Word m n) : Prop :=
  Monotone w ∧ ∀ r, (w r).val ≤ edge m n r.val

/-- The first missing positive stride multiple is `k*d`. -/
def HasRun {m n : ℕ} (d k : ℕ) (w : Word m n) : Prop :=
  0 < k ∧ (∀ q, 0 < q → q < k → ∃ r, (w r).val = q*d) ∧
    ∀ r, (w r).val ≠ k*d

/-- A return is an equality between a north-step column and its row boundary. -/
noncomputable def returnCount {m n : ℕ} (w : Word m n) : ℕ := by
  classical
  exact ((Finset.range n).filter (fun a ↦ ∃ r : Fin n,
    r.val = a ∧ (w r).val = edge m n a)).card

/-- Number of physical north-step words with the two prescribed statistics. -/
noncomputable def jointCount (m n d k ℓ : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Word m n // IsPath w ∧ HasRun d k w ∧ returnCount w = ℓ}

/-- The determinant counts the actual north-step words on the segment, with
the given forbidden column, required columns, and floor-diagonal boundary. -/
theorem segment_determinant {m n d k i j : ℕ} (hn : 0 < n) (hm : n ≤ m) (hd : 0 < d)
    (hij : i < j) (hj : j ≤ n) :
    (segmentCount m n d k i j : ℤ) = determinantEntry m n d k i j := by sorry

/-- The joint run/return count for every permitted stride, including stride one
and the ratio stride floor(m/n). The entries on the right are explicit
binomial determinants; zero-based return index s counts chosen interior arrivals. -/
theorem joint_run_return {m n d k ℓ : ℕ} (hn : 0 < n) (hm : n ≤ m)
    (hd : 0 < d) (hdm : d ≤ m/n) (hk : 0 < k) (hkn : k ≤ n)
    (hℓ : 0 < ℓ) (hℓn : ℓ ≤ n) :
    (jointCount m n d k ℓ : ℤ) = ∑ s ∈ Finset.Ico (ℓ-1) n,
      (-1 : ℤ)^(s-(ℓ-1)) * (s.choose (ℓ-1) : ℤ) *
        (determinantMatrix m n d k ^ (s+1)) 0 (Fin.last n) := by sorry

end RationalReturns
