module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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

end RationalReturns
