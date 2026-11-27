module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace PrivateList

abbrev Point := ℕ × ℕ
abbrev Label (k : ℕ) := Fin (k+1)
abbrev Hyp (k : ℕ) := Point → Label k

def SW (x y : Point) : Prop := x.1 < y.1 ∧ x.2 < y.2

def opposed (x y : Point) : Prop := x.1 < y.1 ∧ y.2 < x.2

/-- Different positive colors occupy strictly southwest-to-northeast blocks.
Inside a block the two orders agree, except in color two, where they are reversed. -/
def Valid {k} (h : Hyp k) : Prop :=
  {x | h x ≠ 0}.Finite ∧
  (∀ x y, h x ≠ 0 → h x < h y → SW x y) ∧
  ∀ x y, x ≠ y → h x ≠ 0 → h x = h y →
    if (h x).val = 2 then opposed x y ∨ opposed y x else SW x y ∨ SW y x

/-- All outgoing labels occur at every node because the class has k+1 labels. -/
def LittlestoneDepth (k n : ℕ) : Prop :=
  ∃ T : List (Label k) → Point, ∀ path : Fin n → Label k, ∃ h : Hyp k,
    Valid h ∧ ∀ i : Fin n, h (T ((List.ofFn path).take i.val)) = path i

/-- The permutation gives the witness order of the k+1 distinct labels. -/
def MonotoneLength (k n : ℕ) : Prop :=
  ∃ x : Fin n → Point, Function.Injective x ∧ ∃ π : Equiv.Perm (Label k),
    ∀ f : Fin n → Label k, Monotone f → ∃ h : Hyp k, Valid h ∧ ∀ i, h (x i) = π (f i)

end PrivateList
