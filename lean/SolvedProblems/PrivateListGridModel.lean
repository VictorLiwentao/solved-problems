module

public import SolvedProblems.PrivateListModel
public import SolvedProblems.PrivateListMeasurePacking
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

namespace PrivateList

open MeasureTheory Set
open scoped Classical

abbrev Sample (k m : ℕ) := Fin m → Point × Label k

def Consistent {k m} (s : Sample k m) : Prop :=
  ∃ h : Hyp k, Valid h ∧ ∀ i, h (s i).1 = (s i).2

def Neighbors {X : Type} {m} (s t : Fin m → X) : Prop :=
  ∃ i : Fin m, ∀ j, j ≠ i → s j = t j

/-- The output space may contain arbitrary improper list-valued predictors.
All probability bounds below use only measurable omission events. -/
structure Rule (k m : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  law : Sample k m → Measure Ω
  normalized : ∀ s, IsProbabilityMeasure (law s)
  predict : Ω → Point → Finset (Label k)
  listSize : ∀ ω x, (predict ω x).card ≤ k
  measurable : ∀ x y, MeasurableSet {ω | y ∉ predict ω x}

def Private {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (scale δ : ℝ) : Prop :=
  ∀ s t, Neighbors s t → MeasureDominates scale δ (A.law s) (A.law t)

noncomputable def omission {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (s : Sample k m)
    (x : Point) (y : Label k) : ℝ := (A.law s).real {ω | y ∉ A.predict ω x}

structure Template (k m : ℕ) where
  xRank : Equiv.Perm (Fin m)
  yRank : Equiv.Perm (Fin m)
  label : Fin m → Label k

def place {k m} (T : Template k m) (a b : Fin m → ℕ) : Sample k m :=
  fun i => ((a (T.xRank i),b (T.yRank i)),T.label i)

abbrev Cell (m : ℕ) := Fin (m+1) × Fin (m+1)

noncomputable def lookup {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (T : Template k m)
    (a b : Fin (m+1) → ℕ) (v : Cell m) (y : Label k) : ℝ :=
  omission A (place T (fun i => a (v.1.succAbove i)) (fun i => b (v.2.succAbove i)))
    (a v.1,b v.2) y

end PrivateList
