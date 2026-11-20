module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Computability.Primrec.List

@[expose] public section

open Set MeasureTheory

namespace UncountableGeneration

abbrev Input := ℕ → ℕ
abbrev Output := ℕ → ℕ
abbrev Rule := Input → Measure Output

def col (w : ℕ) : ℕ := w.unpair.1

def Language (A : Set ℕ) : Set ℕ := {w | col w ∈ A}

def Valid (A : Set ℕ) (x : Input) : Prop := range x = Language A

def Success (A : Set ℕ) (x : Input) : Set Output :=
  {u | ∃ N, ∀ t ≥ N, col (u t) ∈ A ∧ ∀ m ≤ t, u t ≠ x m}

def PrefixEq {α : Type*} (x y : ℕ → α) (t : ℕ) : Prop := ∀ j < t, x j = y j

def PrefixEvent (E : Set Output) (t : ℕ) : Prop :=
  ∀ u v, PrefixEq u v t → (u ∈ E ↔ v ∈ E)

def ProbLaw (P : Rule) : Prop := ∀ x, IsProbabilityMeasure (P x)

def Causal (P : Rule) : Prop :=
  ∀ x y t, PrefixEq x y t → ∀ E, MeasurableSet E → PrefixEvent E t →
    (P x).real E = (P y).real E

def Neighbors (x y : Input) : Prop := ∃ t, x t ≠ y t ∧ ∀ j, j ≠ t → x j = y j

def PrivateWith (P : Rule) (ω : ℝ → ℝ) : Prop :=
  ∀ x y, Neighbors x y → ∀ E, MeasurableSet E → (P x).real E ≤ ω ((P y).real E)

def Vanishes (ω : ℝ → ℝ) : Prop :=
  ∀ a > 0, ∃ δ > 0, ∀ p ∈ Icc (0 : ℝ) 1, p < δ → ω p < a

/-- Worst-case eventual generation can be made arbitrarily unlikely on a fixed injective enumeration. -/
def ZeroUtility (P : Rule) : Prop :=
  ∀ η > 0, ∃ A : Set ℕ, A.Nonempty ∧ ∃ x : Input,
    Function.Injective x ∧ Valid A x ∧ (P x).real (Success A x) < η

def History (x : Input) (t : ℕ) := List.ofFn fun j : Fin (t+1) ↦ x j

/-- A primitive-recursive function on the current history outputs a fresh target word
starting at the very first observation, even when observations repeat. -/
def Ordinary : Prop :=
  ∃ g : List ℕ → ℕ, Primrec g ∧ ∀ A : Set ℕ, A.Nonempty → ∀ x, Valid A x →
    ∀ t, g (History x t) ∈ Language A ∧ ∀ j ≤ t, g (History x t) ≠ x j

end UncountableGeneration
