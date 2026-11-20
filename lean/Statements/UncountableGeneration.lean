module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Computability.Primrec.List

@[expose] public section

open Set MeasureTheory Function

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

/-- The finite-partition definition of a bounded Rényi divergence at order α>1.
One can include a leftover cell to complete any disjoint finite family to a partition.
Absolute continuity handles zero-probability cells. -/
def RenyiBudget (P : Rule) (α D : ℝ) : Prop :=
  ∀ x y, Neighbors x y → (P x) ≪ (P y) ∧
    ∀ (n : ℕ) (E : Fin n → Set Output), Pairwise (Disjoint on E) →
      (∀ j, MeasurableSet (E j)) →
        (∑ j, ((P x).real (E j)) ^ α / ((P y).real (E j)) ^ (α-1))
          ≤ Real.exp ((α-1)*D)

/-- No sequence lists all nonempty unions of complete columns. -/
theorem uncountably_many_languages :
    ¬ ∃ f : ℕ → Set ℕ, ∀ A : Set ℕ, A.Nonempty → ∃ n, f n = Language A := by sorry

/-- The explicit first-example generator is primitive recursive. -/
theorem ordinary_generator : Ordinary := by sorry

/-- Even fixed injective adversarial enumerations force zero worst-case success under any
uniform probability modulus vanishing at zero. -/
theorem vanishing_modulus_zero {P : Rule} (hp : ProbLaw P) (hc : Causal P)
    {ω : ℝ → ℝ} (hw : Vanishes ω) (hpriv : PrivateWith P ω) : ZeroUtility P := by sorry

/-- The pure differential privacy case for every finite real privacy parameter. -/
theorem pure_zero {P : Rule} (hp : ProbLaw P) (hc : Causal P) (ε : ℝ)
    (hpriv : PrivateWith P (fun p ↦ Real.exp ε * p)) : ZeroUtility P := by sorry

/-- A finite Rényi budget at any fixed order strictly greater than one has zero utility. -/
theorem renyi_zero {P : Rule} (hp : ProbLaw P) (hc : Causal P) {α D : ℝ}
    (hα : 1 < α) (hpriv : RenyiBudget P α D) : ZeroUtility P := by sorry

/-- The constant rule is admissible for all nonnegative budgets in both privacy models.
An injective enumeration of column one witnesses its zero worst-case utility. -/
theorem zero_attainable : ∃ P : Rule, ProbLaw P ∧ Causal P ∧
    (∀ ε : ℝ, 0 ≤ ε → PrivateWith P (fun p ↦ Real.exp ε * p)) ∧
    (∀ α D : ℝ, 1 < α → 0 ≤ D → RenyiBudget P α D) ∧ ZeroUtility P := by sorry

/-- Every positive additive privacy allowance restores probability-one utility. -/
theorem positive_slack (δ : ℝ) (hδ : 0 < δ) : ∃ P : Rule,
    ProbLaw P ∧ Causal P ∧ PrivateWith P (fun p ↦ p + δ) ∧
      ∀ A : Set ℕ, A.Nonempty → ∀ x, Valid A x → (P x).real (Success A x) = 1 := by sorry

end UncountableGeneration
