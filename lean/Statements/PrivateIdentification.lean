module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

open MeasureTheory Set

namespace PrivateIdentification

abbrev Input := ℕ → ℕ

/-- A slot contains either zero (unused), or one plus the index of a language. -/
abbrev Transcript (s k : ℕ) := ℕ → Fin k → Fin (s + 1)

abbrev Mechanism (s k : ℕ) := Input → Measure (Transcript s k)

def PrefixEq {α : Type*} (u v : ℕ → α) (t : ℕ) : Prop := ∀ j < t, u j = v j

def PrefixEvent {s k : ℕ} (E : Set (Transcript s k)) (t : ℕ) : Prop :=
  ∀ u v, PrefixEq u v t → (u ∈ E ↔ v ∈ E)

def ProbLaw {s k : ℕ} (P : Mechanism s k) : Prop := ∀ x, IsProbabilityMeasure (P x)

def Causal {s k : ℕ} (P : Mechanism s k) : Prop :=
  ∀ x y t, PrefixEq x y t → ∀ E, MeasurableSet E → PrefixEvent E t →
    (P x).real E = (P y).real E

def Neighbors (x y : Input) : Prop :=
  ∃ t, x t ≠ y t ∧ ∀ j, j ≠ t → x j = y j

def PrivateWith {s k : ℕ} (P : Mechanism s k) (ω : ℝ → ℝ) : Prop :=
  ∀ x y, Neighbors x y → ∀ E, MeasurableSet E → (P x).real E ≤ ω ((P y).real E)

/-- The uniform bound on probabilities of rare events tends to zero at zero. -/
def Vanishes (ω : ℝ → ℝ) : Prop :=
  ∀ a > 0, ∃ δ > 0, ∀ p ∈ Icc (0 : ℝ) 1, p < δ → ω p < a

def Success {s k : ℕ} (i : Fin s) : Set (Transcript s k) :=
  {u | ∃ N, ∀ n ≥ N, ∃ j, u n j = i.succ}

def Valid (repetitionFree : Bool) (L : Set ℕ) (x : Input) : Prop :=
  (repetitionFree = true → Function.Injective x) ∧ range x = L

def Common {s : ℕ} (repetitionFree : Bool) (L : Fin s → Set ℕ) : Prop :=
  if repetitionFree then (⋂ i, L i).Infinite else (⋂ i, L i).Nonempty

/-- Every private learner has a valid enumeration with success within any positive
    tolerance of the upper bound. An input-independent 0-private learner attains it. -/
def Minimax : Prop :=
  ∀ (s k : ℕ), k < s → ∀ (L : Fin s → Set ℕ), (∀ i, (L i).Infinite) →
    Function.Injective L → ∀ repetitionFree, Common repetitionFree L →
    (∀ (P : Mechanism s k) (ω : ℝ → ℝ), ProbLaw P → Causal P →
      Vanishes ω → PrivateWith P ω → ∀ η > 0, ∃ i x,
      Valid repetitionFree (L i) x ∧ (P x).real (Success i) ≤ (k : ℝ) / s + η) ∧
    ∃ P : Mechanism s k, ProbLaw P ∧ Causal P ∧ PrivateWith P id ∧
      ∀ x i, (P x).real (Success i) = (k : ℝ) / s

/-- The sharp k/s bound under a uniform privacy modulus, for repetition-free streams with
    infinite common intersection and for unrestricted streams with a common word. -/
theorem private_identification_minimax : Minimax := by sorry

/-- Zero records a vacant slot. Every natural-number label has its own positive code. -/
abbrev RawTranscript (k : ℕ) := ℕ → Fin k → ℕ

def RawSuccess {k : ℕ} (label : ℕ) : Set (RawTranscript k) :=
  {u | ∃ N, ∀ n ≥ N, ∃ j, u n j = label + 1}

def RawCausal {k : ℕ} (P : Input → Measure (RawTranscript k)) : Prop :=
  ∀ x y t, PrefixEq x y t → ∀ E : Set (RawTranscript k), MeasurableSet E →
    (∀ u v, PrefixEq u v t → (u ∈ E ↔ v ∈ E)) →
      (P x).real E = (P y).real E

def RawPrivateWith {k : ℕ} (P : Input → Measure (RawTranscript k)) (ω : ℝ → ℝ) : Prop :=
  ∀ x y, Neighbors x y → ∀ E, MeasurableSet E → (P x).real E ≤ ω ((P y).real E)

/-- Restrict a countable-alphabet learner to any finite selection of distinct labels.
The same projected law preserves every privacy modulus enjoyed by the original law. -/
def CountableProjection : Prop :=
  ∀ (s k : ℕ) (labels : Fin s ↪ ℕ) (P : Input → Measure (RawTranscript k)),
    (∀ x, IsProbabilityMeasure (P x)) → RawCausal P →
      ∃ Q : Mechanism s k, ProbLaw Q ∧ Causal Q ∧
        (∀ ω, RawPrivateWith P ω → PrivateWith Q ω) ∧
        ∀ x i, (Q x).real (Success i) = (P x).real (RawSuccess (labels i))

/-- A causal learner over countably many candidate labels admits a finite projection
    preserving all selected success probabilities and every privacy modulus. -/
theorem countable_projection : CountableProjection := by sorry

end PrivateIdentification
