module

public import SolvedProblems.PrivateIdModel

@[expose] public section

open MeasureTheory Set

namespace PrivateIdentification

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

open Classical in
private noncomputable def selectLabel {s : ℕ} (labels : Fin s ↪ ℕ) (v : ℕ) : Fin (s+1) :=
  if h : ∃ i, labels i + 1 = v then h.choose.succ else 0

private theorem selectLabel_eq {s : ℕ} (labels : Fin s ↪ ℕ) (v : ℕ) (i : Fin s) :
    selectLabel labels v = i.succ ↔ v = labels i + 1 := by
  classical
  unfold selectLabel
  split <;> rename_i h
  · have he := h.choose_spec
    constructor
    · intro h'
      have eq := Fin.succ_injective _ h'
      rw [← eq]
      exact he.symm
    · intro h'
      exact congrArg Fin.succ (labels.injective (Nat.add_right_cancel (he.trans h')))
  · constructor
    · intro h'
      have := congrArg Fin.val h'
      simp at this
    · intro h'
      exact (h ⟨i, h'.symm⟩).elim

/-- Discard labels outside the selection at every time and slot. This deterministic
map commutes with observing a prefix and preserves the selected success events. -/
theorem countable_projection : CountableProjection := by
  intro s k labels P prob causal
  let project (u : RawTranscript k) : Transcript s k := fun n j ↦ selectLabel labels (u n j)
  have hm : Measurable project := Measurable.of_eval fun n ↦ Measurable.of_eval fun j ↦
    (measurable_of_countable (selectLabel labels)).comp
      ((measurable_pi_apply j).comp (measurable_pi_apply n))
  refine ⟨fun x ↦ (P x).map project, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr (prob x)
  · intro x y t hxy E hE hprefix
    simp only [map_measureReal_apply hm hE]
    apply causal x y t hxy _ (hE.preimage hm)
    intro u v huv
    apply hprefix (project u) (project v)
    intro n hn
    exact congrArg (fun row j ↦ selectLabel labels (row j)) (huv n hn)
  · intro ω privateLaw x y neighbors E hE
    simp only [map_measureReal_apply hm hE]
    exact privateLaw x y neighbors _ (hE.preimage hm)
  · intro x i
    rw [map_measureReal_apply hm (measurableSet_success i)]
    congr 1
    ext u
    simp [Success, RawSuccess, project, selectLabel_eq]

end PrivateIdentification
