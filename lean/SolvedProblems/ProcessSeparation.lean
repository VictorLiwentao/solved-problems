module

public import SolvedProblems.ProcessSeparationModel
import SolvedProblems.ProcessSeparationBlocks
import SolvedProblems.ProcessSeparationAdversary

public section

open Filter Set MeasureTheory
open scoped Topology

namespace ProcessSeparation

/-- One is the universal upper bound on regret at every finite horizon. -/
theorem regret_upper (p f y : Stream) (T : ℕ) : loss p y T - loss f y T ≤ 1 := by
  have h : mistakes p y T ≤ T :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hp : loss p y T ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg T)
  have hf : 0 ≤ loss f y T := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact (sub_le_self _ hf).trans hp

theorem separation (g : ℕ → ℝ) (nonneg : ∀ T, 0 ≤ g T) (mono : Monotone g)
    (diverges : Tendsto g atTop atTop) :
    ∃ (H : Set Stream) (A : Strategy), H.Nonempty ∧ IsClosed H ∧
      (∀ y : Stream, Realizable H y → ∀ T, (mistakes (prediction A y) y T : ℝ) ≤ g T) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (R : (t : ℕ) → (Fin t → ℕ) → Ω → ℕ) (_ : ∀ t h, Measurable (R t h)),
        ∃ (y f : Stream), f ∈ H ∧ Tendsto (loss f y) atTop (𝓝 0) ∧
          ∀ᵐ ω ∂μ, Tendsto
            (fun T ↦ loss (fun t ↦ R t (fun i ↦ y i) ω) y T - loss f y T) atTop (𝓝 1)
    := by
  obtain ⟨C⟩ := clock_exists mono diverges
  obtain ⟨f,hf,_⟩ := C.dense_comparator (fun _ ↦ 0)
  refine ⟨C.concepts,C.learner,⟨f,hf⟩,C.closed_concepts,fun y ↦ C.realizable_bound nonneg mono,?_⟩
  intro Ω _ μ _ R hm
  obtain ⟨y,bad⟩ := adversarial_stream μ R hm
  obtain ⟨target,ht,low⟩ := C.dense_comparator y
  refine ⟨y,target,ht,low,?_⟩
  filter_upwards [bad] with ω high
  simpa only [sub_zero] using high.sub low

end ProcessSeparation
