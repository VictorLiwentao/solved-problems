module

public import SolvedProblems.UncountableGenerationModel
import SolvedProblems.PrivateIdentification

@[expose] public section

open Set MeasureTheory
namespace UncountableGeneration

def Members (A : Set ℕ) : Set Output := {u | ∃ N, ∀ t ≥ N, col (u t) ∈ A}

/-- Postprocess each output to its membership bit. The closed-event completion
argument for binary trajectories then gives a full enumeration of the selected columns. -/
theorem extend_members {P : Rule} (hp : ProbLaw P) (hc : Causal P) {ω : ℝ → ℝ}
    (hw : Vanishes ω) (hpriv : PrivateWith P ω) (A : Set ℕ) (x : Input)
    (hx : ∀ j, col (x j) ∈ A) (hi : Function.Injective x) {η : ℝ} (hη : 0 < η) :
    ∃ y : Input, Function.Injective y ∧ Valid A y ∧
      (P y).real (Success A y) ≤ (P x).real (Members A) + η := by
  classical
  let bit (w : ℕ) : Fin 2 := if col w ∈ A then 1 else 0
  let f (u : Output) : PrivateIdentification.Transcript 1 1 := fun t _ ↦ bit (u t)
  have hm : Measurable f := Measurable.of_eval fun t ↦ Measurable.of_eval fun _ ↦
    (measurable_of_countable bit).comp (measurable_pi_apply t)
  let Q : PrivateIdentification.Mechanism 1 1 := fun z ↦ (P z).map f
  have hq : PrivateIdentification.ProbLaw Q := fun z ↦
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr (hp z)
  have hqc : PrivateIdentification.Causal Q := by
    intro a b t hab E he hprefix
    simp only [Q, map_measureReal_apply hm he]
    apply hc a b t hab _ (he.preimage hm)
    intro u v huv
    apply hprefix (f u) (f v)
    exact fun n hn ↦ funext fun _ ↦ congrArg bit (huv n hn)
  have hqp : PrivateIdentification.PrivateWith Q ω := by
    intro a b hab E he
    simp only [Q, map_measureReal_apply hm he]
    exact hpriv a b hab _ (he.preimage hm)
  let E := PrivateIdentification.Success (k := 1) (0 : Fin 1)
  have he : MeasurableSet E := PrivateIdentification.measurableSet_success _
  have hpre : f ⁻¹' E = Members A := by
    ext u
    simp only [mem_preimage, E, PrivateIdentification.Success, Members, mem_ofPred_eq, f]
    simp [bit]
  obtain ⟨y, hy, hbound⟩ := PrivateIdentification.extend_event hq hqc hw hqp x
    (Language A) true hx (fun _ ↦ hi) he.compl hη
  let := hq x
  let := hq y
  rw [probReal_compl_eq_one_sub he, probReal_compl_eq_one_sub he] at hbound
  simp only [Q, map_measureReal_apply hm he, hpre] at hbound
  let := hp y
  have hs : Success A y ⊆ Members A := by
    rintro u ⟨N, hN⟩
    exact ⟨N, fun t ht ↦ (hN t ht).1⟩
  exact ⟨y, hy.1 rfl, hy.2, (measureReal_mono hs).trans (by linarith)⟩

end UncountableGeneration
