module

public import SolvedProblems.PrivateListGridModel
public import SolvedProblems.PrivateListAverage
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

namespace PrivateList

open MeasureTheory Set
open scoped Classical

def omitted {k s Ω} [MeasurableSpace Ω] (A : Rule k s Ω) (z : Point × Label k) : Set Ω :=
  {ω | z.2 ∉ A.predict ω z.1}

/-- Risk on the uniform distribution of a finite labeled population, counting multiplicities. -/
noncomputable def risk {k s m Ω} [MeasurableSpace Ω] (A : Rule k s Ω) (t : Sample k m) (ω : Ω) : ℝ :=
  avg fun i => (omitted A (t i)).indicator (fun _ => (1:ℝ)) ω

/-- The usual PAC guarantee specialized to arbitrary finitely supported uniform
labeled populations and exactly IID samples of size `s`. -/
def PopulationPAC {k s Ω} [MeasurableSpace Ω] (A : Rule k s Ω) (α β : ℝ) : Prop :=
  ∀ m, 0 < m → ∀ t : Sample k m, Consistent t →
    avg (fun u : Fin s → Fin m => (A.law (t ∘ u)).real {ω | α < risk A t ω}) ≤ β

theorem avg_omissions {k s m Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω) (t : Sample k m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {α : ℝ} (hα : 0 ≤ α) :
    avg (fun i => μ.real (omitted A (t i))) ≤ α + μ.real {ω | α < risk A t ω} := by
  let f (i : Fin m) := (omitted A (t i)).indicator (fun _ => (1:ℝ))
  have meas (i) : Measurable (f i) := measurable_const.indicator (A.measurable _ _)
  have intg (i) : Integrable (f i) μ := (integrable_const _).indicator (A.measurable _ _)
  have F : Measurable (risk A t) :=
    (Finset.measurable_fun_sum _ (fun i _ => meas i)).div_const _
  let E := {ω | α < risk A t ω}
  have mE : MeasurableSet E := measurableSet_lt measurable_const F
  have hInt : (∫ ω, risk A t ω ∂μ) = avg (fun i => μ.real (omitted A (t i))) := by
    change (∫ ω, (∑ i, f i ω) / (Fintype.card (Fin m):ℝ) ∂μ) = _
    simp only [integral_div,integral_finsetSum _ (fun i _ => intg i)]
    have fi (i) : (∫ ω, f i ω ∂μ) = μ.real (omitted A (t i)) := integral_indicator_one (A.measurable _ _)
    simp only [avg,fi]
  have riskInt : Integrable (risk A t) μ :=
    (integrable_finsetSum _ (fun i _ => intg i)).div_const _
  have failInt : Integrable (E.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator mE
  have cInt : (∫ _ : Ω, α ∂μ) = α := by simp
  have fail : (∫ ω, E.indicator (fun _ => (1:ℝ)) ω ∂μ) = μ.real E := integral_indicator_one mE
  rw [← hInt]
  apply LE.le.trans (b := ∫ ω, α+E.indicator (fun _ => (1:ℝ)) ω ∂μ)
  swap
  · rw [integral_add (integrable_const α) failInt,cInt,fail]
  apply integral_mono riskInt ((integrable_const _).add failInt)
  intro ω
  change risk A t ω ≤ α + E.indicator (fun _ => (1:ℝ)) ω
  by_cases h : ω ∈ E
  · rw [Set.indicator_of_mem h]
    have le : risk A t ω ≤ 1 := by
      calc
        _ ≤ avg (fun _ : Fin m => (1:ℝ)) := avg_mono (fun i => by dsimp [Set.indicator];split <;> norm_num)
        _ = _ := avg_const _
    linarith
  · rw [Set.indicator_of_notMem h,add_zero]
    exact le_of_not_gt h

end PrivateList
