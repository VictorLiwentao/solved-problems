module

public import SolvedProblems.PrivateListPopulation
public import SolvedProblems.PrivateListMarginals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrivateList

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable def mixture {I Ω : Type} [Fintype I] [MeasurableSpace Ω] (μ : I → Measure Ω) : Measure Ω :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, μ i

theorem mixture_probability {I Ω : Type} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (mixture μ) := by
  constructor
  rw [mixture,Measure.smul_apply,Measure.finsetSum_apply]
  simp [smul_eq_mul,ENNReal.inv_mul_cancel (show (Fintype.card I : ℝ≥0∞) ≠ 0 by exact_mod_cast Fintype.card_ne_zero) (by simp)]

theorem mixture_real {I Ω : Type} [Fintype I] [MeasurableSpace Ω] (μ : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (E : Set Ω) : (mixture μ).real E = avg (fun i => (μ i).real E) := by
  rw [mixture,measureReal_ennreal_smul_apply,measureReal_def,Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  simp [avg,measureReal_def,div_eq_inv_mul]

/-- An IID draw with repeated indices is replaced by a fixed dataset independent of the population. -/
noncomputable def subsample {k m s} (t : Sample k m) (u : Fin s → Fin m) : Sample k s :=
  if Function.Injective u then t ∘ u else fun _ => ((0,0),0)

noncomputable def resample {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω) : Rule k m Ω where
  law t := mixture (fun u => A.law (subsample t u))
  normalized t := by
    let (u : Fin s → Fin m) := A.normalized (subsample t u)
    exact mixture_probability _
  predict := A.predict
  listSize := A.listSize
  measurable := A.measurable

theorem resample_real {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω)
    (t : Sample k m) (E : Set Ω) : ((resample A).law t).real E = avg (fun u => (A.law (subsample t u)).real E) := by
  let (u : Fin s → Fin m) := A.normalized (subsample t u)
  exact mixture_real _ _

theorem resample_private {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω)
    {δ : ℝ} (hδ : 0 ≤ δ) (priv : Private A 2 δ) : Private (resample (m := m) A) 2 (δ*(s/m)) := by
  rintro t t' ⟨x,hx⟩ E hE
  rw [resample_real,resample_real]
  have bound (u : Fin s → Fin m) : (A.law (subsample t' u)).real E ≤
      2*(A.law (subsample t u)).real E + δ*oneIf (∃ i, u i=x) := by
    by_cases inj : Function.Injective u
    · by_cases hit : ∃ i, u i=x
      · obtain ⟨i,hi⟩ := hit
        have adj : Neighbors (t ∘ u) (t' ∘ u) := ⟨i,fun j ne => hx _ (fun hj => ne (inj (hj.trans hi.symm)))⟩
        simpa [subsample,inj,oneIf,show ∃ i, u i=x from ⟨i,hi⟩] using priv _ _ adj E hE
      · have eq : t ∘ u = t' ∘ u := funext fun i => hx _ (fun h => hit ⟨i,h⟩)
        simp only [subsample,inj,↓reduceIte,eq,oneIf,hit,mul_zero,add_zero]
        linarith [measureReal_nonneg (μ := A.law (t' ∘ u)) (s := E)]
    · simp only [subsample,inj,↓reduceIte]
      have corr : 0 ≤ δ*oneIf (∃ i, u i=x) := mul_nonneg hδ (by unfold oneIf;split <;> norm_num)
      linarith [measureReal_nonneg (μ := A.law (fun _ => ((0,0),0))) (s := E)]
  exact (avg_mono bound).trans (by rw [avg_add,avg_mul,avg_mul]; gcongr; exact avg_hit_bound x)

end PrivateList
