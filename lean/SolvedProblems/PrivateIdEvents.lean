module

public import SolvedProblems.PrivateIdModel
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace PrivateIdentification

variable {s k : ℕ}

/-- The trajectories whose first t outputs extend to some trajectory in C. -/
def envelope (C : Set (Transcript s k)) (t : ℕ) : Set (Transcript s k) :=
  ⋃ v ∈ C, PiNat.cylinder v t

theorem measurable_envelope (C : Set (Transcript s k)) (t : ℕ) :
    MeasurableSet (envelope C t) :=
  (isOpen_iUnion fun v ↦ isOpen_iUnion fun _ ↦ PiNat.isOpen_cylinder _ v t).measurableSet

theorem mem_envelope {C : Set (Transcript s k)} {t : ℕ} {u : Transcript s k} :
    u ∈ envelope C t ↔ ∃ v ∈ C, PrefixEq u v t := by
  simp only [envelope, mem_iUnion, PiNat.mem_cylinder_iff, PrefixEq, exists_prop]

theorem subset_envelope (C : Set (Transcript s k)) (t : ℕ) : C ⊆ envelope C t :=
  fun u hu ↦ mem_envelope.mpr ⟨u, hu, fun _ _ ↦ rfl⟩

theorem envelope_prefix (C : Set (Transcript s k)) (t : ℕ) :
    PrefixEvent (envelope C t) t := by
  intro u v huv
  simp only [mem_envelope]
  constructor
  · rintro ⟨w, hw, huw⟩
    exact ⟨w, hw, fun j hj ↦ (huv j hj).symm.trans (huw j hj)⟩
  · rintro ⟨w, hw, hvw⟩
    exact ⟨w, hw, fun j hj ↦ (huv j hj).trans (hvw j hj)⟩

theorem antitone_envelope (C : Set (Transcript s k)) : Antitone (envelope C) := by
  intro a b hab u hu
  obtain ⟨v, hv, huv⟩ := mem_envelope.mp hu
  exact mem_envelope.mpr ⟨v, hv, fun j hj ↦ huv j (hj.trans_le hab)⟩

theorem iInter_envelope {C : Set (Transcript s k)} (hC : IsClosed C) :
    ⋂ t, envelope C t = C := by
  apply Subset.antisymm _ (subset_iInter (subset_envelope C))
  intro u hu
  by_contra h
  obtain ⟨t, ht⟩ := PiNat.exists_disjoint_cylinder hC h
  obtain ⟨v, hv, huv⟩ := mem_envelope.mp (mem_iInter.mp hu t)
  exact Set.disjoint_left.mp ht hv (PiNat.mem_cylinder_iff.mpr fun j hj ↦ (huv j hj).symm)

theorem tendsto_envelope (μ : Measure (Transcript s k)) [IsProbabilityMeasure μ]
    {C : Set (Transcript s k)} (hC : IsClosed C) :
    Tendsto (fun t ↦ μ.real (envelope C t)) atTop (𝓝 (μ.real C)) := by
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun t ↦ (measurable_envelope C t).nullMeasurableSet)
    (antitone_envelope C) ⟨0, measure_ne_top _ _⟩
  rw [iInter_envelope hC] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

/-- A late replacement cannot significantly decrease the probability of a closed event. -/
theorem late_edit {P : Mechanism s k} (hp : ProbLaw P) (hc : Causal P)
    {ω : ℝ → ℝ} (hw : Vanishes ω) (hpriv : PrivateWith P ω)
    (x : Input) {C : Set (Transcript s k)} (hC : IsClosed C) {a : ℝ} (ha : 0 < a) :
    ∃ t, ∀ y, Neighbors y x → PrefixEq x y t → (P x).real C - a ≤ (P y).real C := by
  let := hp x
  obtain ⟨δ, hδ, hω⟩ := hw a ha
  obtain ⟨t, ht⟩ := ((tendsto_envelope (P x) hC).eventually_lt_const
      (show (P x).real C < (P x).real C + δ by linarith)).exists
  refine ⟨t, fun y hxy hpre ↦ ?_⟩
  let := hp y
  let E := envelope C t
  have hCx : (P x).real C ≤ (P x).real E := measureReal_mono (subset_envelope C t)
  have hsmall : (P x).real (E \ C) < δ := by
    rw [measureReal_sdiff (subset_envelope C t) hC.measurableSet]
    linarith
  have hprob := hpriv y x hxy (E \ C) ((measurable_envelope C t).diff hC.measurableSet)
  have hb := hω ((P x).real (E \ C)) ⟨measureReal_nonneg, measureReal_le_one⟩ hsmall
  rw [measureReal_sdiff (subset_envelope C t) hC.measurableSet] at hprob
  have heq := hc x y t hpre E (measurable_envelope C t) (envelope_prefix C t)
  linarith

end PrivateIdentification
