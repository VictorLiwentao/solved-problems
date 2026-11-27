module

public import SolvedProblems.BinaryDiffuseModel
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Tactic.NormNum

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace BinaryDiffuse

/-- Ask for bit zero at the sampled coordinate. A positive reply certifies that
arm; on a negative reply use bit one at the same coordinate. -/
def oneQuery : Strategy Coord
  | 0, _, x => (x, false)
  | _ + 1, h, x => (x, !(h 0))

theorem one_query_exact (μ : Measure Coord) (hn : ∀ x : Coord, μ {x} = 0)
    (U : Set Arm) (hu : Eligible U) : μ (failure oneQuery 1 U) = 0 := by
  classical
  let _ : NullSingletonClass μ := ⟨hn⟩
  rcases hu with rfl | ⟨f,hf,rfl⟩
  · simp [failure]
  apply measure_mono_null _ (hf.measure_zero μ)
  intro x hx
  have lose := hx.2
  cases he : f x with
  | none => exact he
  | some b =>
    exfalso
    apply lose
    have bit : transcript oneQuery (winSet f) x 1 0 = decide (f x = some false) := by
      change Fin.snoc (α := fun _ : Fin 1 => Bool) Fin.elim0 (decide (oneQuery 0 Fin.elim0 x ∈ winSet f)) 0 = _
      rw [Fin.snoc_zero]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rfl
    change f x = some (!(transcript oneQuery (winSet f) x 1 0))
    rw [bit, he]
    cases b <;> simp

private def atoms (μ : Measure Coord) : Set Coord := {x | 0 < μ {x}}

private theorem atoms_countable (μ : Measure Coord) [IsProbabilityMeasure μ] : (atoms μ).Countable := by
  simpa [atoms, id] using (Measure.countable_meas_level_set_pos (μ := μ) (g := id) measurable_id)

private theorem diffuse_of_residual (μ : Measure Coord) [IsProbabilityMeasure μ]
    (h : μ (atoms μ)ᶜ ≠ 0) : DiffuseExists := by
  classical
  let E := (atoms μ)ᶜ
  let ν := (μ E)⁻¹ • μ.restrict E
  refine ⟨ν, ⟨?_⟩, ?_⟩
  · rw [show ν univ = (μ E)⁻¹ * (μ.restrict E) univ from rfl, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel h (measure_ne_top _ _)
  · intro x
    change (μ E)⁻¹ * μ.restrict E {x} = 0
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    by_cases hx : x ∈ E
    · have hz : μ {x} = 0 := by simpa [E, atoms, not_lt] using hx
      rw [singleton_inter_of_mem hx, hz, mul_zero]
    · rw [singleton_inter_of_notMem hx, measure_empty, mul_zero]

/-- Without a diffuse law, every finite-budget randomized strategy fails
almost surely on one of the eligible partial labelings. -/
theorem atom_obstruction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hd : ¬ DiffuseExists) (A : Strategy Ω)
    (hm : ∀ t h, Measurable (A t h)) (m : ℕ) :
    ∃ U : Set Arm, Eligible U ∧ μ (failure A m U) = 1 := by
  classical
  let a (h : Fin m → Bool) (ω : Ω) := first (A m h ω)
  have ha (h : Fin m → Bool) : Measurable (a h) := Measurable.of_discrete.comp (hm m h)
  let ν (h : Fin m → Bool) := μ.map (a h)
  have hp (h : Fin m → Bool) : IsProbabilityMeasure (ν h) :=
    (Measure.isProbabilityMeasure_map_iff (ha h).aemeasurable).2 inferInstance
  let E := ⋃ h : Fin m → Bool, atoms (ν h)
  have cE : E.Countable := countable_iUnion fun h ↦ @atoms_countable (ν h) (hp h)
  have hit (h : Fin m → Bool) : ∀ᵐ ω ∂μ, a h ω ∈ E := by
    have hz : ν h (atoms (ν h))ᶜ = 0 := by
      by_contra hnon
      exact hd (@diffuse_of_residual (ν h) (hp h) hnon)
    rw [show ν h = μ.map (a h) from rfl, Measure.map_apply (ha h) MeasurableSet.of_discrete] at hz
    apply (ae_iff.mpr hz).mono
    exact fun ω hw ↦ mem_iUnion.mpr ⟨h, hw⟩
  let f (x : Coord) : Option Bool := if x ∈ E then none else some false
  have missing : {x | f x = none} = E := by ext; simp [f]
  have outside : ∃ x : Coord, x ∉ E := by
    by_contra! all
    exact not_countable (α := Coord) (countable_univ_iff.mp ((eq_univ_of_forall all) ▸ cE))
  obtain ⟨x,hx⟩ := outside
  have hn : (winSet f).Nonempty := ⟨(x,false), by change f x = some false; simp [f, hx]⟩
  refine ⟨winSet f, Or.inr ⟨f, missing ▸ cE, rfl⟩, ?_⟩
  have hall := ae_all_iff.mpr hit
  have hfull : failure A m (winSet f) =ᵐ[μ] univ := by
    filter_upwards [hall] with ω hw
    refine propext ⟨fun _ ↦ trivial, fun _ ↦ ⟨hn, ?_⟩⟩
    let branch := transcript A (winSet f) ω m
    change f (a branch ω) ≠ some (Prod.snd (A m branch ω))
    dsimp only [f]
    rw [ite_eq_left (hw branch)]
    intro contra
    cases contra
  rw [measure_congr hfull, measure_univ]

/-- Theorem 2. The power-set-measurable partial-label bandit is learnable
exactly when the whole powerset of the interval supports a diffuse law. -/
theorem learnable_iff_diffuse : Learnable ↔ DiffuseExists := by
  constructor
  · intro learn
    by_contra h
    obtain ⟨m, Ω, s, μ, hp, A, hm, hA⟩ := learn (1/2) (by norm_num)
    obtain ⟨U,hU,he⟩ := atom_obstruction μ h A hm m
    have hle := hA U hU
    rw [he] at hle
    norm_num at hle
  · rintro ⟨μ,hp,hn⟩ ε _
    refine ⟨1, Coord, inferInstance, μ, hp, oneQuery, fun _ _ ↦ Measurable.of_discrete, ?_⟩
    intro U hU
    rw [one_query_exact μ hn U hU]
    exact zero_le

end BinaryDiffuse
