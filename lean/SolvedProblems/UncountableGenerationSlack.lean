module

public import SolvedProblems.UncountableGenerationLottery
import SolvedProblems.UncountableGenerationUniform
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

public section

open Set MeasureTheory Filter
open scoped ENNReal BigOperators

namespace UncountableGeneration

/-- The extra factor t+1 pays for the entire input prefix in the collision estimate. -/
private def size (t : ℕ) := (t+1)*2^t
private abbrev Seeds := (t : ℕ) → Fin (size t+1)
private def height (w : Seeds) (t : ℕ) := (w t).val

private theorem measurable_height : Measurable height := Measurable.of_eval fun t =>
  (measurable_of_countable (fun i : Fin (size t+1) => i.val)).comp (measurable_pi_apply t)

/-- Independent uniform heights eventually avoid the second coordinate of every
word in each observed prefix, almost surely for each fixed input. -/
private theorem heights :
    ∃ ν : Measure Output, IsProbabilityMeasure ν ∧
      ∀ x : Input, ∀ᵐ h ∂ν, ∃ N : ℕ, ∀ t ≥ N, ∀ i ≤ t, h t ≠ (x i).unpair.2 := by
  classical
  let laws (t : ℕ) := uniformLaw (size t)
  let μ : Measure Seeds := Measure.infinitePi laws
  have pl (t : ℕ) : IsProbabilityMeasure (laws t) := uniformLaw_prob _
  have prob : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  refine ⟨μ.map height,(Measure.isProbabilityMeasure_map_iff measurable_height.aemeasurable).mpr prob,?_⟩
  intro x
  let S (t : ℕ) : Finset (Fin (size t + 1)) := Finset.univ.filter fun h =>
    ∃ i : Fin (t+1), h.val = (x i).unpair.2
  let bad (t : ℕ) : Set Seeds := (fun w : Seeds => w t) ⁻¹' (↑(S t) : Set (Fin (size t+1)))
  have card (t : ℕ) : (S t).card ≤ t+1 := by
    let seen := (Finset.univ : Finset (Fin (t+1))).image (fun i : Fin (t+1) => (x i).unpair.2)
    calc
      (S t).card = ((S t).image Fin.val).card := (Finset.card_image_of_injective (S t) Fin.val_injective).symm
      _ ≤ seen.card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨i,eq⟩ := (Finset.mem_filter.mp hh).2
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,eq.symm⟩
      _ ≤ t+1 := by simpa [seen] using
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin (t+1)))) (f := fun i : Fin (t+1) => (x i).unpair.2))
  have mass (t : ℕ) : μ (bad t) = ((size t+1 : ℕ) : ℝ≥0∞)⁻¹ * (S t).card := by
    have hs := (S t).finite_toSet.measurableSet
    have e := Measure.infinitePi_map_eval laws t
    have measureEq := congrArg (fun m : Measure (Fin (size t+1)) => m (S t)) e
    rw [Measure.map_apply (measurable_pi_apply t) hs] at measureEq
    change μ (bad t) = laws t (S t) at measureEq
    rw [measureEq]
    simp [laws,uniformLaw,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul,
      Measure.dirac_apply' _ hs,Set.indicator_apply]
  have bound (t : ℕ) : μ (bad t) ≤ ((2 : ℝ≥0∞)⁻¹)^t := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
    rw [mass]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    have count : (S t).card * 2^t ≤ size t + 1 :=
      Nat.le_succ_of_le (Nat.mul_le_mul_right _ (card t))
    have count' : ((S t).card : ℝ) * 2^t ≤ ((size t+1 : ℕ) : ℝ) := by
      exact_mod_cast count
    have denom : (0 : ℝ) < ((size t+1 : ℕ) : ℝ) := by positivity
    have powpos : (0 : ℝ) < 2^t := by positivity
    have h : ((S t).card : ℝ) / ((size t+1 : ℕ) : ℝ) ≤ 1 / (2:ℝ)^t :=
      (div_le_div_iff₀ denom powpos).mpr (by simpa using count')
    simpa only [div_eq_mul_inv, one_mul, inv_pow, mul_comm] using h
  have finite : ∑' t, μ (bad t) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum bound)
    rw [ENNReal.tsum_geometric]
    norm_num
  have ev := ae_eventually_notMem (μ:=μ) finite
  have mapped : ∀ᵐ w ∂μ, ∃ N : ℕ, ∀ t ≥ N, ∀ i ≤ t, height w t ≠ (x i).unpair.2 := by
    filter_upwards [ev] with w hw
    obtain ⟨N,hN⟩ := eventually_atTop.mp hw
    refine ⟨N,fun t ht i hi eq => hN t ht ?_⟩
    change w t ∈ S t
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨⟨i, by omega⟩, eq⟩
  apply (ae_map_iff measurable_height.aemeasurable ?_).mpr mapped
  have rep : {h : Output | ∃ N : ℕ, ∀ t ≥ N, ∀ i ≤ t, h t ≠ (x i).unpair.2} =
      ⋃ N : ℕ, ⋂ t : {t : ℕ // N ≤ t}, ⋂ i : Fin (t.val+1), {h : Output | h t.val ≠ (x i).unpair.2} := by
    ext h; simp [Fin.forall_iff]
  rw [rep]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
    (measurableSet_eq_fun (measurable_pi_apply t.val) (measurable_const (a := (x i).unpair.2))).compl

/-- Any positive additive privacy allowance suffices for almost-sure eventual generation
on every enumeration of every nonempty union of columns. -/
theorem positive_slack (δ : ℝ) (hδ : 0 < δ) : ∃ P : Rule, ProbLaw P ∧ Causal P ∧
    PrivateWith P (fun p ↦ p + δ) ∧ ∀ A : Set ℕ, A.Nonempty → ∀ x, Valid A x →
      (P x).real (Success A x) = 1 := by
  obtain ⟨ν,prob,fresh⟩ := heights
  exact lottery_of_heights ν fresh δ hδ

end UncountableGeneration
