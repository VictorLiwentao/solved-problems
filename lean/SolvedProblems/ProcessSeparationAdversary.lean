module

public import SolvedProblems.ProcessSeparationModel
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

namespace ProcessSeparation
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- One of the first 2^t labels has probability at most 2^(-t). -/
private theorem rare {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℕ) (Z : Ω → ℕ) (hm : Measurable Z) :
    ∃ a : ℕ, μ (Z ⁻¹' {a}) ≤ ((2 : ℝ≥0∞)⁻¹)^t := by
  classical
  let n := 2^t
  have hn : 0 < n := by dsimp [n]; positivity
  have hR : ∃ a : ℕ, μ.real (Z ⁻¹' {a}) ≤ (n : ℝ)⁻¹ := by
    by_contra! h
    have sumlt := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hn.ne')
      (fun a (_ : a ∈ Finset.range n) ↦ h a)
    rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,
      mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0),
      sum_measureReal_preimage_singleton _ (fun a _ ↦ hm (measurableSet_singleton a))] at sumlt
    exact (not_lt.mpr measureReal_le_one) sumlt
  obtain ⟨a,ha⟩ := hR
  refine ⟨a,?_⟩
  have he := ENNReal.ofReal_le_ofReal ha
  rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  simpa [n,ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn : 0 < (n:ℝ)),← inv_pow] using he

/-- Eventually wrong at every round implies mistake rate one. -/
private theorem eventually_wrong {p y : Stream} (h : ∀ᶠ t in atTop, p t ≠ y t) :
    Tendsto (loss p y) atTop (𝓝 1) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp h
  let good (T : ℕ) := ((Finset.range T).filter (fun t ↦ p t = y t)).card
  have bound (T : ℕ) : good T ≤ K := by
    apply (Finset.card_le_card (t := Finset.range K) ?_).trans_eq (Finset.card_range K)
    intro t ht
    apply Finset.mem_range.mpr
    exact lt_of_not_ge (fun h ↦ hK _ h (Finset.mem_filter.mp ht).2)
  have total (T : ℕ) : good T + mistakes p y T = T := by
    simpa [good,mistakes] using (Finset.range T).card_filter_add_card_filter_not (fun t ↦ p t=y t)
  have lim : Tendsto (fun T ↦ (good T : ℝ)/T) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity))
      (Eventually.of_forall (fun T ↦ div_le_div_of_nonneg_right
        (show (good T : ℝ) ≤ K by exact_mod_cast bound T) (Nat.cast_nonneg T)))
      (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  have res : Tendsto (fun T ↦ (1:ℝ)-(good T : ℝ)/T) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub lim
  refine res.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have ht : (T:ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have eq : (good T : ℝ) + mistakes p y T = T := by exact_mod_cast total T
  change 1-(good T:ℝ)/T = (mistakes p y T : ℝ)/T
  rw [← div_self ht,← sub_div,← eq]
  ring

/-- The next label is selected using the law of the prediction at the fixed
history, independently of the realized seed. Summability rules out infinitely
many correct predictions. -/
theorem adversarial_stream {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : (t : ℕ) → (Fin t → ℕ) → Ω → ℕ) (hm : ∀ t h, Measurable (R t h)) :
    ∃ y : Stream, ∀ᵐ ω ∂μ, Tendsto
      (loss (fun t ↦ R t (fun i ↦ y i) ω) y) atTop (𝓝 1) := by
  classical
  let step (t : ℕ) (h : Fin t → ℕ) := (rare μ t (R t h) (hm t h)).choose
  let y (t : ℕ) := Nat.strongRecOn t (motive := fun _ ↦ ℕ)
    (fun n prev ↦ step n (fun i ↦ prev i i.isLt))
  have rule (t : ℕ) : y t = step t (fun i ↦ y i) := Nat.strongRecOn_eq _ _
  let correct (t : ℕ) := R t (fun i ↦ y i) ⁻¹' {y t}
  have bound (t : ℕ) : μ (correct t) ≤ ((2:ℝ≥0∞)⁻¹)^t := by
    unfold correct
    conv_lhs => rhs; rhs; rw [rule t]
    exact (rare μ t _ (hm t (fun i ↦ y i))).choose_spec
  have finite : ∑' t, μ (correct t) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum bound)
    rw [ENNReal.tsum_geometric]
    norm_num
  refine ⟨y,?_⟩
  filter_upwards [ae_eventually_notMem (μ:=μ) finite] with ω h
  exact eventually_wrong h

end ProcessSeparation
