module

public import SolvedProblems.BinaryBanditModel
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

open Set MeasureTheory Filter
open scoped Cardinal unitInterval ENNReal Topology

namespace BinaryBandit

private theorem measurable_play {Ω : Type*} [MeasurableSpace Ω] (A : Strategy Ω)
    (hm : ∀ t h, Measurable (A t h)) (U : Set Arm) (hu : MeasurableSet U) (m : ℕ) :
    Measurable fun ω ↦ A m (transcript A U ω m) ω := by
  classical
  have step (n : ℕ) : Measurable (fun p : Ω × (Fin n → Bool) ↦ A n p.2 p.1) :=
    measurable_from_prod_countable_left (hm n)
  have hist (n : ℕ) : Measurable (fun ω ↦ transcript A U ω n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      have eval := (step n).comp (measurable_id.prodMk ih)
      have bit : Measurable (fun ω ↦ decide (A n (transcript A U ω n) ω ∈ U)) := by
        have eq (ω : Ω) : decide (A n (transcript A U ω n) ω ∈ U) =
            (if A n (transcript A U ω n) ω ∈ U then true else false) := by split <;> simp_all
        simp_rw [eq]
        exact Measurable.ite (hu.preimage eval) measurable_const measurable_const
      exact (measurable_of_countable (fun p : (Fin n → Bool) × Bool ↦ (Fin.snoc p.1 p.2 : Fin (n+1) → Bool))).comp
        (ih.prodMk bit)
  exact (step m).comp (measurable_id.prodMk (hist m))

/-- Every failure event in the definition of learning is measurable. -/
theorem failure_measurable {Ω : Type*} [MeasurableSpace Ω] (A : Strategy Ω)
    (hm : ∀ t h, Measurable (A t h)) (m : ℕ) (U : Set Arm) (hu : Eligible U) :
    MeasurableSet (failure A m U) := by
  rcases hu with rfl | ⟨hn, ho, _⟩
  · simp [failure]
  have h := ho.measurableSet.compl.preimage (measurable_play A hm U ho.measurableSet m)
  simpa [failure, hn, preimage, compl_def] using h

/-- Failure of CH makes each eligible closed losing set countable, so that the
uniform arm wins almost surely for each nonzero target without querying it. -/
theorem uniform_zero_queries (hc : ℵ₁ < (𝔠 : Cardinal.{0})) (U : Set Arm)
    (h : Eligible U) : volume (failure (fun _ _ (ω : Arm) ↦ ω) 0 U) = 0 := by
  rcases h with rfl | ⟨hn, ho, hsmall⟩
  · simp [failure]
  have hcoun : Uᶜ.Countable := by
    by_contra hunc
    obtain ⟨f, hr, _, hf⟩ := ho.isClosed_compl.exists_nat_bool_injection_of_not_countable hunc
    let g (a : ℕ → Bool) : ↥(Uᶜ) := ⟨f a, hr ⟨a,rfl⟩⟩
    have hg : Function.Injective g := fun x y he ↦ hf (congrArg Subtype.val he)
    have lower := Cardinal.mk_le_of_injective hg
    have hcard : #(ℕ → Bool) = (𝔠 : Cardinal.{0}) := by simp
    rw [hcard] at lower
    exact hc.not_ge (lower.trans hsmall)
  have he : failure (fun _ _ (ω : Arm) ↦ ω) 0 U = Uᶜ := by ext x; simp [failure, hn]
  rw [he]
  exact hcoun.measure_zero _

/-- Nested nonempty open sets with empty intersection. -/
private def win (n : ℕ) : Set Arm := {u | 0 < u.val ∧ u.val < 1 / (n + 1 : ℝ)}

private theorem win_open (n : ℕ) : IsOpen (win n) :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

private theorem win_nonempty (n : ℕ) : (win n).Nonempty := by
  have hp : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  have hu : 1 / (n + 1 : ℝ) ≤ 1 := by
    apply div_le_one_of_le₀
    · linarith [Nat.cast_nonneg (α := ℝ) n]
    · positivity
  exact ⟨⟨(1 / (n + 1 : ℝ))/2, by constructor <;> linarith⟩, by change 0 < _ ∧ _ < _; constructor <;> linarith⟩

private theorem win_antitone : Antitone win := by
  intro i j hij x hx
  exact ⟨hx.1, lt_of_lt_of_le hx.2 (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij))⟩

private theorem leaves_win (u : Arm) : ∀ᶠ n in atTop, u ∉ win n := by
  by_cases h : 0 < u.val
  · obtain ⟨n,hn⟩ := exists_nat_one_div_lt h
    exact eventually_atTop.2 ⟨n, fun j hj hmem ↦ (not_lt_of_ge (le_of_lt hn)) (win_antitone hj hmem).2⟩
  · exact Eventually.of_forall fun _ hmem ↦ h hmem.1

/-- A bound on the number of binary queries leaves finitely many possible
outputs for each random seed. Some nonempty open target makes the error larger
than any fixed threshold below one. This includes arbitrary shared randomness. -/
theorem open_target_lower_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Strategy Ω) (m : ℕ) {δ : ℝ≥0∞} (hδ : δ < 1) :
    ∃ U : Set Arm, U.Nonempty ∧ IsOpen U ∧ δ < μ (failure A m U) := by
  classical
  let safe (n : ℕ) : Set Ω := {ω | ∀ h : Fin m → Bool, A m h ω ∉ win n}
  have mono : Monotone safe := fun _ _ hij _ hx h hm ↦ hx h (win_antitone hij hm)
  have full : ⋃ n, safe n = univ := by
    apply eq_univ_of_forall
    intro ω
    have h : ∀ᶠ n in atTop, ∀ h : Fin m → Bool, A m h ω ∉ win n :=
      (Filter.eventually_all).mpr fun h ↦ leaves_win (A m h ω)
    obtain ⟨n,hn⟩ := h.exists
    exact mem_iUnion.mpr ⟨n, hn⟩
  have total : (⨆ n, μ (safe n)) = 1 := by rw [← mono.measure_iUnion, full, measure_univ]
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp (total ▸ hδ : δ < ⨆ n, μ (safe n))
  refine ⟨win n, win_nonempty n, win_open n, lt_of_lt_of_le hn (measure_mono ?_)⟩
  exact fun ω h ↦ ⟨win_nonempty n, h (transcript A (win n) ω m)⟩

/-- Hanneke and Yang's binary-bandit question: the open-target instance in
Theorem 1 is learnable exactly when the continuum exceeds aleph one. -/
theorem learnable_iff_not_CH : Learnable ↔ ℵ₁ < (𝔠 : Cardinal.{0}) := by
  constructor
  · intro learns
    by_contra! hc
    obtain ⟨m, Ω, s, μ, hp, A, _, hA⟩ := learns (1/2) (by norm_num)
    obtain ⟨U, hU, ho, hbad⟩ := open_target_lower_bound μ A m (δ := 1/2) (by norm_num)
    have eligible : Eligible U := Or.inr ⟨hU, ho, (Cardinal.mk_set_le _).trans (by simpa [Arm] using hc)⟩
    exact hbad.not_ge (hA U eligible)
  · intro hc ε _
    refine ⟨0, Arm, inferInstance, volume, inferInstance, fun _ _ ω ↦ ω, fun _ _ ↦ measurable_id, ?_⟩
    intro U hU
    rw [uniform_zero_queries hc U hU]
    exact zero_le

end BinaryBandit
