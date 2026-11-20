module

public import SolvedProblems.UncountableGenerationPools
public import SolvedProblems.UncountableGenerationUniform
public import Mathlib.Probability.ProductMeasure

@[expose] public section

open MeasureTheory Set Function
open scoped ENNReal
noncomputable section

namespace UncountableGeneration

abbrev Choices (m : ℕ → ℕ) := (i : ℕ) → Fin (m i+1)

def choiceLaw (m : ℕ → ℕ) : Measure (Choices m) := Measure.infinitePi fun i ↦ uniformLaw (m i)

instance choiceLaw_prob (m : ℕ → ℕ) : IsProbabilityMeasure (choiceLaw m) := by
  unfold choiceLaw
  infer_instance

def hitProb (P : Rule) {m : ℕ → ℕ} (t i : ℕ) (z : Choices m) : ℝ≥0∞ :=
  ENNReal.ofReal ((P (sparse z)).real (hit t (poolColumn i (z i))))

private def scope (t i : ℕ) := insert i (Finset.range (t+1))

/-- The round-t hit probability for pool i reads only the current input prefix and choice i. -/
private theorem hitProb_finite {P : Rule} (hc : Causal P) {m : ℕ → ℕ} (t i : ℕ) :
    Measurable[Filtration.piFinset (scope t i)] (hitProb P (m := m) t i) := by
  classical
  let S := scope t i
  let extend (v : (j : S) → Fin (m j+1)) := updateFinset (fun j ↦ (0 : Fin (m j+1))) S v
  let g (v : (j : S) → Fin (m j+1)) := hitProb P t i (extend v)
  have eq : g ∘ S.restrict = hitProb P t i := by
    funext z
    let y := extend (S.restrict z)
    have agree {j : ℕ} (hj : j ∈ S) : y j = z j := by
      simp [y, extend, updateFinset, hj]
    have hpfx : PrefixEq (sparse y) (sparse z) (t+1) :=
      fun j hj ↦ by rw [sparse, sparse, agree (by simp [S, scope, hj])]
    change ENNReal.ofReal ((P (sparse y)).real (hit t (poolColumn i (y i)))) =
      ENNReal.ofReal ((P (sparse z)).real (hit t (poolColumn i (z i))))
    rw [agree (by simp [S, scope])]
    rw [hc _ _ _ hpfx _ (hit_measurable t _) (hit_prefix t (poolColumn i (z i)))]
  rw [← eq]
  exact (measurable_of_countable g).comp (Measurable.of_comap_le le_rfl)

theorem hitProb_measurable {P : Rule} (hc : Causal P) {m : ℕ → ℕ} (t i : ℕ) :
    Measurable (hitProb P (m := m) t i) :=
  (hitProb_finite hc t i).mono (Filtration.piFinset.le _) le_rfl

/-- Integrate first over the i-th coordinate. Under the product law all conditional
distributions of that coordinate are the same finite uniform distribution. -/
theorem mean_hit_le {P : Rule} (hc : Causal P) {m : ℕ → ℕ} {e : ℕ → ℝ}
    (sum_bound : ∀ (z : Choices m) (t i : ℕ),
      (∑ j : Fin (m i+1), (P (sparse (update z i j))).real (hit t (poolColumn i j)))
        ≤ (m i+1 : ℕ) * e i)
    (t i : ℕ) : (∫⁻ z, hitProb P t i z ∂choiceLaw m) ≤ ENNReal.ofReal (e i) := by
  classical
  let μ := fun j ↦ uniformLaw (m j)
  let F := hitProb P (m := m) t i
  let C := ENNReal.ofReal (e i)
  have hm : Measurable F := hitProb_measurable hc t i
  have bound (z : Choices m) : (∫⁻ j, F (update z i j) ∂μ i) ≤ C := by
    rw [uniformLaw_integral]
    simp only [F, hitProb, update_self, ← ENNReal.ofReal_sum_of_nonneg
      (fun _ _ ↦ measureReal_nonneg)]
    have h := ENNReal.ofReal_le_ofReal (sum_bound z t i)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast] at h
    calc
      _ ≤ _ := mul_le_mul_right h _
      _ = C := by simp [C, ← mul_assoc, ENNReal.inv_mul_cancel]
  let S := scope t i
  let seed : Choices m := fun _ ↦ 0
  change (∫⁻ z, F z ∂Measure.infinitePi μ) ≤ C
  rw [lintegral_infinitePi_of_piFinset μ (hitProb_finite hc t i) seed,
    lmarginal_erase' F hm (show i ∈ S by simp [S, scope])]
  unfold lmarginal
  calc
    _ ≤ ∫⁻ _, C ∂Measure.pi (fun j : ↑(S.erase i) ↦ μ j.val) := lintegral_mono fun _ ↦ bound _
    _ = C := by simp

end UncountableGeneration
