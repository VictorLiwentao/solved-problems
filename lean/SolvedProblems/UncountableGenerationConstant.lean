module

public import SolvedProblems.UncountableGenerationRenyiModel
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.Tactic.Linarith

@[expose] public section

open Set MeasureTheory Function
namespace UncountableGeneration

/-- The constant rule is admissible for all nonnegative budgets in both privacy models.
An injective enumeration of column one witnesses its zero worst-case utility. -/
theorem zero_attainable : ∃ P : Rule, ProbLaw P ∧ Causal P ∧
    (∀ ε : ℝ, 0 ≤ ε → PrivateWith P (fun p ↦ Real.exp ε * p)) ∧
    (∀ α D : ℝ, 1 < α → 0 ≤ D → RenyiBudget P α D) ∧ ZeroUtility P := by
  classical
  let u : Output := fun _ ↦ 0
  let P : Rule := fun _ ↦ Measure.dirac u
  refine ⟨P, fun _ ↦ ⟨Measure.dirac_apply_of_mem (Set.mem_univ u)⟩,
    fun _ _ _ _ _ _ _ ↦ rfl, ?_, ?_, ?_⟩
  · intro ε hε x y _ E _
    simpa [P] using mul_le_mul_of_nonneg_right (Real.one_le_exp hε)
      (measureReal_nonneg (μ := Measure.dirac u) (s := E))
  · intro α D hα hD x y _
    refine ⟨Measure.AbsolutelyContinuous.rfl, ?_⟩
    intro n E hdis hm
    let S := Finset.univ.filter fun j : Fin n ↦ u ∈ E j
    have hone : S.card ≤ 1 := Finset.card_le_one_iff.mpr fun {a b} ha hb ↦ by
      by_contra hab
      exact Set.disjoint_left.mp (hdis hab) (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have eq (j : Fin n) :
        ((P x).real (E j)) ^ α / ((P y).real (E j)) ^ (α-1) =
        if u ∈ E j then (1 : ℝ) else 0 := by
      by_cases hj : u ∈ E j
      · simp [P, Measure.real, Measure.dirac_apply' _ (hm j), hj]
      · simp [P, Measure.real, Measure.dirac_apply' _ (hm j), hj, Real.zero_rpow (by linarith : α ≠ 0)]
    simp_rw [eq]
    calc
      _ = (S.card : ℝ) := by simp [S]
      _ ≤ 1 := by exact_mod_cast hone
      _ ≤ _ := Real.one_le_exp (mul_nonneg (by linarith) hD)
  · intro η hη
    let A : Set ℕ := {1}
    let x : Input := fun n ↦ Nat.pair 1 n
    have hj : Injective x := fun _ _ h ↦ (Nat.pair_eq_pair.mp h).2
    have hv : Valid A x := by
      ext w
      constructor
      · rintro ⟨k, rfl⟩
        simp [x, Language, A, col]
      · intro hw
        have hcol : w.unpair.1 = 1 := hw
        exact ⟨w.unpair.2, by simpa only [x, ← hcol] using Nat.pair_unpair w⟩
    have fail : u ∉ Success A x := by
      rintro ⟨N, hN⟩
      have := (hN N le_rfl).1
      simp [A, u, col] at this
    refine ⟨A, ⟨1,rfl⟩, x, hj, hv, ?_⟩
    simpa [P, Measure.real, Measure.dirac_apply, fail] using hη

end UncountableGeneration
