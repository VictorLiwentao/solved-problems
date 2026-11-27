module

public import SolvedProblems.EMXUniform
public import SolvedProblems.EMXCounting
public import SolvedProblems.EMXCompressionSize
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace EMX

open Set MeasureTheory
open scoped ENNReal Classical

def budget (s : ℕ) := slots s * (s+1)^3

def stage (m : ℕ) := Nat.findGreatest (fun s => budget s ≤ m) m

noncomputable def learner : Learner := fun m xs => stageLearner (stage m) m xs

theorem learnable : Learnable := by
  refine ⟨learner, ?_⟩
  intro ε δ hε hδ
  obtain ⟨s₀, hs₀⟩ := exists_nat_gt (max (3/ε) (1/δ))
  have herr : 3 < ε * (s₀+1:ℝ) := by
    have hs := (le_max_left (3/ε) (1/δ)).trans_lt hs₀
    have := (div_lt_iff₀ hε).mp hs
    linarith
  have hconf : 1 < δ * (s₀+1:ℝ) := by
    have hs := (le_max_right (3/ε) (1/δ)).trans_lt hs₀
    have := (div_lt_iff₀ hδ).mp hs
    linarith
  refine ⟨max (budget s₀) (s₀+1), ?_⟩
  intro m hm μ hμ
  let _ := hμ
  let s := stage m
  have base : budget s₀ ≤ m := (le_max_left ..).trans hm
  have sb : s₀+1 ≤ m := (le_max_right ..).trans hm
  have sm : 0 < m := by omega
  have hs : s₀ ≤ s := Nat.le_findGreatest (P := fun j => budget j ≤ m) (by omega) base
  have budgetLe : budget s ≤ m := Nat.findGreatest_spec (P := fun j => budget j ≤ m) (by omega) base
  have hsub : (s₀ : ℝ) ≤ s := by exact_mod_cast hs
  have hden : 0 < (s : ℝ)+1 := by positivity
  have herror : (3 : ℝ)/(s+1) ≤ ε := (div_le_iff₀ hden).mpr
    (herr.le.trans (mul_le_mul_of_nonneg_left (by linarith) hε.le))
  have hconfidence : (1 : ℝ)/(s+1) ≤ δ := (div_le_iff₀ hden).mpr
    (hconf.le.trans (mul_le_mul_of_nonneg_left (by linarith) hδ.le))
  have hr : (slots s : ℝ)*((s:ℝ)+1)^3 ≤ m := by exact_mod_cast budgetLe
  have hcalc : (slots s : ℝ)/((m:ℝ)*(1/(s+1:ℝ))^2) ≤ 1/(s+1:ℝ) := by
    have hm' : (0:ℝ)<m := by exact_mod_cast sm
    field_simp
    nlinarith [hr]
  calc
    _ ≤ Measure.pi (fun _ : Fin m => μ) (deficitEvent (stageLearner s) μ m (3/(s+1:ℝ))) := by
      apply measure_mono
      rintro xs ⟨h, hh⟩
      exact ⟨h,(add_le_add le_rfl herror).trans_lt hh⟩
    _ ≤ _ := stage_bound s μ sm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hcalc.trans hconfidence)

/-- The paper’s proper EMX versus bounded monotone compression separation.
The points and hypotheses are countable, each support is finite, one learner
works for all IID laws, and each bounded decoder fails even at one fixed length. -/
theorem separation : Countable Point ∧ Countable Hyp ∧ Learnable ∧
    ∀ d a : ℕ, ∃ m : ℕ, ∀ D : Fin a → Message Point d → Hyp, ¬Reconstructs d a m D :=
  ⟨inferInstance, inferInstance, learnable, noBoundedCompression⟩

end EMX
