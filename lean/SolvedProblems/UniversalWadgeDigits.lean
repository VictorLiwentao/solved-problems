module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace UniversalWadge

open Set Filter
open scoped Classical Topology

abbrev Cantor := ℕ → Bool
abbrev Tests := ℕ → Cantor
abbrev Circle := AddCircle (1:ℝ)

def level (n : ℕ) := (n+2)^2

def character (n : ℕ) := 2^level n

noncomputable def dyad (j : ℕ) := (1/2:ℝ)^j

@[simp] theorem dyad_add (i j) : dyad (i+j) = dyad i * dyad j := pow_add ..

theorem dyad_pos (i) : 0 < dyad i := by unfold dyad;positivity

theorem dyad_antitone : Antitone dyad := fun _ _ h => pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem dyad_summable : Summable dyad := summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem dyad_sum : ∑' i, dyad i = 2 := by
  change (∑' i : ℕ, (1/2:ℝ)^i) = 2
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)];norm_num

theorem dyad_limit : Tendsto dyad atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem char_dyad (n : ℕ) : (character n:ℝ)*dyad (level n) = 1 := by
  unfold character dyad;push_cast;rw [← mul_pow];norm_num

noncomputable def bitValue (a : Tests) (j n : ℕ) := if a j n = true then dyad (j+2) else 0

noncomputable def digit (a : Tests) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (n+1) => bitValue a j.val n)

theorem digit_realized (a : Tests) (n) : ∃ j : Fin (n+1), digit a n = bitValue a j.val n := by
  obtain ⟨i,_,h⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun j : Fin (n+1) => bitValue a j.val n)
  exact ⟨i,h⟩

theorem digit_ge {a : Tests} {j n} (hj : j≤n) (hit : a j n=true) : dyad (j+2) ≤ digit a n := by
  have bound : bitValue a j n ≤ digit a n := Finset.le_sup' (fun i : Fin (n+1) => bitValue a i.val n) (Finset.mem_univ (⟨j,Nat.lt_succ_of_le hj⟩ : Fin (n+1)))
  simpa only [bitValue,hit,↓reduceIte] using bound

theorem digit_range (a : Tests) (n) : 0 ≤ digit a n ∧ digit a n ≤ 1/4 := by
  obtain ⟨j,r⟩ := digit_realized a n
  rw [r,bitValue];split
  · exact ⟨(dyad_pos _).le, (dyad_antitone (show 2≤j.val+2 by omega)).trans (by norm_num [dyad])⟩
  · norm_num

theorem digit_continuous (n) : Continuous (fun a => digit a n) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro j _
  exact (continuous_of_discreteTopology (f := fun b : Bool => if b=true then dyad (j.val+2) else 0)).comp
    ((continuous_apply n).comp (continuous_apply j.val))

noncomputable def term (a : Tests) (n : ℕ) := dyad (level n)*digit a n

theorem term_bound (a : Tests) (n : ℕ) : 0 ≤ term a n ∧ term a n ≤ dyad n := by
  have range := digit_range a n
  refine ⟨mul_nonneg (dyad_pos _).le range.1, ?_⟩
  apply (mul_le_of_le_one_right (dyad_pos _).le (by linarith : digit a n ≤ 1)).trans
  apply dyad_antitone;unfold level;nlinarith

theorem term_summable (a : Tests) : Summable (term a) :=
  Summable.of_nonneg_of_le (fun n => (term_bound a n).1) (fun n => (term_bound a n).2) dyad_summable

noncomputable def code (a : Tests) : Circle := ((∑' n, term a n : ℝ) : Circle)

theorem code_continuous : Continuous code :=
  (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_tsum (fun n => continuous_const.mul (digit_continuous n))
    dyad_summable (fun n a => by rw [Real.norm_eq_abs,abs_of_nonneg (term_bound a n).1];exact (term_bound a n).2))

end UniversalWadge
