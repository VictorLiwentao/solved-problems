module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

open Finset

namespace SphericalEntropy

noncomputable def taylor (k : ℕ) (u : ℝ) := ∑ j ∈ range k, u^j / j.factorial

theorem taylor_error {α u : ℝ} (hu : |u|≤α) (k : ℕ) :
    |Real.exp u - taylor k u| ≤ α^k/(k.factorial:ℝ)*Real.exp α := by
  have ha : 0≤α := (abs_nonneg u).trans hu
  have hs (x:ℝ) : HasSum (fun n : ℕ => x^n/(n.factorial:ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hu' := (hs u).summable.sum_add_tsum_nat_add k
  rw [(hs u).tsum_eq] at hu'
  have htail : Real.exp u - taylor k u = ∑' i : ℕ, u^(i+k)/((i+k).factorial:ℝ) := by unfold taylor; linarith
  rw [htail,←Real.norm_eq_abs]
  let m (i : ℕ) := α^k/(k.factorial:ℝ)*(α^i/(i.factorial:ℝ))
  have hm : HasSum m (α^k/(k.factorial:ℝ)*Real.exp α) := (hs α).mul_left _
  have hb (i : ℕ) : ‖u^(i+k)/((i+k).factorial:ℝ)‖ ≤ m i := by
    have hden : |((i+k).factorial:ℝ)| = ((i+k).factorial:ℝ) := abs_of_nonneg (by positivity)
    rw [Real.norm_eq_abs,abs_div,abs_pow,hden]
    have hfac : (i.factorial:ℝ)*k.factorial ≤ (i+k).factorial := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add i k)
    have hpower := pow_le_pow_left₀ (abs_nonneg u) hu (i+k)
    calc _ ≤ α^(i+k)/((i+k).factorial:ℝ) := div_le_div_of_nonneg_right hpower (by positivity)
         _ ≤ α^(i+k)/((i.factorial:ℝ)*k.factorial) := div_le_div_of_nonneg_left (pow_nonneg ha _) (by positivity) hfac
         _ = _ := by rw [pow_add]; unfold m; ring
  have hnorm := hm.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hb hm.summable).trans_eq hm.tsum_eq)

end SphericalEntropy
