module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow

public section

namespace SelectedRate

/-- For positive accuracy and confidence parameters, the selected-disagreement
sample bound is eventually below the confidence parameter. -/
theorem decays {ε δ : ℝ} (hε : 0 < ε) (hε' : ε < 1) (hδ : 0 < δ) :
    ∃ N : Nat, ∀ m ≥ N, 2 * (1-ε)^m + (m : ℝ) * (1-ε)^(m-1) < δ := by
  -- Bernoulli bounds ε/2 times the sample bound by the geometric sequence (1 − ε/2)^m.
  let q : ℝ := 1-ε
  let b : ℝ := ε/2
  have hq : 0 ≤ q := (sub_pos.mpr hε').le
  have hb : 0 < b := half_pos hε
  have hsmall : q+b < 1 := by
    calc
      q+b < q+ε := add_lt_add_right (half_lt_self hε) _
      _ = 1 := sub_add_cancel _ _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hδ hb) hsmall
  refine ⟨N, fun m hm => ?_⟩
  have hpower := pow_le_pow_of_le_one (add_nonneg hq hb.le) hsmall.le hm
  have hbern := pow_add_mul_le_add_pow hq (add_nonneg (mul_nonneg (zero_le_two) hq) hb.le) m
  have hfirst : (2 * q^m) * b ≤ q^m := by
    calc
      (2 * q^m) * b = (b+b) * q^m := by
        rw [← two_mul]
        ac_rfl
      _ = ε * q^m := by rw [show b+b = ε from add_halves ε]
      _ ≤ 1 * q^m := mul_le_mul_of_nonneg_right hε'.le (pow_nonneg hq _)
      _ = q^m := one_mul _
  apply lt_of_mul_lt_mul_right _ hb.le
  change (2 * q^m + (m : ℝ) * q^(m-1)) * b < δ*b
  rw [add_mul]
  exact ((add_le_add_left hfirst _).trans hbern).trans_lt (hpower.trans_lt hN)

end SelectedRate
