module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

open Matrix
open scoped MatrixOrder

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

private theorem trace_product_nonneg {A B : Mat} (ha : A.PosSemidef) (hb : B.PosSemidef) :
    0 ≤ (A*B).trace := by
  obtain ⟨X, hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha.nonneg
  rw [hx, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle B]
  simpa only [mul_assoc] using (hb.mul_mul_conjTranspose_same X).trace_nonneg

private theorem inverse_lower {A : Mat} (ha : A.PosDef) {m : ℝ} (hm : 0 < m)
    (h : A ≤ m • (1 : Mat)) : (m⁻¹ • (1 : Mat)) ≤ A⁻¹ := by
  have hu := ha.isUnit
  have hl : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ (A.isUnit_iff_isUnit_det.mp hu)
  have hr : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (A.isUnit_iff_isUnit_det.mp hu)
  have hd := (Matrix.le_iff.mp h).nonneg
  have hc : Commute A⁻¹ (m • (1 : Mat) - A) := by
    show _ * _ = _ * _
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul, hl, hr]
  have hp := Commute.mul_nonneg ha.posSemidef.inv.nonneg hd hc
  rw [mul_sub, Matrix.mul_smul, mul_one, hl] at hp
  have hps := (Matrix.nonneg_iff_posSemidef.mp hp).smul (inv_nonneg.mpr hm.le)
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hm.ne', one_smul] at hps
  exact Matrix.le_iff.mpr hps

/-- Strong monotonicity for the inverse of two positive definite regularized
Laplacians bounded above by the same scalar multiple of the identity. -/
theorem inverse_trace_bound (A C : Mat) (ha : A.PosDef) (hc : C.PosDef)
    {m : ℝ} (hm : 0 < m) (hA : A ≤ m • (1 : Mat)) (hC : C ≤ m • (1 : Mat)) :
    m⁻¹ ^ 2 * ((A-C)*(A-C)).trace ≤ ((A-C)*(C⁻¹-A⁻¹)).trace := by
  let B := A-C
  let r := m⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr hm.le
  have hb : Bᴴ = B := (ha.isHermitian.sub hc.isHermitian).eq
  have hs := Matrix.le_iff.mp (inverse_lower ha hm hA)
  have ht := Matrix.le_iff.mp (inverse_lower hc hm hC)
  have hba : (B*A⁻¹*B).PosSemidef := by
    simpa only [hb] using ha.posSemidef.inv.mul_mul_conjTranspose_same B
  have h₁ := trace_product_nonneg hba ht
  have h₂ := (hs.mul_mul_conjTranspose_same B).trace_nonneg
  rw [hb, mul_sub B A⁻¹, sub_mul (B*A⁻¹), Matrix.mul_smul, mul_one, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h₂
  rw [mul_sub (B*A⁻¹*B) C⁻¹, Matrix.mul_smul, mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h₁
  have hi : C⁻¹ - A⁻¹ = A⁻¹*B*C⁻¹ := by
    dsimp [B]
    rw [mul_sub, sub_mul, Matrix.nonsing_inv_mul _ (A.isUnit_iff_isUnit_det.mp ha.isUnit),
      one_mul, mul_assoc, Matrix.mul_nonsing_inv _ (C.isUnit_iff_isUnit_det.mp hc.isUnit), mul_one]
  rw [hi]
  change r^2 * (B*B).trace ≤ (B*(A⁻¹*B*C⁻¹)).trace
  rw [← mul_assoc B, ← mul_assoc B]
  dsimp [r] at *
  nlinarith [mul_nonneg hr h₂]

end ResistanceRecovery
