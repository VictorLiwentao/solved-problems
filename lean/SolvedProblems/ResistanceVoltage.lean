module

public import SolvedProblems.ResistanceStability

@[expose] public section

open Finset Matrix
namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

/-- The source injects one unit of current and the sink extracts one. -/
noncomputable def demand (i j : V) : V → ℝ := Pi.single i 1 - Pi.single j 1

private theorem lap_const (w : Mat) (t : ℝ) : weightedLap w *ᵥ (fun _ => t) = 0 := by
  ext i
  rw [weightedLap, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
  simp [mulVec, dotProduct, ← sum_mul]

private theorem ground_apply (w : Mat) (W : ℝ) (x : V → ℝ) (i : V) :
    (grounded w W *ᵥ x) i = (weightedLap w *ᵥ x) i + W*(∑ j, x j) := by
  rw [grounded, add_mulVec, Pi.add_apply]
  simp [mulVec, dotProduct, Finset.mul_sum]

private theorem sum_lap (w : Mat) (h : ∀ i j, w i j = w j i) (x : V → ℝ) :
    ∑ i, (weightedLap w *ᵥ x) i = 0 := by
  rw [weightedLap, sub_mulVec]
  simp only [Pi.sub_apply, sum_sub_distrib, mulVec_diagonal]
  apply sub_eq_zero.mpr
  simp only [mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [h j i]

private theorem total_demand (i j : V) : ∑ k, demand i j k = 0 := by
  classical
  simp [demand, Finset.sum_sub_distrib, Pi.single_apply]

private theorem drop_apply (B : Mat) (i j : V) :
    drop B i j = (B *ᵥ demand i j) i - (B *ᵥ demand i j) j := by
  rw [demand, mulVec_sub, mulVec_single_one, mulVec_single_one]
  simp only [drop, Pi.sub_apply, col_apply]
  ring

/-- Every finite connected nonnegatively weighted graph admits a solution to
Kirchhoff's equations for one source and one sink. -/
theorem weighted_kirchhoff (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j)
    (conn : (supportGraph w h).Connected) {W : ℝ} (hw : 0 < W) (i j : V) :
    weightedLap w *ᵥ ((grounded w W)⁻¹ *ᵥ demand i j) = demand i j := by
  let A := grounded w W
  let x := A⁻¹ *ᵥ demand i j
  have pos := grounded_pos w h hn conn hw
  have hu : IsUnit A.det := A.isUnit_iff_isUnit_det.mp pos.isUnit
  have sol : A *ᵥ x = demand i j := by rw [show x = _ from rfl, mulVec_mulVec, A.mul_nonsing_inv hu, one_mulVec]
  have whole : ∑ k, (A *ᵥ x) k = 0 := sol ▸ total_demand i j
  change ∑ k, (grounded w W *ᵥ x) k = 0 at whole
  simp_rw [ground_apply] at whole
  rw [sum_add_distrib, sum_lap w h x, zero_add, sum_const, card_univ, nsmul_eq_mul] at whole
  have : Nonempty V := conn.nonempty
  have nz : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have z := (mul_eq_zero.mp ((mul_eq_zero.mp whole).resolve_left nz)).resolve_left hw.ne'
  ext k
  have s := congrFun sol k
  change (grounded w W *ᵥ x) k = _ at s
  rw [ground_apply,z,mul_zero,add_zero] at s
  exact s

/-- The inverse-matrix reading in the recovery theorem is the voltage drop
for every solution of the unit-current equations, for every positive grounding. -/
theorem weighted_voltage (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j)
    (conn : (supportGraph w h).Connected) {W : ℝ} (hw : 0 < W) (i j : V) (p : V → ℝ)
    (sol : weightedLap w *ᵥ p = demand i j) : weightedResistance w W i j = p i - p j := by
  let A := grounded w W
  have hu : IsUnit A.det := A.isUnit_iff_isUnit_det.mp (grounded_pos w h hn conn hw).isUnit
  have : Nonempty V := conn.nonempty
  have cn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let t := (∑ k, p k)/(Fintype.card V:ℝ)
  let q : V → ℝ := p - fun _ => t
  have z : ∑ k, q k = 0 := by
    simp [q,t,Finset.sum_sub_distrib, mul_div_cancel₀,cn]
  have eq : A *ᵥ q = demand i j := by
    ext k
    rw [show A = grounded w W from rfl, ground_apply,z,mul_zero,add_zero,show q = _ from rfl,
      mulVec_sub, sol, lap_const, sub_zero]
  have qi : A⁻¹ *ᵥ demand i j = q := by rw [← eq, mulVec_mulVec, A.nonsing_inv_mul hu, one_mulVec]
  change drop A⁻¹ i j = _
  rw [drop_apply,qi]
  simp only [q, Pi.sub_apply]; ring

end ResistanceRecovery
