module

public import SolvedProblems.ResistanceWeighted

@[expose] public section

open Finset Matrix
open scoped MatrixOrder

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

/-- The voltage drop between i and j for the Green matrix H and the
unit demand that injects current at i and extracts it at j. -/
def drop (H : Mat) (i j : V) : ℝ := H i i + H j j - H i j - H j i

noncomputable def weightedResistance (w : Mat) (W : ℝ) (i j : V) : ℝ :=
  drop (grounded w W)⁻¹ i j

private theorem trace_lap (d H : Mat) (hs : ∀ i j, d i j = d j i) :
    2*(weightedLap d*H).trace = ∑ i, ∑ j, d i j * drop H i j := by
  have swap (f : V → V → ℝ) :
      (∑ i, ∑ j, d i j*f j i) = ∑ i, ∑ j, d i j*f i j := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hs j i]
  have base : (weightedLap d*H).trace =
      (∑ i, ∑ j, d i j * H i i) - ∑ i, ∑ j, d i j * H j i := by
    rw [weightedLap, sub_mul, trace_sub]
    congr 1
    · unfold trace
      apply sum_congr rfl
      intro i _
      simp [diagonal_mul, Finset.sum_mul]
  have sdiag := swap (fun i _ => H i i)
  have soff := swap H
  rw [base]
  simp only [drop, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sdiag, soff]
  ring

private theorem frobenius (d : Mat) (hs : ∀ i j, d i j = d j i) (hz : ∀ i, d i i = 0) :
    (∑ i, ∑ j, (d i j)^2) ≤ (weightedLap d*weightedLap d).trace := by
  unfold Matrix.trace
  apply sum_le_sum
  intro i _
  change _ ≤ ∑ j, weightedLap d i j * weightedLap d j i
  apply sum_le_sum
  intro j _
  by_cases e : i=j
  · subst j
    simpa only [hz, zero_pow (by decide : 2 ≠ 0)] using
      (mul_self_nonneg (weightedLap d i i))
  · simp [weightedLap, e, Ne.symm e, ← hs i j, sq]

/-- Exact identifiability for arbitrary finite conductance levels separated by Δ.
Pairs outside the measurement set have the same known weight in both graphs. -/
theorem noisy_identifiability (u v : Mat) (W Δ η : ℝ) (U : V → V → Prop) (y : V → V → ℝ)
    (hu : ∀ i j, u i j = u j i) (hv : ∀ i j, v i j = v j i)
    (zu : ∀ i, u i i = 0) (zv : ∀ i, v i i = 0)
    (un : ∀ i j, 0 ≤ u i j) (vn : ∀ i j, 0 ≤ v i j)
    (ub : ∀ i j, u i j ≤ W) (vb : ∀ i j, v i j ≤ W)
    (cu : (supportGraph u hu).Connected) (cv : (supportGraph v hv).Connected)
    (hW : 0 < W) (gap : ∀ i j, u i j ≠ v i j → Δ ≤ |u i j - v i j|)
    (known : ∀ i j, ¬U i j → u i j = v i j)
    (yu : ∀ i j, U i j → |weightedResistance u W i j - y i j| ≤ η)
    (yv : ∀ i j, U i j → |weightedResistance v W i j - y i j| ≤ η)
    (hη : η < Δ/((Fintype.card V:ℝ)*W)^2) : u = v := by
  classical
  have : Nonempty V := cu.nonempty
  let m := (Fintype.card V:ℝ)*W
  have hm : 0 < m := mul_pos (by exact_mod_cast Fintype.card_pos) hW
  let d := u-v
  have ds (i j : V) : d i j = d j i := by dsimp [d]; rw [hu i j,hv i j]
  have dz (i : V) : d i i = 0 := by simp [d,zu,zv]
  let A := grounded u W
  let C := grounded v W
  have bd : A-C = weightedLap d := grounded_sub _ _ _
  have inv := inverse_trace_bound A C (grounded_pos _ hu un cu hW) (grounded_pos _ hv vn cv hW)
    hm (grounded_le _ hu ub) (grounded_le _ hv vb)
  rw [bd] at inv
  have core := (mul_le_mul_of_nonneg_left (frobenius d ds dz) (sq_nonneg m⁻¹)).trans inv
  have bound (i j : V) :
      d i j * drop (C⁻¹-A⁻¹) i j ≤ (2*η)*|d i j| := by
    by_cases eq : u i j = v i j
    · simp [d,eq]
    have unknown : U i j := by by_contra no; exact eq (known i j no)
    have yd := yu i j unknown
    have yc := yv i j unknown
    have hh : drop (C⁻¹-A⁻¹) i j = weightedResistance v W i j - weightedResistance u W i j := by
      simp only [drop, weightedResistance, C, A, Matrix.sub_apply]; ring
    rw [hh, mul_comm (2*η)]
    apply (le_abs_self _).trans
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hh := abs_sub_le (weightedResistance v W i j) (y i j) (weightedResistance u W i j)
    rw [abs_sub_comm (y i j)] at hh
    linarith
  have total := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun j _ => bound i j))
  rw [← trace_lap d _ ds] at total
  simp only [← Finset.mul_sum] at total
  have gapSum : Δ*(∑ i, ∑ j, |d i j|) ≤ ∑ i, ∑ j, (d i j)^2 := by
    simp only [Finset.mul_sum]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    by_cases eq : u i j = v i j
    · simp [d,eq]
    · have hg : Δ ≤ |d i j| := gap i j eq
      simpa only [← sq, sq_abs] using (mul_le_mul_of_nonneg_right hg (abs_nonneg (d i j)))
  by_contra neq
  have pos : 0 < ∑ i, ∑ j, |d i j| := by
    by_contra! no
    have nn (i : V) := sum_nonneg (s := univ) fun j _ => abs_nonneg (d i j)
    have z := le_antisymm no (sum_nonneg fun i _ => nn i)
    apply neq
    ext i j
    have row := (sum_eq_zero_iff_of_nonneg fun k _ => nn k).mp z i (mem_univ _)
    have val := (sum_eq_zero_iff_of_nonneg fun k _ => abs_nonneg (d i k)).mp row j (mem_univ _)
    exact sub_eq_zero.mp (abs_eq_zero.mp val)
  have hη' : η < m⁻¹^2*Δ := by simpa only [div_eq_inv_mul, inv_pow] using hη
  have strict := mul_lt_mul_of_pos_right hη' pos
  have lower := mul_le_mul_of_nonneg_left gapSum (sq_nonneg m⁻¹)
  linarith only [strict, total, core, lower]

end ResistanceRecovery
