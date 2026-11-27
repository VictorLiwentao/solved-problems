module

public import SolvedProblems.ResistanceCoercivity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

open Finset Matrix
open scoped MatrixOrder

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

noncomputable def weightedLap (w : Mat) : Mat := diagonal (fun i => ∑ j, w i j) - w

/-- Ground the constant eigenspace by assigning the constant matrix value W.
Its quadratic form vanishes on every difference of two coordinate vectors. -/
noncomputable def grounded (w : Mat) (W : ℝ) : Mat := weightedLap w + Matrix.of (fun _ _ => W)

private theorem lap_sub (u v : Mat) : weightedLap (u-v) = weightedLap u - weightedLap v := by
  ext i j
  by_cases h : i=j <;> simp [weightedLap, h, Finset.sum_sub_distrib] <;> ring

theorem grounded_sub (u v : Mat) (W : ℝ) : grounded u W - grounded v W = weightedLap (u-v) := by
  rw [grounded, grounded, lap_sub, add_sub_add_right_eq_sub]

private theorem lap_symm (w : Mat) (h : ∀ i j, w i j = w j i) : (weightedLap w).IsHermitian := by
  ext i j
  by_cases e : i=j <;> simp [weightedLap, e, Ne.symm, h j i, Matrix.conjTranspose_apply]

private theorem quad_lap (w : Mat) (h : ∀ i j, w i j = w j i) (x : V → ℝ) :
    2 * (star x ⬝ᵥ (weightedLap w *ᵥ x)) = ∑ i, ∑ j, w i j * (x i-x j)^2 := by
  have swap : (∑ i, ∑ j, w i j * x j^2) = ∑ i, ∑ j, w i j * x i^2 := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [h j i]
  have row : star x ⬝ᵥ (weightedLap w *ᵥ x) =
      ∑ i, ∑ j, (w i j * x i^2 - w i j * x i * x j) := by
    rw [weightedLap, sub_mulVec]
    unfold dotProduct
    apply sum_congr rfl
    intro i _
    rw [Pi.sub_apply, Pi.star_apply, star_trivial, Matrix.mulVec_diagonal, mul_sub,
      Matrix.mulVec, dotProduct, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> apply sum_congr rfl <;> intro j _ <;> ring
  rw [row]
  have expand (i j : V) : w i j * (x i - x j)^2 =
      w i j*x i^2 - 2*(w i j*x i*x j) + w i j*x j^2 := by ring
  simp_rw [expand]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, swap]
  ring

omit [DecidableEq V] in
private theorem quad_const (W : ℝ) (x : V → ℝ) :
    star x ⬝ᵥ ((Matrix.of (fun _ _ : V => W)) *ᵥ x) = W*(∑ i, x i)^2 := by
  simp only [dotProduct, mulVec, of_apply, Pi.star_apply, star_trivial, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

theorem lap_psd (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j) :
    (weightedLap w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (lap_symm w h)
  intro x
  have H := quad_lap w h x
  have : 0 ≤ ∑ i, ∑ j, w i j * (x i-x j)^2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg _)
  linarith

/-- The complete graph of capacity W bounds the grounded Laplacian in Loewner order. -/
theorem grounded_le (w : Mat) (h : ∀ i j, w i j = w j i) {W : ℝ} (hw : ∀ i j, w i j ≤ W) :
    grounded w W ≤ ((Fintype.card V:ℝ)*W) • (1 : Mat) := by
  let c : Mat := Matrix.of (fun i j => W-w i j)
  have hc := lap_psd c (fun i j => by simp [c,h j i]) (fun i j => sub_nonneg.mpr (hw i j))
  apply Matrix.le_iff.mpr
  convert hc using 1
  ext i j
  by_cases hij : i=j <;> simp [grounded, weightedLap, c,
    hij, Finset.sum_sub_distrib] <;> ring

/-- The graph of positive conductances ignores diagonal entries, which cancel
in the Laplacian. -/
def supportGraph (w : Mat) (h : ∀ i j, w i j = w j i) : SimpleGraph V where
  Adj i j := i ≠ j ∧ 0 < w i j
  symm := ⟨fun i j e => ⟨e.1.symm, h i j ▸ e.2⟩⟩
  loopless := ⟨fun _ e => e.1 rfl⟩

theorem grounded_pos (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j)
    (conn : (supportGraph w h).Connected) {W : ℝ} (hW : 0 < W) : (grounded w W).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos ((lap_symm w h).add (by
    ext i j
    simp [conjTranspose_apply]))
  intro x hx
  change 0 < star x ⬝ᵥ ((weightedLap w + Matrix.of (fun _ _ => W)) *ᵥ x)
  rw [add_mulVec, dotProduct_add, quad_const]
  have lp := (lap_psd w h hn).dotProduct_mulVec_nonneg x
  by_contra! bad
  have zero : (∑ i, x i) = 0 := by
    by_contra nz
    have pos := mul_pos hW (sq_pos_of_ne_zero nz)
    linarith
  have lzero : star x ⬝ᵥ (weightedLap w *ᵥ x) = 0 := by rw [zero] at bad; linarith
  have sumzero := (quad_lap w h x).symm
  rw [lzero, mul_zero] at sumzero
  have nn (i j : V) := mul_nonneg (hn i j) (sq_nonneg (x i-x j))
  have same {i j : V} (e : (supportGraph w h).Adj i j) : x i = x j := by
    have row := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg (fun j _ => nn i j))).mp sumzero i (mem_univ _)
    have term := (sum_eq_zero_iff_of_nonneg (fun j _ => nn i j)).mp row j (mem_univ _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp term).resolve_left e.2.ne'))
  obtain ⟨i⟩ := conn.nonempty
  have all (j : V) : x i = x j := by
    obtain ⟨p⟩ := conn.preconnected i j
    induction p with
    | nil => rfl
    | cons e _ ih => exact (same e).trans ih
  have sum : (∑ j, x j) = (Fintype.card V:ℝ)*x i := by simp_rw [← all]; simp
  have : Nonempty V := ⟨i⟩
  have xi : x i = 0 := (mul_eq_zero.mp (sum.symm.trans zero)).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  exact hx (funext fun j => (all j).symm.trans xi)

end ResistanceRecovery
