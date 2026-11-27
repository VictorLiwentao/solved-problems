module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace JointForest

/-- `continuant (r+1)` is the determinant of the tridiagonal path-interior
matrix of size `r`, with diagonal 3 and consecutive entries −1. -/
def continuant : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => 3 * continuant (n+1) - continuant n

theorem continuant_increasing (i : ℕ) : continuant i < continuant (i+1) := by
  induction i with
  | zero => decide
  | succ i ih => rw [continuant]; omega

abbrev ratCont (i : ℕ) : ℚ := continuant i

@[simp] theorem ratCont_zero : ratCont 0 = 0 := rfl
@[simp] theorem ratCont_one : ratCont 1 = 1 := rfl

theorem ratCont_pos {i : ℕ} (h : 0 < i) : 0 < ratCont i := by
  cases i with
  | zero => omega
  | succ i => exact_mod_cast Nat.zero_lt_of_lt (continuant_increasing i)

theorem ratCont_rec (i : ℕ) : ratCont (i+2) = 3 * ratCont (i+1) - ratCont i := by
  have hn := continuant_increasing i
  change ((3 * continuant (i+1) - continuant i : ℕ) : ℚ) = _
  simp only [ratCont, Nat.cast_sub (by omega : continuant i ≤ 3 * continuant (i+1)),
    Nat.cast_mul, Nat.cast_ofNat]

/-- Discrete Wronskian, used at the vertex carrying the unit current. -/
theorem ratCont_join (a b : ℕ) : ratCont (a+1) * ratCont (b+1) - ratCont a * ratCont b = ratCont (a+b+1) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    have h := ih (b+1)
    rw [ratCont_rec b] at h
    rw [ratCont_rec a]
    rw [show a+1+b+1 = a+(b+1)+1 by omega]
    linear_combination h

/-- Green entry at internal positions `i,j` of a length-`s` path with both
endpoints held at zero. We number the endpoints 0 and `s`. -/
def pathGreen (s i j : ℕ) : ℚ := ratCont (min i j) * ratCont (s - max i j) / ratCont s

theorem pathGreen_symm (s i j : ℕ) : pathGreen s i j = pathGreen s j i := by
  simp only [pathGreen, min_comm i j, max_comm i j]

@[simp] theorem pathGreen_zero (s j : ℕ) : pathGreen s 0 j = 0 := by simp [pathGreen]

@[simp] theorem pathGreen_end (s j : ℕ) : pathGreen s s j = 0 := by
  simp [pathGreen, Nat.sub_eq_zero_of_le (le_max_left s j)]

theorem pathGreen_left {s i j : ℕ} (h : i ≤ j) : pathGreen s i j = ratCont i * ratCont (s-j) / ratCont s := by
  simp [pathGreen, min_eq_left h, max_eq_right h]

theorem pathGreen_right {s i j : ℕ} (h : j ≤ i) : pathGreen s i j = ratCont j * ratCont (s-i) / ratCont s := by
  rw [pathGreen_symm, pathGreen_left h]

theorem ratCont_at {j : ℕ} (hj : 0 < j) : 3 * ratCont j - ratCont (j-1) = ratCont (j+1) := by
  cases j with
  | zero => omega
  | succ j => exact (ratCont_rec j).symm

/-- Applying the interior path operator gives a Kronecker delta. -/
theorem pathGreen_current {s i j : ℕ} (hi : 0 < i) (his : i < s) (hj : 0 < j) (hjs : j < s) :
    3 * pathGreen s i j - pathGreen s (i-1) j - pathGreen s (i+1) j = if i = j then 1 else 0 := by
  have hn := (ratCont_pos (by omega : 0 < s)).ne'
  rcases lt_trichotomy i j with hl | rfl | hr
  · rw [pathGreen_left hl.le, pathGreen_left (by omega : i-1 ≤ j), pathGreen_left (by omega : i+1 ≤ j),
      ite_eq_right hl.ne]
    have h := ratCont_at hi
    field_simp
    linear_combination (ratCont (s-j)) * h
  · rw [pathGreen_left le_rfl, pathGreen_left (by omega : i-1 ≤ i), pathGreen_right (by omega : i ≤ i+1),
      ite_eq_left rfl]
    have h := ratCont_at hi
    have h' := ratCont_join i (s-i-1)
    rw [show s-i-1+1 = s-i by omega, show i+(s-i-1)+1 = s by omega] at h'
    rw [show s-(i+1) = s-i-1 by omega]
    field_simp
    linear_combination (ratCont (s-i)) * h + h'
  · rw [pathGreen_right hr.le, pathGreen_right (by omega : j ≤ i-1), pathGreen_right (by omega : j ≤ i+1),
      ite_eq_right (Ne.symm hr.ne)]
    rw [show s-(i-1) = s-i+1 by omega, show s-(i+1) = s-i-1 by omega]
    have h := ratCont_at (by omega : 0 < s-i)
    field_simp
    linear_combination (ratCont j) * h

/-- The corner inverse entry contributed by a single long path. -/
theorem pathGreen_corner {s : ℕ} (hs : 2 ≤ s) : pathGreen s 1 (s-1) = 1 / ratCont s := by
  rw [pathGreen_left (by omega : 1 ≤ s-1), show s-(s-1) = 1 by omega]
  simp

end JointForest
