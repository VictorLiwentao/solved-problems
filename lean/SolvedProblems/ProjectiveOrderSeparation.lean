module

import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

public section

namespace ProjectiveIndiscernibles

/-- Integer-spaced marker positions used to replicate a finite order configuration. -/
@[expose] def center (i : ℕ) : ℚ := 5*(i : ℚ)

private noncomputable def offset (x : ℚ) : ℚ :=
  ((orderIsoIooNegOneOne ℚ) x).val - ((orderIsoIooNegOneOne ℚ) 0).val

private theorem offset_strict : StrictMono offset := by
  intro x y h
  have less : ((orderIsoIooNegOneOne ℚ) x).val < ((orderIsoIooNegOneOne ℚ) y).val :=
    (orderIsoIooNegOneOne ℚ).strictMono h
  unfold offset
  linarith

private theorem offset_zero : offset 0 = 0 := by simp [offset]

private theorem offset_bounds (x : ℚ) : -2 < offset x ∧ offset x < 2 := by
  obtain ⟨lo,hi⟩ := ((orderIsoIooNegOneOne ℚ) x).property
  obtain ⟨lo',hi'⟩ := ((orderIsoIooNegOneOne ℚ) 0).property
  unfold offset
  constructor <;> linarith

/-- Map prescribed `u < v` to `center i`, `center j`. Every other position
misses every marker, even when the other markers outnumber the original tuple. -/
noncomputable def movePair (u v : ℚ) (i j : ℕ) (x : ℚ) : ℚ :=
  if x < v then center i + offset (x-u) else center j + offset (x-v)

theorem movePair_strict {u v : ℚ} {i j : ℕ} (ij : i < j) : StrictMono (movePair u v i j) := by
  intro x y xy
  by_cases yv : y < v
  · simp only [movePair,ite_eq_left yv,ite_eq_left (xy.trans yv),add_lt_add_iff_left]
    exact offset_strict (sub_lt_sub_right xy _)
  by_cases xv : x < v
  · simp only [movePair,ite_eq_left xv,ite_eq_right yv,center]
    have le : (i:ℚ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt ij
    linarith [(offset_bounds (x-u)).2,(offset_bounds (y-v)).1]
  · simp only [movePair,ite_eq_right xv,ite_eq_right yv,add_lt_add_iff_left]
    exact offset_strict (sub_lt_sub_right xy _)

theorem movePair_left {u v : ℚ} (uv : u < v) (i j : ℕ) : movePair u v i j u = center i := by
  simp [movePair,uv,offset_zero]

theorem movePair_right (u v : ℚ) (i j : ℕ) : movePair u v i j v = center j := by
  simp [movePair,offset_zero]

private theorem offset_ne_center {i l : ℕ} {x : ℚ} (hx : x ≠ 0) : center i + offset x ≠ center l := by
  intro eq
  unfold center at eq
  rcases lt_trichotomy i l with h|rfl|h
  · have le : (i:ℚ)+1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [(offset_bounds x).2]
  · exact hx (offset_strict.injective (by rw [offset_zero]; linarith))
  · have le : (l:ℚ)+1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [(offset_bounds x).1]

theorem movePair_avoids {u v x : ℚ} {i j l : ℕ} (hu : x ≠ u) (hv : x ≠ v) :
    movePair u v i j x ≠ center l := by
  by_cases h : x < v
  · simpa only [movePair,ite_eq_left h] using (offset_ne_center (i := i) (l := l) (sub_ne_zero.mpr hu))
  · simpa only [movePair,ite_eq_right h] using (offset_ne_center (i := j) (l := l) (sub_ne_zero.mpr hv))

end ProjectiveIndiscernibles
