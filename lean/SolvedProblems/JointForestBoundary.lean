module

public import SolvedProblems.JointForestInterpolation
public import SolvedProblems.JointForestIncidence

@[expose] public section

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Terminal self-conductance left after eliminating one whole side. -/
def gain (r : ℕ) : ℚ := 1 + ratCont (r+1) - ratCont r

theorem gain_pos (r : ℕ) : 0 < gain r := by
  have h : ratCont r < ratCont (r+1) := by exact_mod_cast continuant_increasing r
  unfold gain; linarith

def leftRatio (j : Fin r) : ℚ := ratCont (r-j.val) / ratCont (r+1)
def rightRatio (j : Fin r) : ℚ := ratCont (j.val+1) / ratCont (r+1)

theorem first_green (j : Fin r) : pathGreen (r+1) 1 (j.val+1) = leftRatio j := by
  rw [pathGreen_left (by omega : 1 ≤ j.val+1)]
  simp [leftRatio]

theorem last_green (j : Fin r) : pathGreen (r+1) r (j.val+1) = rightRatio j := by
  rw [pathGreen_right (by have := j.isLt; omega : j.val+1 ≤ r)]
  simp [rightRatio]

theorem line_first (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i 1 = (ratCont r * z e.val.1 - sideSign tw d e * z e.val.2) / ratCont (r+1) + localGreen a e i 1 := by simp [lineValue]

theorem line_last (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i r = (z e.val.1 - sideSign tw d e * ratCont r * z e.val.2) / ratCont (r+1) + localGreen a e i r := by simp [lineValue]

theorem sideSign_square (tw : Bool) (d e : Side T) : sideSign tw d e * sideSign tw d e = 1 := polarity_square _

/-- The off-diagonal response of the parallel paths is exactly the negative of
the response of the direct signed edge at both ends. -/
theorem left_bundle (hm : m = continuant (r+1)) (tw : Bool) (d e : Side T) (z : T → ℚ) (a : Base T m r) :
    z e.val.1 - sideSign tw d e * z e.val.2 + (∑ i : Fin m, (z e.val.1 - lineValue tw d z a e i 1)) =
    gain r * z e.val.1 - ∑ i : Fin m, localGreen a e i 1 := by
  have hm' : (m : ℚ) = ratCont (r+1) := congrArg Nat.cast hm
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp only [line_first, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm', gain]
  field_simp
  ring

theorem right_bundle (hm : m = continuant (r+1)) (tw : Bool) (d e : Side T) (z : T → ℚ) (a : Base T m r) :
    z e.val.2 - sideSign tw d e * z e.val.1 + (∑ i : Fin m, (z e.val.2 + sideSign tw d e * lineValue tw d z a e i r)) =
    gain r * z e.val.2 + sideSign tw d e * ∑ i : Fin m, localGreen a e i r := by
  have hm' : (m : ℚ) = ratCont (r+1) := congrArg Nat.cast hm
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp only [line_last, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm', gain]
  field_simp
  cases tw <;> by_cases he : e = d <;> simp [sideSign, polarity, he] <;> ring

/-- Coefficient of terminal `u` in the conditional mean at source `a`. -/
def boundaryWeight (tw : Bool) (d : Side T) (a : Base T m r) (u : T) : ℚ :=
  match a with
  | .inl v => if u = v then 1 else 0
  | .inr (e,_,j) => (if e.val.1 = u then leftRatio j else 0) -
                      (if e.val.2 = u then sideSign tw d e * rightRatio j else 0)

noncomputable def leftLeak (a : Base T m r) (e : Side T) : ℚ := ∑ i : Fin m, localGreen a e i 1
noncomputable def rightLeak (a : Base T m r) (e : Side T) : ℚ := ∑ i : Fin m, localGreen a e i r

theorem leftLeak_inner (e e' : Side T) (i : Fin m) (j : Fin r) :
    leftLeak (.inr (e',i,j)) e = if e = e' then leftRatio j else 0 := by
  by_cases h : e = e' <;> simp [leftLeak, localGreen,h, first_green]

theorem rightLeak_inner (e e' : Side T) (i : Fin m) (j : Fin r) :
    rightLeak (.inr (e',i,j)) e = if e = e' then rightRatio j else 0 := by
  by_cases h : e = e' <;> simp [rightLeak, localGreen,h, last_green]

theorem sum_leaks [Fintype T] (tw : Bool) (d : Side T) (a : Base T m r) (u : T) :
    (∑ e : Side T, ((if e.val.1 = u then leftLeak a e else 0) -
      (if e.val.2 = u then sideSign tw d e * rightLeak a e else 0))) = boundaryWeight tw d a u - pulse (.inl u) a := by
  classical
  cases a with
  | inl v => simp [leftLeak, rightLeak, localGreen, boundaryWeight, pulse]
  | inr a =>
    obtain ⟨e',i',j'⟩ := a
    have h (e : Side T) : (if e.val.1 = u then leftLeak (.inr (e',i',j')) e else 0) -
        (if e.val.2 = u then sideSign tw d e * rightLeak (.inr (e',i',j')) e else 0) =
        if e = e' then boundaryWeight tw d (.inr (e',i',j')) u else 0 := by
      by_cases he : e = e' <;> simp [he, leftLeak_inner, rightLeak_inner, boundaryWeight]
    simp_rw [h]
    simp [pulse]

end JointForest
