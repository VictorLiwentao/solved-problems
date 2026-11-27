module

public import SolvedProblems.JointForestContinuant
public import SolvedProblems.JointForestNeighbors

@[expose] public section

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Local inverse on a single path with zero boundary values. A source in any
other path (or at a terminal) contributes zero. -/
def localGreen (a : Base T m r) (e : Side T) (i : Fin m) (k : ℕ) : ℚ :=
  match a with
  | .inl _ => 0
  | .inr (d,n,j) => if e = d ∧ i = n then pathGreen (r+1) k (j.val+1) else 0

/-- Linear response along a path between prescribed terminal voltages, with
the sign of the far terminal and the internal point-source response. -/
def lineValue (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (k : ℕ) : ℚ :=
  (ratCont (r+1-k) * z e.val.1 - sideSign tw d e * ratCont k * z e.val.2) / ratCont (r+1) +
    localGreen a e i k

def extension (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) : Base T m r → ℚ
  | .inl x => z x
  | .inr (e,i,j) => lineValue tw d z a e i (j.val+1)

@[simp] theorem localGreen_zero (a : Base T m r) (e : Side T) (i : Fin m) :
    localGreen a e i 0 = 0 := by cases a <;> simp [localGreen]

@[simp] theorem localGreen_end (a : Base T m r) (e : Side T) (i : Fin m) :
    localGreen a e i (r+1) = 0 := by cases a <;> simp [localGreen]

@[simp] theorem lineValue_zero (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i 0 = z e.val.1 := by
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp [lineValue, hn]

@[simp] theorem lineValue_end (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i (r+1) = -sideSign tw d e * z e.val.2 := by
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp [lineValue]
  field_simp

theorem line_previous (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    extension tw d z a (previous e i j) = lineValue tw d z a e i j.val := by
  unfold previous
  split <;> rename_i h
  · rw [h, lineValue_zero]; rfl
  · change lineValue _ _ _ _ _ _ (j.val-1+1) = _
    rw [show j.val-1+1 = j.val by omega]

theorem line_following (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    (if j.val+1 < r then 1 else -sideSign tw d e) * extension tw d z a (following e i j) =
    lineValue tw d z a e i (j.val+2) := by
  by_cases h : j.val+1 < r
  · simp [h, following, extension]
  · have he := j.isLt
    rw [show j.val+2 = r+1 by omega, lineValue_end]
    simp [h, following, extension]

theorem localGreen_current (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    3 * localGreen a e i (j.val+1) - localGreen a e i j.val - localGreen a e i (j.val+2) =
    pulse (.inr (e,i,j)) a := by
  cases a with
  | inl u => simp [localGreen, pulse]
  | inr a =>
    obtain ⟨e',i',k⟩ := a
    by_cases he : e = e'
    · subst e'
      by_cases hi : i = i'
      · subst i'
        have h := pathGreen_current (s := r+1) (i := j.val+1) (j := k.val+1)
          (by omega) (by have := j.isLt; omega) (by omega) (by have := k.isLt; omega)
        simpa [localGreen, pulse, Fin.ext_iff] using h
      · simp [hi, localGreen, pulse]
    · simp [he, localGreen, pulse]

theorem line_current (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    3 * lineValue tw d z a e i (j.val+1) - lineValue tw d z a e i j.val - lineValue tw d z a e i (j.val+2) =
    pulse (.inr (e,i,j)) a := by
  have hr := j.isLt
  have h1 := ratCont_rec j.val
  have h2 := ratCont_at (by omega : 0 < r-j.val)
  have l0 : r+1-j.val = r-j.val+1 := by omega
  have l1 : r+1-(j.val+1) = r-j.val := by omega
  have l2 : r+1-(j.val+2) = r-j.val-1 := by omega
  simp only [lineValue, l0,l1,l2, ← h2, h1]
  have h := localGreen_current a e i j
  linear_combination h

theorem extension_inner_eq [Fintype T] (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T)
    (i : Fin m) (j : Fin r) : signedShift (expanded T m r) (signing tw d) (extension tw d z a) (.inr (e,i,j)) =
    pulse (.inr (e,i,j)) a := by
  rw [interior_row, line_previous, line_following]
  exact line_current ..

end JointForest
