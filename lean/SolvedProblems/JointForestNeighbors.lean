module

public import SolvedProblems.JointForestLong
public import SolvedProblems.JointForestResponse

@[expose] public section

namespace JointForest

open SimpleGraph

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Each unordered pair has exactly one increasing representation. -/
theorem side_endpoints (a b : Side T) : s(a.val.1,a.val.2) = s(b.val.1,b.val.2) ↔ a = b := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have h₁ := a.property
      rw [h.1, h.2] at h₁
      exact (lt_asymm h₁ b.property).elim
  · rintro rfl; rfl

/-- Direct sign on this side (right-terminal path signs are its negatives). -/
def sideSign (tw : Bool) (d e : Side T) : ℚ := polarity (tw && decide (e = d))

theorem right_sign (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inr (e,i,j)) (.inl e.val.2)) = -sideSign tw d e := by
  simp [signing, signBit, sideSign]; cases tw <;> by_cases e = d <;> simp [*, polarity]

theorem direct_sign (tw : Bool) (d e : Side T) :
    polarity ((signing (m := m) (r := r) tw d).neg (.inl e.val.1) (.inl e.val.2)) = sideSign tw d e := by
  simp only [signing, signBit, side_endpoints, sideSign]

def previous (e : Side T) (i : Fin m) (j : Fin r) : Base T m r :=
  if hj : j.val = 0 then .inl e.val.1 else .inr (e,i,⟨j.val-1,by have := j.isLt; omega⟩)

def following (e : Side T) (i : Fin m) (j : Fin r) : Base T m r :=
  if hj : j.val+1 < r then .inr (e,i,⟨j.val+1,hj⟩) else .inl e.val.2

theorem previous_ne_following (e : Side T) (i : Fin m) (j : Fin r) : previous e i j ≠ following e i j := by
  unfold previous following
  split <;> split <;> simp_all [ne_of_lt e.property, Fin.ext_iff]

theorem previous_adj (e : Side T) (i : Fin m) (j : Fin r) :
    (expanded T m r).Adj (.inr (e,i,j)) (previous e i j) := by
  unfold previous
  split <;> rename_i h
  · exact ⟨by simp, Or.inr (Or.inl ⟨rfl,h⟩)⟩
  · refine ⟨by simp [Fin.ext_iff]; omega, Or.inr ⟨rfl,rfl,?_⟩⟩
    change j.val-1+1 = j.val
    omega

theorem following_adj (e : Side T) (i : Fin m) (j : Fin r) :
    (expanded T m r).Adj (.inr (e,i,j)) (following e i j) := by
  unfold following
  split <;> rename_i h
  · exact ⟨by simp [Fin.ext_iff], Or.inl ⟨rfl,rfl,rfl⟩⟩
  · refine ⟨by simp, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    have := j.isLt; omega

theorem inner_neighbors (e : Side T) (i : Fin m) (j : Fin r) {z : Base T m r}
    (h : (expanded T m r).Adj (.inr (e,i,j)) z) : z = previous e i j ∨ z = following e i j := by
  cases z with
  | inl v =>
    rcases h.2 with hs | hs
    · exact False.elim hs
    · rcases hs with ⟨rfl,hj⟩ | ⟨rfl,hj⟩
      · exact Or.inl (by simp [previous,hj])
      · exact Or.inr (by simp [following,hj])
  | inr z =>
    obtain ⟨d,k,l⟩ := z
    rcases h.2 with hs | hs
    · rcases hs with ⟨rfl,rfl,hj⟩
      have hl := l.isLt
      exact Or.inr (by simp [following, hj, hl])
    · rcases hs with ⟨rfl,rfl,hj⟩
      have hp : j.val ≠ 0 := by omega
      exact Or.inl (by simp [previous, hp, Fin.ext_iff]; omega)

theorem previous_sign (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inr (e,i,j)) (previous e i j)) = 1 := by
  unfold previous
  split <;> simp [signing, signBit, ne_of_lt e.property]

theorem following_sign (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inr (e,i,j)) (following e i j)) =
      if j.val+1 < r then 1 else -sideSign tw d e := by
  unfold following
  split <;> rename_i h
  · simp [signing, signBit]
  · simp only [right_sign]

/-- The entire shifted signed row at an interior vertex consists of its two
path neighbors. Only the far terminal edge can carry a negative sign. -/
theorem interior_row [Fintype T] (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r)
    (p : Base T m r → ℚ) : signedShift (expanded T m r) (signing tw d) p (.inr (e,i,j)) =
    3*p (.inr (e,i,j)) - p (previous e i j) -
      (if j.val+1 < r then 1 else -sideSign tw d e) * p (following e i j) := by
  classical
  let x : Base T m r := .inr (e,i,j)
  let a := previous e i j
  let b := following e i j
  let f (v : Base T m r) := p x - polarity ((signing tw d).neg x v) * p v
  have hne : a ≠ b := previous_ne_following e i j
  have hh (v : Base T m r) : (if (expanded T m r).Adj x v then f v else 0) =
      (if v = a then f v else 0) + (if v = b then f v else 0) := by
    by_cases ha : v = a
    · subst v; simp [hne, show (expanded T m r).Adj x a from previous_adj ..]
    by_cases hb : v = b
    · subst v; simp [ha, show (expanded T m r).Adj x b from following_adj ..]
    have hn : ¬ (expanded T m r).Adj x v := fun h => (inner_neighbors e i j h).elim ha hb
    simp [ha,hb,hn]
  change p x + (∑ v, if (expanded T m r).Adj x v then f v else 0) = _
  simp_rw [hh]
  simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq', f, x, a, b, previous_sign, following_sign]
  ring

end JointForest
