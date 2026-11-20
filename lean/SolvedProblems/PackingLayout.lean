module

public import SolvedProblems.PackingLift

public section

namespace PackingLift

private theorem offset_inj (p : Seed) {t h} {a b : LiftSlot p t h} :
    offset p a = offset p b → a = b := by
  have := p.disjoint
  cases a with
  | inl a =>
    have := a.isLt
    cases b with
    | inl b =>
      have := b.isLt
      intro eq
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [offset] at eq
      split at eq <;> (try split at eq) <;> (try split at eq) <;> (try split at eq) <;> omega
    | inr b =>
      have := b.isLt
      intro eq
      simp only [offset] at eq
      split at eq <;> (try split at eq) <;> (try split at eq) <;> (try split at eq) <;> omega
  | inr a =>
    have := a.isLt
    cases b with
    | inl b =>
      have := b.isLt
      intro eq
      simp only [offset] at eq
      split at eq <;> (try split at eq) <;> (try split at eq) <;> (try split at eq) <;> omega
    | inr b =>
      have := b.isLt
      intro eq
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [offset] at eq
      split at eq <;> (try split at eq) <;> (try split at eq) <;> (try split at eq) <;> omega

private theorem next_offset (p : Seed) {t h} (a b : LiftSlot p t h) :
    offset p a = (p.stride+t+h) + offset p b ↔
    match a, b with
    | .inl a, .inl b => b.val = (t+h) + a.val
    | .inr a, .inr b => a.val = p.stride+b.val
    | _, _ => False := by
  have := p.disjoint
  cases a <;> cases b <;> rename_i a b
  all_goals
    have := a.isLt
    have := b.isLt
    simp only [offset]
    repeat' (first | split | constructor)
    all_goals intros; first | contradiction | omega

/-- Equal physical positions in overlapping windows are exactly the tagged
identifications used to generate the lifted packing order. -/
theorem samePosition (p : Seed) {j t h} (i k : Fin j) (a b : LiftSlot p t h) :
    position p i a = position p k b ↔ liftAt p i a = liftAt p k b := by
  suffices forward : ∀ (i k : Fin j) (a b : LiftSlot p t h), i.val ≤ k.val →
      (position p i a = position p k b ↔ liftAt p i a = liftAt p k b) by
    by_cases le : i.val ≤ k.val
    · exact forward i k a b le
    · simpa [eq_comm] using forward k i b a (by omega)
  intro u v a b le
  have := p.disjoint
  have hU := u.isLt
  have hV := v.isLt
  by_cases eq : u = v
  · subst v
    have left : position p u a = position p u b ↔ a = b := by
      constructor
      · intro e
        exact offset_inj p (Nat.add_left_cancel (congrArg Fin.val e))
      · rintro rfl; rfl
    rw [left]
    constructor
    · rintro rfl; rfl
    · cases a <;> cases b <;> simp [liftAt,newAt,oldAt,Fin.ext_iff]
  by_cases adj : u.val+1 = v.val
  · have phys : position p u a = position p v b ↔ offset p a = (p.stride+t+h)+offset p b := by
      simp [position,Fin.ext_iff,← adj,Nat.succ_mul,Nat.add_assoc]
    rw [phys,next_offset]
    have rev : (j-1-v.val)+1=j-1-u.val := by omega
    cases a <;> cases b <;> simp [liftAt, newAt, oldAt,Fin.ext_iff,← rev,← adj,Nat.succ_mul,Nat.add_assoc] <;> omega
  · have gap : u.val+2 ≤ v.val := by
      have neq : u.val ≠ v.val := fun e => eq (Fin.ext e)
      omega
    have apart {d : Nat} : u.val*d+d+d ≤ v.val*d := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right d gap
    have revApart {d : Nat} : (j-1-v.val)*d+d+d ≤ (j-1-u.val)*d := by
      have h : (j-1-v.val)+2 ≤ (j-1-u.val) := by omega
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right d h
    have phys : position p u a ≠ position p v b := by
      intro e
      have bound := offset_bounds p a
      have same := congrArg Fin.val e
      change u.val*(p.stride+t+h)+offset p a = v.val*(p.stride+t+h)+offset p b at same
      have := apart (d := p.stride+t+h)
      omega
    simp [phys]
    cases a <;> cases b <;> simp [liftAt, newAt, oldAt, Fin.ext_iff]
    · rename_i a b
      have := revApart (d := t+h); have := b.isLt; omega
    · rename_i a b
      have := apart (d := p.stride); have := a.isLt; omega

end PackingLift
