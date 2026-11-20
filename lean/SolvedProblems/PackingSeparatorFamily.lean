module

public import SolvedProblems.PackingSeparatorOrder

public section

namespace PackingSeparator

private theorem existsTwo (q : Nat → Prop) : (∃ i < 2, q i) ↔ q 0 ∨ q 1 := by
  constructor
  · rintro ⟨i,hi,h⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl|rfl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h|h)
    · exact ⟨0,by decide,h⟩
    · exact ⟨1,by decide,h⟩

/-- In the overlap-two family with prefix (0,a) and suffix (b,c), the last
position of the first window separates every packing of at least two copies.
Ranks and positions are zero-based. -/
theorem proposed_separator {k j a b c} (p : Pattern k 2) (two : 1 < j)
    (pa : 1 < a) (ab : a < b) (bc : b+1 < c) (ck : c+1 < k)
    (pref0 : p.rank 0 = 0) (pref1 : p.rank 1 = a)
    (suf0 : p.rank (k-2) = b) (suf1 : p.rank (k-2+1) = c) :
    ∃ z : Mark k j, z.1.val = 0 ∧ z.2.val = c ∧ SeparatesBy (LEPos p) z := by
  let first (r : Fin k) : Mark k j := (⟨0,by omega⟩,r)
  let second (r : Fin k) : Mark k j := (⟨1,two⟩,r)
  have lr (r s : Fin k) : LEPos p (first r) (second s) ↔
      (r.val ≤ b ∧ 0 ≤ s.val) ∨ (r.val ≤ c ∧ a ≤ s.val) := by
    rw [firstToSecond p two,existsTwo]
    simp only [Nat.add_zero,pref0,pref1,suf0,suf1]
  have rl (r s : Fin k) : LEPos p (second r) (first s) ↔
      (r.val ≤ 0 ∧ b ≤ s.val) ∨ (r.val ≤ a ∧ c ≤ s.val) := by
    rw [secondToFirst p two,existsTwo]
    simp only [Nat.add_zero,pref0,pref1,suf0,suf1]
  have xx (r s : Fin k) : LEPos p (first r) (first s) ↔ r.val ≤ s.val :=
    withinWindow p _ r s
  have joined : Below p j 0 c 1 a := by
    have path : Below p j 0 c 0 (p.rank (k-2+1)) := suf1 ▸ Below.refl
    simpa only [pref1] using Below.right path (by decide : 1 < 2) two
  have later (n) (hn : n+2 < j) : Below p j 0 c (n+2) 0 := by
    induction n with
    | zero =>
      have path := Below.rise joined (t := p.rank (k-2+0)) (by simp [suf0]; omega)
        (by simp [suf0]; omega)
      simpa only [pref0] using Below.right path (by decide : 0 < 2) hn
    | succ n ih =>
      have path := Below.rise (ih (by omega)) (t := p.rank (k-2+0)) (Nat.zero_le _)
        (by simp [suf0]; omega)
      simpa only [pref0] using Below.right path (by decide : 0 < 2) hn
  let z : Fin k := ⟨c,by omega⟩
  refine ⟨first z,rfl,rfl,?_⟩
  refine ⟨first ⟨b+1,by omega⟩,second ⟨1,by omega⟩,first ⟨c+1,ck⟩,second ⟨a+1,by omega⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · rintro ⟨⟨w,hw⟩,r⟩
    cases w with
    | zero =>
      change LEPos p (first z) (first r) ∨ LEPos p (first r) (first z)
      simpa only [xx] using Nat.le_total z.val r.val
    | succ w =>
      cases w with
      | zero =>
        change LEPos p (first z) (second r) ∨ LEPos p (second r) (first z)
        simp only [lr,rl,z]
        omega
      | succ w => exact Or.inl (Below.rise (later w hw) (Nat.zero_le _) r.isLt)
  all_goals simp only [xx,lr,rl,z]
  all_goals omega

end PackingSeparator
