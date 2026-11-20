module

public import SolvedProblems.TapeModel
public import Std

public section

namespace TapeInclusion

private theorem copies_zero (u : Word) : copies u 0 = [] := rfl

private theorem copies_succ (u : Word) (n : Nat) : copies u (n+1) = u ++ copies u n := rfl

private theorem rotation (p q : Word) (i : Nat) :
    copies (p ++ q) i ++ p = p ++ copies (q ++ p) i := by
  induction i with
  | zero => simp [copies_zero]
  | succ i ih =>
    simp only [copies_succ, List.append_assoc] at *
    rw [ih]

private theorem length_copies (v : Word) (k) : (copies v k).length = k*v.length := by
  induction k with
  | zero => simp [copies_zero]
  | succ k ih => simp [copies_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem primitiveThree (a b c : Bool) (diff : ¬ (a = b ∧ b = c)) :
    primitive [a,b,c] := by
  intro v k h
  have size := congrArg List.length h
  simp [length_copies] at size
  cases v with
  | nil => simp at size
  | cons x xs =>
    simp at size
    by_cases small : k ≤ 1
    · exact small
    · have prod : k * xs.length + k = 3 := by simpa [Nat.mul_succ] using size
      by_cases empty : xs.length = 0
      · have ek : k = 3 := by simp [empty] at prod; omega
        have en := List.length_eq_zero_iff.mp empty
        subst xs k
        change [x, x, x] = [a, b, c] at h
        grind
      · have le := Nat.mul_le_mul_left k (show 1 ≤ xs.length by omega)
        simp at le
        omega

/-- Strict inclusion for aligned, equal-width, primitive, noncommuting stars
despite a different first repeater. This refutes the empty-wall proposal. -/
theorem emptyWallCounterexample :
    aligned source ∧ aligned target ∧
    (∀ h ∈ [source,target], primitive h.first ∧ primitive h.second ∧
      h.first.length = 3 ∧ h.second.length = 3 ∧
      h.first ++ h.second ≠ h.second ++ h.first) ∧
    (∀ w, accepts source w → accepts target w) ∧
    (∃ w, accepts target w ∧ ¬ accepts source w) ∧ source.first ≠ target.first := by
  refine ⟨by unfold aligned source; decide, by unfold aligned target; decide, ?_, ?_, ?_, by decide⟩
  · intro h mem
    simp at mem
    rcases mem with rfl | rfl <;>
      exact ⟨primitiveThree _ _ _ (by decide),primitiveThree _ _ _ (by decide),
        rfl,rfl,by decide⟩
  · rintro w ⟨i,j,rfl⟩
    refine ⟨i,j+1,?_⟩
    have h := rotation [false] [false,true] i
    change copies [false,false,true] i ++ [false] = [false] ++ copies [false,true,false] i at h
    have eq := congrArg (fun u : Word => u ++ [true,true] ++ copies [false,true,true] j) h.symm
    simpa [source,target,copies_succ,List.append_assoc] using eq
  · refine ⟨[],⟨0,0,rfl⟩,?_⟩
    rintro ⟨i,j,h⟩
    simp [source] at h

end TapeInclusion
