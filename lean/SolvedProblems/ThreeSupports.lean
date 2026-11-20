module

public import SolvedProblems.GenerationThresholdModel

public section

namespace GenerationThreshold

private def loss (i : Fin 3) (e : Edge) : Nat :=
  if ((e.lo % 4 < 3 ∧ e.lo % 4 ≠ i.val) ↔ (e.hi % 4 < 3 ∧ e.hi % 4 ≠ i.val)) then 1 else 0

private theorem atLeastOne (e : Edge) : 1 ≤ loss 0 e + loss 1 e + loss 2 e := by
  simp only [loss]
  have a := Nat.mod_lt e.lo (by decide : 0 < 4)
  have b := Nat.mod_lt e.hi (by decide : 0 < 4)
  have ha : e.lo%4 = 0 ∨ e.lo%4 = 1 ∨ e.lo%4 = 2 ∨ e.lo%4 = 3 := by omega
  have hb : e.hi%4 = 0 ∨ e.hi%4 = 1 ∨ e.hi%4 = 2 ∨ e.hi%4 = 3 := by omega
  rcases ha with h|h|h|h <;> rcases hb with h'|h'|h'|h' <;> simp [h,h']

private theorem countStep (i : Fin 3) (e : Edge) (s : List Edge) :
    violations (threeSupport i) (e::s) = violations (threeSupport i) s + loss i e := by
  classical
  unfold violations
  rw [List.filter_cons]
  by_cases h : crosses (threeSupport i) e
  · have zero : loss i e = 0 := by unfold loss; exact ite_eq_right h
    simp [h,zero]
  · have one : loss i e = 1 := by unfold loss; exact ite_eq_left (Classical.not_not.mp h)
    simp [h,one]

private def ceiling (s : List Edge) : Nat := s.foldr (fun e b => max e.hi b) 0

private theorem below {e : Edge} {s : List Edge} (he : e ∈ s) : e.hi ≤ ceiling s := by
  induction s with
  | nil => simp at he
  | cons a s ih =>
    rcases List.mem_cons.mp he with rfl | hm
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih hm) (Nat.le_max_right ..)

/-- The same generator, independent of the corruption budget, works at every
prefix with strictly fewer than one third violations for the true cut. -/
theorem unknownBudget : ∃ G : List Edge → Nat, ∀ s i, 3 * violations (threeSupport i) s < s.length →
    fresh s (G s) ∧ threeSupport i (G s) := by
  classical
  let v (s : List Edge) (i : Fin 3) := violations (threeSupport i) s
  let drop (s : List Edge) : Fin 3 := if v s 1 ≤ v s 0 ∧ v s 2 ≤ v s 0 then 0
    else if v s 2 ≤ v s 1 then 1 else 2
  let G (s : List Edge) := 4*(ceiling s+1) + (drop s).val
  refine ⟨G,fun s i h => ?_⟩
  have sum (xs : List Edge) : xs.length ≤ v xs 0 + v xs 1 + v xs 2 := by
    induction xs with
    | nil => simp [v,violations]
    | cons e xs ih =>
      simp only [v,countStep,List.length_cons] at *
      have := atLeastOne e
      omega
  have total := sum s
  change 3 * v s i < s.length at h
  have bad : i ≠ drop s := by
    intro eq
    rw [eq] at h
    unfold drop at h
    split at h
    · omega
    · split at h <;> omega
  have residue : G s % 4 = (drop s).val := by simp [G,Nat.add_mod,Nat.mod_eq_of_lt (show (drop s).val < 4 by omega)]
  constructor
  · intro e he
    have := below he
    have := e.ordered
    dsimp [G]
    omega
  · simp only [threeSupport,residue]
    exact ⟨(drop s).isLt, fun eq => bad (Fin.ext eq.symm)⟩

end GenerationThreshold
