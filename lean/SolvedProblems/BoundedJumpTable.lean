module

public import SolvedProblems.BoundedJumpCountModel
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

namespace BoundedJump

variable {α : Type} [Fintype α] (M : Machine α)

theorem wordCount_zero (q : M.State) : M.wordCount 0 q = if M.accept q then 1 else 0 := by
  classical
  cases h : M.accept q <;> simp [Machine.wordCount, h]

/-- Each table entry is computed by one summation over the fixed action alphabet.
Distinct letters count separately even if they induce the same transition. -/
theorem wordCount_step (n : Nat) (q : M.State) :
    M.wordCount (n+1) q = ∑ a : α, M.wordCount n (M.step a q) := by
  classical
  let f (w : Fin (n+1) → α) : Nat := if M.accept ((List.ofFn w).foldr M.step q) then 1 else 0
  have h := (Fin.snocEquiv (fun _ : Fin (n+1) => α)).sum_comp f
  rw [Fintype.sum_prod_type] at h
  have snoc (w : Fin n → α) (a : α) :
      (List.ofFn (Fin.snoc w a)).foldr M.step q = (List.ofFn w).foldr M.step (M.step a q) := by
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.foldr_append,
      List.foldr_cons, List.foldr_nil]
  have split (a : α) (w : Fin n → α) : (Fin.snocEquiv (fun _ : Fin (n+1) => α)) (a, w) = Fin.snoc w a := rfl
  simpa only [Machine.wordCount, Finset.card_filter, f, split, snoc] using h.symm

/-- At level n every table entry, and hence every partial sum of its nonnegative
summands, is bounded by the number of all words of length n. -/
theorem wordCount_bound (n : Nat) (q : M.State) :
    M.wordCount n q ≤ Fintype.card α ^ n := by
  classical
  simpa [Machine.wordCount, Fintype.card_pi] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n → α)))
      (p := fun w => M.accept ((List.ofFn w).foldr M.step q) = true))

end BoundedJump
