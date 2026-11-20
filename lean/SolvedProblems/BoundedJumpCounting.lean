module

public import SolvedProblems.BoundedJumpTable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

public section

namespace BoundedJump

open Matrix Polynomial

variable {α : Type} [Fintype α] (M : Machine α)

/-- A monic integer recurrence for all accepting-word counts. Reversing its coefficients
gives a denominator with constant coefficient one for the ordinary generating function.
Changing the empty word count adds only a constant to that function. -/
theorem wordCount_recurrence :
    ∃ (d : Nat) (c : Nat → ℤ), c d = 1 ∧ ∀ n,
      ∑ i ∈ Finset.range (d+1), c i * (M.wordCount (n+i) M.start : ℤ) = 0 := by
  classical
  letI := M.finite
  let W : Matrix M.State M.State ℤ := fun q r =>
    ∑ a : α, if M.step a q = r then 1 else 0
  let v (n : Nat) (q : M.State) : ℤ := M.wordCount n q
  have step (n : Nat) : W *ᵥ v n = v (n+1) := by
    ext q
    simp only [Matrix.mulVec, dotProduct, W, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    simp [v, wordCount_step]
  have power (i n : Nat) : (W ^ i) *ᵥ v n = v (n+i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, step, Nat.add_assoc]
  let p := W.charpoly
  refine ⟨p.natDegree, p.coeff, W.charpoly_monic, fun n => ?_⟩
  have h := W.aeval_self_charpoly
  rw [aeval_eq_sum_range] at h
  have hz := congrArg (fun A : Matrix M.State M.State ℤ => (A *ᵥ v n) M.start) h
  simpa only [Matrix.sum_mulVec, Finset.sum_apply, Matrix.smul_mulVec, power,
    Pi.smul_apply, smul_eq_mul, Matrix.zero_mulVec, Pi.zero_apply, v, p] using hz

end BoundedJump
