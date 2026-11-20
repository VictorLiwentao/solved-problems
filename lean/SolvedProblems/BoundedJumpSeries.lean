module

public import SolvedProblems.BoundedJumpCounting

public section

namespace BoundedJump

variable {α : Type} [Fintype α] (M : Machine α)

/-- Reverse a monic recurrence to obtain a denominator of constant term one.
Overriding the zeroth series coefficient only affects terms up to its degree. -/
private theorem rational_of_monic (w : Nat → ℤ) (d : Nat) (c : Nat → ℤ)
    (monic : c d = 1) (recurrence : ∀ n, ∑ i ∈ Finset.range (d+1), c i * w (n+i) = 0) :
    ∃ den num : Nat → ℤ, den 0 = 1 ∧ (∀ i > d, den i = 0 ∧ num i = 0) ∧
      ∀ n, (∑ i ∈ Finset.range (n+1), den i * (if n-i = 0 then 1 else w (n-i))) = num n := by
  let den (i : Nat) : ℤ := if i ≤ d then c (d-i) else 0
  let coeff (n i : Nat) := den i * (if n-i = 0 then 1 else w (n-i))
  let num (n : Nat) := if n ≤ d then ∑ i ∈ Finset.range (n+1), coeff n i else 0
  refine ⟨den,num,by simp [den,monic],fun i hi => by simp [den,num,Nat.not_le_of_gt hi],fun n => ?_⟩
  change ∑ i ∈ Finset.range (n+1), coeff n i = _
  by_cases hn : n ≤ d
  · simp [num,hn]
  rw [show num n = 0 by simp [num,hn], ← recurrence (n-d)]
  have trunc := Finset.sum_subset (f := coeff n)
    (Finset.range_mono (show d+1 ≤ n+1 by omega)) (fun i _ outside => by
      have h : ¬ i ≤ d := by simp at outside; omega
      simp [coeff,den,h])
  rw [← trunc]
  apply Finset.sum_bij' (fun i _ => d-i) (fun i _ => d-i)
  · intro i _; simp; omega
  · intro i _; simp; omega
  · intro i h; simp at h; omega
  · intro i h; simp at h; omega
  · intro i hi
    have bound : i ≤ d := by have := Finset.mem_range.mp hi; omega
    have pos : n-i ≠ 0 := by omega
    have idx : n-i = n-d+(d-i) := by omega
    simp only [coeff,den,ite_eq_left bound,ite_eq_right pos]
    rw [idx]

/-- Explicit numerator and denominator coefficients for the ordinary series, with the
empty-count convention fixed at one. Above degree d both polynomials vanish. -/
theorem wordCount_rational :
    ∃ (d : Nat) (den num : Nat → ℤ), den 0 = 1 ∧ (∀ i > d, den i = 0 ∧ num i = 0) ∧
      ∀ n, (∑ i ∈ Finset.range (n+1), den i *
        (if n-i = 0 then 1 else (M.wordCount (n-i) M.start : ℤ))) = num n := by
  obtain ⟨d,c,monic,recurrence⟩ := wordCount_recurrence M
  exact ⟨d,rational_of_monic (fun n => (M.wordCount n M.start : ℤ)) d c monic recurrence⟩

/-- Count binary additions with one accumulator initialized to zero per state.
Every intermediate sum needs at most A*n+1 bits, including for an empty alphabet. -/
theorem table_complexity (n : Nat) :
    let A := Fintype.card α
    let S := M.finite.elems.card
    (∑ _t ∈ Finset.range n, ∑ _q ∈ M.finite.elems, A) = n*S*A ∧
      (∀ t < n, ∀ (q : M.State) (U : Finset α),
        (∑ a ∈ U, M.wordCount t (M.step a q)) < 2^(A*n+1)) ∧
      (n*S*A)*(A*n+1) ≤ (S*(A+1)^2)*(n+1)^2 := by
  classical
  let A := Fintype.card α
  let S := M.finite.elems.card
  refine ⟨by simp [Nat.mul_assoc], ?_, ?_⟩
  · intro t lt q U
    have sub : (∑ a ∈ U, M.wordCount t (M.step a q)) ≤ ∑ a : α, M.wordCount t (M.step a q) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ U)]
      omega
    rw [← wordCount_step] at sub
    have H := (sub.trans (wordCount_bound M (t+1) q)).trans
      (Nat.pow_le_pow_left (Nat.lt_two_pow_self.le : A ≤ 2^A) (t+1))
    rw [← Nat.pow_mul] at H
    have H' := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.mul_le_mul_left A lt)
    exact Nat.lt_of_le_of_lt (H.trans H') (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  · change n*S*A*(A*n+1) ≤ S*(A+1)^2*(n+1)^2
    have bound : A*n+1 ≤ (A+1)*(n+1) := by rw [Nat.add_mul,Nat.mul_add]; omega
    calc
      _ ≤ (n+1)*S*(A+1)*((A+1)*(n+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right S (Nat.le_succ _)) (Nat.le_succ _)) bound
      _ = _ := by simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]; ac_rfl

end BoundedJump
