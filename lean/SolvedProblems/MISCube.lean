module

public import SolvedProblems.MISBernoulli

@[expose] public section

namespace MISQueries
variable {V : Type*} [DecidableEq V]

/-- A numerical indicator for finite probability calculations. -/
noncomputable def bit (p : Prop) : ℝ := by classical exact if p then 1 else 0
@[simp] theorem bit_pos {p : Prop} (h : p) : bit p = 1 := by simp [bit,h]
@[simp] theorem bit_neg {p : Prop} (h : ¬p) : bit p = 0 := by simp [bit,h]
theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by classical by_cases h : p <;> simp [h]
theorem bit_le_one (p : Prop) : bit p ≤ 1 := by classical by_cases h : p <;> simp [h]
theorem bit_mono {p q : Prop} (h : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [hp,h hp]
  · simpa only [bit_neg hp] using bit_nonneg q

theorem bit_not (p : Prop) : bit (¬p) = 1 + -1 * bit p := by
  classical
  by_cases h : p <;> simp [h,bit]

theorem avoidance (p : ℝ) (xs : List V) (R : Finset V) :
    average p xs (fun S => bit (Disjoint S R)) = (1-p) ^ (xs.filter (fun x => decide (x ∈ R))).length := by
  induction xs with
  | nil => simp [average,bit]
  | cons x xs ih =>
    by_cases hx : x ∈ R <;>
      simp [average, Finset.disjoint_insert_left, hx, average.const, ih, pow_succ] <;> ring

theorem hit_probability [Fintype V] (p : ℝ) (R : Finset V) :
    average p Finset.univ.toList (fun S => bit (¬Disjoint S R)) = 1 - (1-p)^R.card := by
  classical
  let xs : List V := Finset.univ.toList
  have hset : (xs.filter (fun x => decide (x ∈ R))).toFinset = R := by ext; simp [xs]
  have hn := List.toFinset_card_of_nodup ((Finset.nodup_toList (Finset.univ : Finset V)).filter (fun x => decide (x ∈ R)))
  rw [hset] at hn
  simp_rw [bit_not]
  rw [average.add, average.const, average.scale, avoidance, ← hn]
  ring

/-- The exponential moment of the number of blockers is at most (1+p)^n. -/
theorem size_moment {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) :
    average p xs (fun S => (2 : ℝ)^S.card) ≤ (1+p)^xs.length := by
  induction xs with
  | nil => simp [average]
  | cons x xs ih =>
    have step : average p xs (fun S => (2 : ℝ)^(insert x S).card) ≤ 2 * average p xs (fun S => (2 : ℝ)^S.card) := by
      rw [← average.scale]
      apply average.mono hp hp' xs
      intro S
      rw [mul_comm, ← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) (Finset.card_insert_le ..)
    simp only [average, List.length_cons, pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left step hp,
      mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+p by linarith)]

/-- Markov's bound discards trials on which the degree promise might fail. -/
theorem bad_probability {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) (D : ℕ) :
    average p xs (fun S => bit (D ≤ S.card)) ≤ (1+p)^xs.length / 2^D := by
  have h : average p xs (fun S => bit (D ≤ S.card)) ≤
      (2^D : ℝ)⁻¹ * average p xs (fun S => (2 : ℝ)^S.card) := by
    rw [← average.scale]
    apply average.mono hp hp' xs
    intro S
    by_cases hs : D ≤ S.card
    · rw [bit_pos hs, ← div_eq_inv_mul]
      exact (one_le_div₀ (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) hs)
    · rw [bit_neg hs]; positivity
  rw [div_eq_inv_mul]
  exact h.trans (mul_le_mul_of_nonneg_left (size_moment hp hp' xs) (by positivity))

end MISQueries
