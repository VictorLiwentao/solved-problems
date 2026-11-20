module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Intervals

public section

namespace RationalReturns

/-- Alternating binomial inversion for a path with exactly `t` interior returns. -/
theorem binomial_inversion (n r t : ℕ) (_hr : r < n) (ht : t < n) :
    ∑ s ∈ Finset.Ico r n, (-1:ℤ)^(s-r) * (s.choose r:ℤ) * (t.choose s:ℤ) =
      if t = r then 1 else 0 := by
  by_cases hrt : r ≤ t
  · let f (s : ℕ) := (-1:ℤ)^(s-r) * (s.choose r:ℤ) * (t.choose s:ℤ)
    change ∑ s ∈ Finset.Ico r n, f s = _
    have trim : ∑ s ∈ Finset.Ico r (t+1), f s = ∑ s ∈ Finset.Ico r n, f s := by
      apply Finset.sum_subset
      · intro i h; simp only [Finset.mem_Ico] at *; omega
      · intro i hi h
        have hi' := (Finset.mem_Ico.mp hi).1
        have high : t < i := by simp only [Finset.mem_Ico] at h; omega
        simp [f, Nat.choose_eq_zero_of_lt high]
    rw [← trim, Finset.sum_Ico_eq_sum_range, show t+1-r = (t-r)+1 by omega]
    have val (j : ℕ) : f (r+j) = (t.choose r : ℤ)*((-1:ℤ)^j*((t-r).choose j:ℤ)) := by
      have h := Nat.choose_mul (n:=t) (k:=r+j) (s:=r) (by omega)
      simp only [Nat.add_sub_cancel_left] at h
      have h' : (t.choose (r+j) : ℤ) * ((r+j).choose r : ℤ) =
          (t.choose r : ℤ) * ((t-r).choose j : ℤ) := by exact_mod_cast h
      dsimp [f]; rw [Nat.add_sub_cancel_left]
      calc
        _ = (-1:ℤ)^j * ((t.choose (r+j):ℤ) * ((r+j).choose r:ℤ)) := by ring
        _ = _ := by rw [h']; ring
    simp_rw [val]; rw [← Finset.mul_sum, Int.alternating_sum_range_choose]
    by_cases eq : t=r
    · simp [eq]
    · simp [eq, show t-r ≠ 0 by omega]
  · rw [ite_eq_right (by omega : t ≠ r)]
    apply Finset.sum_eq_zero
    intro s hs
    have := (Finset.mem_Ico.mp hs).1
    simp [Nat.choose_eq_zero_of_lt (by omega : t<s)]

/-- Sum by the largest of the chosen return positions. -/
theorem sum_rank_choose (S : Finset ℕ) (s : ℕ) :
    ∑ a ∈ S, ((S.filter (· < a)).card).choose s = S.card.choose (s+1) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S h ih =>
    have fresh : a ∉ S := fun ha ↦ (h a ha).false
    rw [Finset.sum_insert fresh, Finset.card_insert_of_notMem fresh, Nat.choose_succ_succ]
    have top : (insert a S).filter (· < a) = S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi, lt⟩; exact hi.resolve_left (ne_of_lt lt)
      · intro hi; exact ⟨Or.inr hi,h i hi⟩
    rw [top, ← ih]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.filter_insert]; simp [not_lt_of_gt (h x hx)]

end RationalReturns
