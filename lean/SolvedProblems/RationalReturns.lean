module

public import SolvedProblems.RationalReturnsSegment
public import SolvedProblems.RationalReturnsFull
public import SolvedProblems.RationalReturnsPower

public section

namespace RationalReturns

/-- The joint run/return count for every permitted stride, including stride one
and the ratio stride floor(m/n). The entries on the right are explicit
binomial determinants; zero-based return index s counts chosen interior arrivals. -/
theorem joint_run_return {m n d k ℓ : ℕ} (hn : 0 < n) (hm : n ≤ m)
    (hd : 0 < d) (hdm : d ≤ m/n) (hk : 0 < k) (hkn : k ≤ n)
    (hℓ : 0 < ℓ) (hℓn : ℓ ≤ n) :
    (jointCount m n d k ℓ : ℤ) = ∑ s ∈ Finset.Ico (ℓ-1) n,
      (-1 : ℤ)^(s-(ℓ-1)) * (s.choose (ℓ-1) : ℤ) *
        (determinantMatrix m n d k ^ (s+1)) 0 (Fin.last n) := by
  classical
  have kernel : segmentMatrix m n d k = determinantMatrix m n d k := by
    ext i j
    by_cases h : i < j
    · simpa only [segmentMatrix, determinantMatrix, ite_eq_left h] using
        (segment_determinant (k:=k) hn hm hd h (Nat.le_of_lt_succ j.isLt))
    · simp only [segmentMatrix, determinantMatrix, ite_eq_right h]
  rw [jointCount_eq_segment hn hm hd hdm hk hkn, ←kernel]
  exact count_by_powers hn hm hℓ hℓn

end RationalReturns
