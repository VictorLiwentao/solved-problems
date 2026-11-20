module

public import SolvedProblems.PackingSeparatorFamily
public import SolvedProblems.PackingSeparatorPhysical
public import SolvedProblems.PackingSeparatorTransfer

public section

namespace PackingSeparator

/-- Six clipped gaps between five witnesses and the endpoints suffice for any length. -/
theorem separator_cutoff {k m j} (p : Pattern k m) :
    HasSeparator p j ↔ HasSeparator p (min j (6*(m+1)+1)) :=
  cutoff_of_rankTest p (fun x y => rankTest_iff p x y)

/-- The executable bounded rank search decides existence in the original packing. -/
theorem separatorTest_correct {k m j} (p : Pattern k m) :
    separatorTest p j = true ↔ HasSeparator p j := by
  rw [separator_cutoff p]
  unfold separatorTest
  simp only [decide_eq_true_eq]
  unfold HasSeparator SeparatesBy
  simp only [rankTest_iff]

/-- A finite interval of tests characterizes all copy counts above the overlap. -/
theorem all_lengths {k m} (p : Pattern k m) :
    (∀ j, m < j → HasSeparator p j) ↔
      ∀ j, m < j → j ≤ 6*(m+1)+1 → separatorTest p j = true := by
  constructor
  · intro h j hj _
    exact (separatorTest_correct p).mpr (h j hj)
  · intro h j hj
    apply (separator_cutoff p).mpr
    apply (separatorTest_correct p).mp
    exact h _ (by omega) (Nat.min_le_right _ _)

end PackingSeparator
