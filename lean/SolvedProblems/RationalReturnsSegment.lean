module

public import SolvedProblems.RationalReturnsRemove
public import SolvedProblems.RationalReturnsRanks
public import SolvedProblems.RationalReturnsFlagDet

public section

namespace RationalReturns

/-- The determinant counts the actual north-step words on the segment, with
the given forbidden column, required columns, and floor-diagonal boundary. -/
theorem segment_determinant {m n d k i j : ℕ} (hn : 0 < n) (hm : n ≤ m) (hd : 0 < d)
    (hij : i < j) (hj : j ≤ n) :
    (segmentCount m n d k i j : ℤ) = determinantEntry m n d k i j := by
  classical
  let L := edge m n i
  let U := edge m n j
  let A := allowed d k L U
  let B := mandatory d k L U
  let D := demand m n i
  let R := j-i-B.card
  let b (q : Fin R) := flag A B D L U q.val
  have eq := segmentBags (d:=d) (k:=k) hn hm hij hj
  change (Fintype.card (Segment m n d k i j) : ℤ) =
    if B.card ≤ j-i ∧ ∀ c ∈ Finset.Icc L U, D c ≤ before B c + R then binomialDet b else 0
  split
  next feasible =>
    obtain ⟨room,bounds⟩ := feasible
    have rows := residualWords A B D L U (mandatory_subset_allowed hd) room
    have ranks := residualRanks A B D L U R bounds
    rw [Fintype.card_congr ((eq.trans rows).trans ranks)]
    exact flagged_count b (fun _ _ h => flag_mono A B D L U h)
  next infeasible =>
    have empty : IsEmpty (Segment m n d k i j) := ⟨fun w =>
      infeasible (necessary_bounds (eq w).property)⟩
    simp [Fintype.card_eq_zero]

end RationalReturns
