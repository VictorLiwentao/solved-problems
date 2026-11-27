module

public import SolvedProblems.MISHiddenGraphs
public import SolvedProblems.MISCube
public import SolvedProblems.MISSeparationProbability

@[expose] public section

namespace MISQueries

/-- Average over the algorithm's coins for this fixed hidden pair and blockers.
If the degree bound holds, a missed pair forces an error on at least one of
the two bits for the two *fixed* legal oracles. -/
theorem ambiguity {n D t : ℕ} (w : Strategy n t → ℝ) (hw : Distribution w) {ε : ℝ}
    (hε : 0 ≤ ε) (learns : Learns w D ε) {e : Finset (Fin n)} (he : e.card = 2) (S : Finset (Fin n)) :
    (∑ s, w s * bit (miss s.1 e S)) ≤ 2*ε + bit (D ≤ S.card) := by
  classical
  by_cases hv : S.card < D
  · rw [bit_neg (not_le.mpr hv), add_zero]
    let B := S \ e
    have hb : B.card < D := (Finset.card_le_card Finset.sdiff_subset).trans_lt hv
    have hd : Disjoint e B := Finset.disjoint_sdiff
    obtain ⟨O,hO,agree⟩ := coupled_oracles he hd
    let G := hidden e B
    let loss (s : Strategy n t) (k : Bool) : ℝ := if s.2 (fun i => O k (s.1 i)) = G k then 0 else 1
    have upper (k : Bool) : (∑ s, w s * loss s k) ≤ ε := learns (G k) (hidden_degree he hb k) (O k) (hO k)
    have inevitable (s : Strategy n t) : bit (miss s.1 e S) ≤ loss s false + loss s true := by
      by_cases hm : miss s.1 e S
      · rw [bit_pos hm]
        have hans : (fun i => O false (s.1 i)) = (fun i => O true (s.1 i)) := by
          funext i
          apply agree
          rcases hm i with h | h
          · exact .inl h
          · obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp h
            exact .inr (Finset.not_disjoint_iff.mpr ⟨x,(Finset.mem_sdiff.mp hy).1,Finset.mem_sdiff.mpr ⟨hx,(Finset.mem_sdiff.mp hy).2⟩⟩)
        have hgraph : G false ≠ G true := hidden_distinct he B
        simp only [loss, hans]
        split_ifs with h₁ h₂ <;> norm_num
        exact hgraph (h₁.symm.trans h₂)
      · rw [bit_neg hm]
        unfold loss
        split_ifs <;> norm_num
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => mul_le_mul_of_nonneg_left (inevitable s) (hw.1 s))
    simp_rw [mul_add, Finset.sum_add_distrib] at hsum
    linarith only [hsum,upper false,upper true]
  · rw [bit_pos (Nat.le_of_not_gt hv)]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => mul_le_mul_of_nonneg_left (bit_le_one (miss s.1 e S)) (hw.1 s))
    simpa only [mul_one,hw.2] using hsum.trans (show (∑ s, w s * 1) ≤ 2*ε+1 by simp [hw.2,hε])

end MISQueries
