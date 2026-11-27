module

public import SolvedProblems.MISScheduleBound
public import SolvedProblems.MISAdversary

@[expose] public section

namespace MISQueries

/-- The hidden-pair lower bound from the draft, with absolute constants. It
holds for any distribution on all deterministic nonadaptive schedules and
answer decoders, uniformly over every legal maximal-independent-set oracle. -/
theorem randomized_lower {n D t : ℕ} (hn : 2 ≤ n) (hd : 0 < D) (hdn : D ≤ n-1)
    (ht : 2*t ≤ n.choose 2) (w : Strategy n t → ℝ) (hw : Distribution w) {ε : ℝ}
    (hε : 0 ≤ ε) (learns : Learns w D ε) :
    Real.exp (-(4608*t/(D:ℝ)^2))/4 - Real.exp (-(D:ℝ)/4) ≤ ε := by
  classical
  let E := pairs (Fin n)
  let xs := (Finset.univ : Finset (Fin n)).toList
  let p := rate n D
  let m := exponent t D
  have hp := (rate_pos (n:=n) (by omega) hd).le
  have hp' := rate_le_one (n:=n) (by omega) (show D ≤ n by omega)
  have he (e : Finset (Fin n)) (he : e ∈ E) :
      average p xs (fun S => ∑ s, w s * bit (miss s.1 e S)) ≤ 2*ε + Real.exp (-(D:ℝ)/4) := by
    apply (average.mono hp hp' xs (ambiguity w hw hε learns (pair_mem.mp he))).trans
    rw [average.add, average.const]
    exact add_le_add le_rfl (degree_tail (n := n) (by omega) hd (by omega))
  have hsub (s : Strategy n t) : (n.choose 2 : ℝ)/2 * Real.exp (-m) ≤
      ∑ e ∈ E, average p xs (fun S => bit (miss s.1 e S)) := schedule_bound hn hd (by omega) ht _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => mul_le_mul_of_nonneg_left (hsub s) (hw.1 s))
  rw [← Finset.sum_mul, hw.2, one_mul] at hsum
  simp_rw [Finset.mul_sum] at hsum
  rw [Finset.sum_comm] at hsum
  have hupper := Finset.sum_le_sum he
  simp_rw [average.sum, average.scale] at hupper
  have hraw := hsum.trans hupper
  rw [Finset.sum_const, nsmul_eq_mul, show E.card = n.choose 2 from pair_count n] at hraw
  have hN : (0:ℝ) < n.choose 2 := by exact_mod_cast (Nat.choose_pos hn)
  have htmp : (n.choose 2:ℝ)*(Real.exp (-m)/2) ≤ (n.choose 2:ℝ)*(2*ε+Real.exp (-(D:ℝ)/4)) := by linarith only [hraw]
  have hdiv := (mul_le_mul_iff_right₀ hN).mp htmp
  change Real.exp (-m)/4 - Real.exp (-(D:ℝ)/4) ≤ ε
  linarith only [hdiv, Real.exp_pos (-(D:ℝ)/4)]

end MISQueries
