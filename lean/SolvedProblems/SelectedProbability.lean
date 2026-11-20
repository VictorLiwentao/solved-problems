module

public import SolvedProblems.SelectedDisagreement
public import SolvedProblems.SelectedRate
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace SelectedDisagreement

/-- Probability of selecting a hypothesis with disagreement mass greater than ε after m IID
draws. The increasing finite sample cubes exhaust all ordered m-tuples of this countable domain. -/
noncomputable def errorProbability (p : Point → ℝ) (t : Hyp) (m : Nat) (ε : ℝ) : ℝ :=
  sSup (Set.range (fun k => iid p k m (event p t ε)))

/-- The full IID error probability obeys the sample bound. A single sample threshold
works for every distribution and every target at the given accuracy and confidence. -/
theorem pacProbability {ε : ℝ} (positive : 0 < ε) (small : ε < 1) :
    (∀ p, Law p → ∀ t m, 1 ≤ m → errorProbability p t m ε ≤
      2 * (1-ε)^m + (m : ℝ) * (1-ε)^(m-1)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ N : Nat, ∀ m ≥ N, ∀ p, Law p → ∀ t, errorProbability p t m ε < δ) := by
  obtain ⟨_, _, _, _, _, _, _, finiteBound⟩ := selectedSeparation
  have bound (p) (law : Law p) (t m) (hm : 1 ≤ m) :
      errorProbability p t m ε ≤ 2 * (1-ε)^m + (m : ℝ) * (1-ε)^(m-1) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact finiteBound p law t m ε hm positive small k
  refine ⟨bound, ?_⟩
  intro δ hd
  obtain ⟨N, eventually⟩ := SelectedRate.decays positive small hd
  refine ⟨max 1 N, ?_⟩
  intro m hm p law t
  exact (bound p law t m ((Nat.le_max_left ..).trans hm)).trans_lt
    (eventually m ((Nat.le_max_right ..).trans hm))

end SelectedDisagreement
