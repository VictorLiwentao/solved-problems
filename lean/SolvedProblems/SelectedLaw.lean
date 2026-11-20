module

public import SolvedProblems.SelectedClass
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace SelectedDisagreement

/-- A nonnegative preference, ordered as fallback, named hypotheses by their binary mask, central. -/
noncomputable def pref : Hyp → ℝ
  | .fallback => 0
  | .central => 3
  | .named a => 2 - 1 / ((a : ℝ) + 1)

/-- Sum the weighted test over the first k ordinary points and the first k markers. -/
noncomputable def weight (p : Point → ℝ) (k : Nat) (f : Point → ℝ) : ℝ :=
  Nat.rec 0 (fun i r => r + p (.ordinary i) * f (.ordinary i) + p (.marker i) * f (.marker i)) k

/-- A discrete probability law has nonnegative atom masses with partial sums increasing to one. -/
def Law (p : Point → ℝ) :=
  (∀ x, 0 ≤ p x) ∧ (∀ k, weight p k (fun _ => 1) ≤ 1) ∧
    ∀ r : ℝ, r < 1 → ∃ k, r < weight p k (fun _ => 1)

/-- Integrate over m independent draws, restricting each coordinate to the first k pairs of atoms.
These finite products exhaust the countable sample space as k increases. -/
noncomputable def iid (p : Point → ℝ) (k m : Nat) (f : List Point → ℝ) : ℝ :=
  Nat.rec (motive := fun _ => (List Point → ℝ) → ℝ) (fun h => h [])
    (fun _ ih h => weight p k (fun x => ih (fun s => h (x :: s)))) m f

/-- Indicator of disagreement with the target at one point. -/
noncomputable def miss (t g : Hyp) (x : Point) : ℝ := if label t x = label g x then 0 else 1

/-- The true disagreement probability exceeds e when some finite partial sum already exceeds it. -/
def bad (p : Point → ℝ) (t g : Hyp) (e : ℝ) := ∃ k, e < weight p k (miss t g)

/-- Indicator that the hypothesis selected on this target-labelled sample has true loss above e. -/
noncomputable def event (p : Point → ℝ) (t : Hyp) (e : ℝ) (s : List Point) : ℝ := by
  classical
  exact if bad p t (select (observe t s)) e then 1 else 0

end SelectedDisagreement
