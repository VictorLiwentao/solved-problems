module

public import Std
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace SelectedDisagreement

/-- Ordinary points are natural numbers. Each marker names a finite subset by its binary mask. -/
inductive Point
  | ordinary (i : Nat)
  | marker (a : Nat)
  deriving DecidableEq

/-- The central and fallback hypotheses together with one hypothesis per binary mask. -/
inductive Hyp
  | central
  | fallback
  | named (a : Nat)
  deriving DecidableEq

/-- Zero is shared. Each other label identifies its unique owner. -/
def label : Hyp → Point → Nat
  | .central, _ => 0
  | .fallback, .ordinary _ => 0
  | .fallback, .marker _ => 1
  | .named a, .ordinary i => if a.testBit i then a + 2 else 0
  | .named a, .marker b => if a = b then 0 else a + 2

/-- Agreement with the labels on a finite sample. -/
def fits (g : Hyp) (s : List (Point × Nat)) := ∀ x y, (x,y) ∈ s → label g x = y

/-- The learner prefers the fallback when possible, then a consistent named hypothesis,
and finally the central hypothesis. On realizable samples the named choice, when needed, is unique. -/
noncomputable def select (s : List (Point × Nat)) : Hyp := by
  classical
  exact if fits .fallback s then .fallback else
    if h : ∃ a, fits (.named a) s then .named h.choose else .central

/-- Label the sample using the specified target hypothesis. -/
def observe (t : Hyp) (s : List Point) := s.map fun x => (x, label t x)

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

/-- This fixed regularizer has a unique consistent minimum on every realizable sample.
Its selected disagreements shatter arbitrarily many ordinary points, and its iid error
probability satisfies the distribution-free bound from the draft. -/
theorem selectedSeparation :
    (∃ enc : Point → Nat, Function.Injective enc) ∧
    (∃ enc : Hyp → Nat, Function.Injective enc) ∧
    Function.Injective label ∧ Function.Injective pref ∧ (∀ g, 0 ≤ pref g) ∧
    (∀ s t, fits t s → fits (select s) s ∧
      ∀ g, fits g s → (g = select s ∨ pref (select s) < pref g)) ∧
    (∀ n : Nat, ∀ v : Nat → Bool, ∃ s : List Point, ∀ i < n,
      (label (select (observe .central s)) (.ordinary i) ≠ label .central (.ordinary i)
        ↔ v i = true)) ∧
    (∀ p : Point → ℝ, Law p → ∀ (t : Hyp) (m : Nat) (e : ℝ),
      1 ≤ m → 0 < e → e < 1 → ∀ k,
      iid p k m (event p t e) ≤ 2 * (1-e)^m + (m:ℝ) * (1-e)^(m-1)) := by
  sorry

end SelectedDisagreement

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
    (∀ δ : ℝ, 0 < δ → ∃ N : Nat, ∀ m ≥ N, ∀ p, Law p → ∀ t, errorProbability p t m ε < δ) := by sorry

end SelectedDisagreement
