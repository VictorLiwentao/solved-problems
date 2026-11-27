module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace SymmetricERM

abbrev Point (B r : ℕ) := Fin B × Fin r
abbrev Label (r : ℕ) := Finset (Fin r)
abbrev Code (B r : ℕ) := Equiv.Perm (Label r) × (Fin B → Label r)
abbrev Sample (B r m : ℕ) := Fin m → Point B r × Label r
abbrev Learner (B r : ℕ) := (m : ℕ) → Sample B r m → Code B r

/-- Points of a mask carry its code, and the other points carry the empty code.
One permutation relabels all blocks at once. -/
def classify {B r} (c : Code B r) (x : Point B r) : Label r :=
  c.1 (if x.2 ∈ c.2 x.1 then c.2 x.1 else ∅)

def mistakes {B r m} (c : Code B r) (s : Sample B r m) : ℕ :=
  (Finset.univ.filter fun i => classify c (s i).1 ≠ (s i).2).card

def ERM {B r} (A : Learner B r) : Prop :=
  ∀ m s c, mistakes (A m s) s ≤ mistakes c s

def Symmetric (B r : ℕ) : Prop :=
  ∀ (e : Equiv.Perm (Label r)) (c : Code B r), ∃ c', ∀ x, classify c' x = e (classify c x)

def NShatters {B r} (S : Finset (Point B r)) : Prop :=
  ∃ f g : Point B r → Label r, (∀ x ∈ S, f x ≠ g x) ∧
    ∀ T ⊆ S, ∃ c : Code B r, ∀ x ∈ S,
      classify c x = if x ∈ T then f x else g x

noncomputable def dimension (B r : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (@NShatters B r)).sup Finset.card

def Law {X : Type} [Fintype X] (p : X → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

noncomputable def risk {B r} (p : Point B r → ℝ) (t c : Code B r) : ℝ :=
  ∑ x, if classify c x = classify t x then 0 else p x

/-- Failure probability at error 1/4 under an ordered sample of independent draws. -/
noncomputable def failure {B r} (A : Learner B r) (m : ℕ) (p : Point B r → ℝ)
    (t : Code B r) : ℝ := by
  classical
  exact ∑ xs : Fin m → Point B r, if (1/4 : ℝ) <
    risk p t (A m (fun i => (xs i, classify t (xs i)))) then ∏ i, p (xs i) else 0

def Threshold {B r} (A : Learner B r) (n : ℕ) : Prop :=
  ∀ m ≥ n, ∀ p, Law p → ∀ t, failure A m p t ≤ 1/4

end SymmetricERM
