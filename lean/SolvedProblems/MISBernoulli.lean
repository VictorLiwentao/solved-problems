module

public import SolvedProblems.MISModel
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace MISQueries

variable {V : Type*} [DecidableEq V]

/-- Exact expectation after independently including each listed coordinate with
probability `p`; repeated coordinates, if present, are included by union. -/
noncomputable def average (p : ℝ) : List V → (Finset V → ℝ) → ℝ
  | [], f => f ∅
  | x :: xs, f => (1-p) * average p xs f + p * average p xs (fun S => f (insert x S))

namespace average

theorem const (p : ℝ) (xs : List V) (r : ℝ) : average p xs (fun _ => r) = r := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [average, ih]; ring

theorem add (p : ℝ) (xs : List V) (f g : Finset V → ℝ) :
    average p xs (fun S => f S + g S) = average p xs f + average p xs g := by
  induction xs generalizing f g with
  | nil => rfl
  | cons x xs ih => simp only [average, ih]; ring

theorem scale (p : ℝ) (xs : List V) (r : ℝ) (f : Finset V → ℝ) :
    average p xs (fun S => r * f S) = r * average p xs f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [average, ih]; ring

theorem sum {I : Type*} (p : ℝ) (xs : List V) (T : Finset I) (f : I → Finset V → ℝ) :
    average p xs (fun S => ∑ i ∈ T, f i S) = ∑ i ∈ T, average p xs (f i) := by
  classical
  induction T using Finset.induction with
  | empty => simp [const]
  | @insert i T hi ih => simp only [Finset.sum_insert hi, add, ih]

theorem mono {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) {f g : Finset V → ℝ} (h : ∀ S, f S ≤ g S) :
    average p xs f ≤ average p xs g := by
  induction xs generalizing f g with
  | nil => exact h ∅
  | cons x xs ih =>
    apply add_le_add (mul_le_mul_of_nonneg_left (ih h) (sub_nonneg.mpr hp'))
      (mul_le_mul_of_nonneg_left (ih (fun S => h (insert x S))) hp)

theorem nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) {f : Finset V → ℝ} (h : ∀ S, 0 ≤ f S) :
    0 ≤ average p xs f := by simpa only [const] using mono hp hp' xs h

/-- Positive correlation for increasing functions under biased independent coins. -/
theorem harris {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) (f g : Finset V → ℝ)
    (hf : Monotone f) (hg : Monotone g) :
    average p xs f * average p xs g ≤ average p xs (fun S => f S * g S) := by
  induction xs generalizing f g with
  | nil => rfl
  | cons x xs ih =>
    let f' := fun S => f (insert x S)
    let g' := fun S => g (insert x S)
    have h0 := ih f g hf hg
    have h1 := ih f' g' (fun _ _ h => hf (Finset.insert_subset_insert _ h))
      (fun _ _ h => hg (Finset.insert_subset_insert _ h))
    have df : 0 ≤ average p xs f' - average p xs f := sub_nonneg.mpr (mono hp hp' xs (fun S => hf (Finset.subset_insert _ S)))
    have dg : 0 ≤ average p xs g' - average p xs g := sub_nonneg.mpr (mono hp hp' xs (fun S => hg (Finset.subset_insert _ S)))
    have hex := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) (mul_nonneg df dg)
    dsimp only [average]
    change _ ≤ (1-p)*average p xs (fun S => f S * g S) + p*average p xs (fun S => f' S * g' S)
    calc
      _ ≤ (1-p)*(average p xs f * average p xs g) + p*(average p xs f' * average p xs g') := by
        dsimp only [f',g'] at *; linarith only [hex]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hp')) (mul_le_mul_of_nonneg_left h1 hp)

/-- Harris for all events in a list (or for nonnegative, increasing observables). -/
theorem harris_prod {I : Type*} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V)
    (T : Finset I) (f : I → Finset V → ℝ) (hm : ∀ i, Monotone (f i)) (hpos : ∀ i S, 0 ≤ f i S) :
    (∏ i ∈ T, average p xs (f i)) ≤ average p xs (fun S => ∏ i ∈ T, f i S) := by
  classical
  induction T using Finset.induction with
  | empty => simp [const]
  | @insert i T hi ih =>
    simp only [Finset.prod_insert hi]
    exact (mul_le_mul_of_nonneg_left ih (nonneg hp hp' xs (hpos i))).trans
      (harris hp hp' xs (f i) _ (hm i) (fun _ _ hab => Finset.prod_le_prod₀ (fun j _ => hpos j _) (fun j _ => hm j hab)))

end average
end MISQueries
