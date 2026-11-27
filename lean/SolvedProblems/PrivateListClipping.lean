module

public import SolvedProblems.PrivateListPerceptron
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PrivateList

open scoped Classical

noncomputable def mass {X : Type} (p : X → ℝ) (E : Finset X) : ℝ := ∑ x ∈ E, p x

def Law {X : Type} [Fintype X] (p : X → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

def Domination {X : Type} (scale δ : ℝ) (p q : X → ℝ) : Prop :=
  ∀ E : Finset X, mass q E ≤ scale * mass p E + δ

theorem mass_le_one {X : Type} [Fintype X] {p : X → ℝ} (hp : Law p) (E : Finset X) :
    mass p E ≤ 1 := by
  rw [← hp.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hp.1 x)

noncomputable def clip {X : Type} (scale : ℝ) (p q : X → ℝ) (x : X) : ℝ := min (q x) (scale*p x)

theorem clip_event {X : Type} [Fintype X] {p q : X → ℝ} {scale δ : ℝ}
    (priv : Domination scale δ p q) (E : Finset X) :
    mass q E - δ ≤ mass (clip scale p q) E ∧ mass (clip scale p q) E ≤ mass q E := by
  classical
  let cut := Finset.univ.filter fun x => scale*p x < q x
  have excess : ∑ x, (q x - clip scale p q x) = mass q cut - scale * mass p cut := by
    unfold mass
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    unfold clip
    by_cases h : scale*p x < q x
    · simp [h,min_eq_right h.le]
    · simp [h,min_eq_left (le_of_not_gt h)]
  have e := priv cut
  have small : ∑ x ∈ E, (q x - clip scale p q x) ≤ ∑ x, (q x - clip scale p q x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sub_nonneg.mpr (min_le_left ..))
  refine ⟨?_,Finset.sum_le_sum (fun _ _ => min_le_left ..)⟩
  rw [Finset.sum_sub_distrib, excess] at small
  unfold mass at *
  linarith

noncomputable def density {X : Type} (scale : ℝ) (p q : X → ℝ) (x : X) : ℝ := clip scale p q x / p x

theorem density_props {X : Type} [Fintype X] {p q : X → ℝ} (hp : Law p) (hq : Law q)
    {scale : ℝ} (hscale : 0 ≤ scale) (x : X) :
    p x * density scale p q x = clip scale p q x ∧ 0 ≤ density scale p q x ∧ density scale p q x ≤ scale := by
  have cn : 0 ≤ clip scale p q x := le_min (hq.1 x) (mul_nonneg hscale (hp.1 x))
  have hi : clip scale p q x ≤ scale*p x := min_le_right .. 
  unfold density
  by_cases h : p x = 0
  · rw [h,mul_zero] at hi
    simp [h, hi.antisymm cn, hscale]
  · have pos := lt_of_le_of_ne (hp.1 x) (Ne.symm h)
    exact ⟨by field_simp, div_nonneg cn pos.le, (div_le_iff₀ pos).mpr hi⟩

theorem density_norm {X : Type} [Fintype X] {p q : X → ℝ} (hp : Law p) (hq : Law q)
    {scale : ℝ} (hscale : 0 ≤ scale) : dot p (density scale p q) (density scale p q) ≤ scale := by
  calc
    _ ≤ ∑ x, scale*q x := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨he,hn,hu⟩ := density_props hp hq hscale x
      rw [he]
      have cn : 0 ≤ clip scale p q x := le_min (hq.1 x) (mul_nonneg hscale (hp.1 x))
      calc
        _ ≤ clip scale p q x * scale := mul_le_mul_of_nonneg_left hu cn
        _ ≤ q x * scale := mul_le_mul_of_nonneg_right (min_le_left ..) hscale
        _ = _ := mul_comm .. 
    _ = _ := by rw [← Finset.mul_sum,hq.2,mul_one]

end PrivateList
