module

public import SolvedProblems.ResistanceSoundness
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

open Finset
open scoped Matrix Classical

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete the two-element orbits of an involution from the complete graph.
Its fixed vertices retain all edges. -/
def minusMatching (σ : Equiv.Perm V) (hσ : Function.Involutive σ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ y ≠ σ x
  symm := ⟨fun x y h ↦ ⟨h.1.symm, fun he ↦ h.2 (by rw [he,hσ])⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

noncomputable def current (a b : V) (x : V) : ℝ :=
  (if x = a then 1 else 0) - (if x = b then 1 else 0)

noncomputable def matchingPotential (σ : Equiv.Perm V) (a b : V) (x : V) : ℝ :=
  let n : ℝ := Fintype.card V
  current a b x / n + (current a b x - current a b (σ x)) / (n*(n-2))

private theorem lap_minus (σ : Equiv.Perm V) (hσ : Function.Involutive σ) (f : V → ℝ) (x : V) :
    ((minusMatching σ hσ).lapMatrix ℝ *ᵥ f) x =
      (Fintype.card V : ℝ) * f x - (∑ y, f y) - (f x - f (σ x)) := by
  classical
  let G := minusMatching σ hσ
  change (G.lapMatrix ℝ *ᵥ f) x = _
  rw [G.lapMatrix_mulVec_apply']
  have part : G.neighborFinset x ⊆ univ.erase (σ x) := by
    intro y hy
    have adj := (G.mem_neighborFinset x y).mp hy
    exact mem_erase.mpr ⟨adj.2, mem_univ _⟩
  rw [Finset.sum_subset part (by
    intro y hy hn
    have he : x = y := by
      by_contra hne
      exact hn ((G.mem_neighborFinset x y).mpr ⟨hne,(mem_erase.mp hy).1⟩)
    rw [he, sub_self])]
  have all := Finset.sum_erase_add univ (f := fun y ↦ f x - f y) (mem_univ (σ x))
  rw [show (∑ y : V, (f x - f y)) = (Fintype.card V : ℝ) * f x - ∑ y, f y by
    rw [Finset.sum_sub_distrib]; simp] at all
  linarith

/-- An explicit solution of all Kirchhoff equations after deleting a matching,
with no choice of matrix inverse or numerical tolerance. -/
theorem matching_potential (σ : Equiv.Perm V) (hσ : Function.Involutive σ)
    (nlarge : 2 < Fintype.card V) (a b : V) :
    ResistanceLifts.UnitPotential (minusMatching σ hσ) a b (matchingPotential σ a b) := by
  classical
  let n : ℝ := Fintype.card V
  let d := current a b
  have hn : (2:ℝ) < n := by dsimp [n]; exact_mod_cast nlarge
  have hn0 : n ≠ 0 := by linarith
  have hn2 : n - 2 ≠ 0 := by linarith
  have hd : ∑ y, d y = 0 := by simp [d, current, Finset.sum_sub_distrib]
  have he : ∑ y, d (σ y) = ∑ y, d y := Equiv.sum_comp σ d
  have zero : ∑ y, matchingPotential σ a b y = 0 := by
    change (∑ y, (d y/n + (d y-d (σ y))/(n*(n-2)))) = 0
    simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, he, hd]
    simp
  ext x
  rw [lap_minus, zero]
  change n * (d x/n + (d x-d (σ x))/(n*(n-2))) - 0 -
    (d x/n + (d x-d (σ x))/(n*(n-2)) - (d (σ x)/n + (d (σ x)-d (σ (σ x)))/(n*(n-2)))) = d x
  rw [hσ]
  field_simp
  ring

end ResistanceRecovery
