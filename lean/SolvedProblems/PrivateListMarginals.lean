module

public import SolvedProblems.PrivateListRanks
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrivateList

open MeasureTheory Set
open scoped Classical

def Empirical {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (e : ℝ) : Prop :=
  ∀ s : Sample k m, Consistent s → (∑ i, omission A s (s i).1 (s i).2) ≤ m*e

theorem high_omission {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (s : Sample k m) (x : Point) :
    ∃ y : Label k, 1/(k+1:ℝ) ≤ omission A s x y := by
  let μ := A.law s
  have prob : IsProbabilityMeasure μ := A.normalized s
  let E (y : Label k) := {w | y ∉ A.predict w x}
  have all : ⋃ y, E y = univ := by
    apply Set.eq_univ_of_forall
    intro w
    apply mem_iUnion.mpr
    by_contra! h
    have eq : A.predict w x = Finset.univ := Finset.eq_univ_of_forall (fun y => by
      by_contra hy; exact h y hy)
    have size := A.listSize w x
    simp [eq] at size
  have bound : 1 ≤ ∑ y, omission A s x y := by
    have := measureReal_iUnion_fintype_le (μ := μ) E
    rwa [all,probReal_univ] at this
  have total : (∑ _i : Label k, 1/(k+1:ℝ)) = 1 := by
    simp [ne_of_gt (show (0:ℝ)<k+1 by positivity)]
  obtain ⟨y,_,hy⟩ := Finset.exists_le_of_sum_le (f := fun _ : Label k => 1/(k+1:ℝ))
    (g := fun y => omission A s x y) Finset.univ_nonempty (total.le.trans bound)
  exact ⟨y,hy⟩

theorem low_omission {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) {s : Sample k m}
    (hm : 0 < m) (consistent : Consistent s) (y : Label k)
    (balanced : m ≤ 2*(k+1)*(Finset.univ.filter fun i => (s i).2 = y).card)
    (emp : Empirical A (1 / (200*(k+1:ℝ)^2))) :
    ∃ i, (s i).2 = y ∧ omission A s (s i).1 y ≤ 1/(100*(k+1:ℝ)) := by
  let I := Finset.univ.filter fun i => (s i).2 = y
  have proportion : (m:ℝ) ≤ 2*(k+1:ℝ)*I.card := by exact_mod_cast balanced
  have nn : 0 < I.card := by
    by_contra! hn
    have zero : I.card = 0 := by omega
    change m ≤ 2*(k+1)*I.card at balanced
    simp [zero] at balanced
    omega
  have restricted : (∑ i ∈ I, omission A s (s i).1 (s i).2) ≤ m*(1/(200*(k+1:ℝ)^2)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => measureReal_nonneg)).trans
      (emp s consistent)
  have bound : (m:ℝ)*(1/(200*(k+1:ℝ)^2)) ≤ (∑ _i ∈ I, 1/(100*(k+1:ℝ))) := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    have pos : (0:ℝ)<k+1 := by positivity
    field_simp
    nlinarith
  obtain ⟨i,hi,low⟩ := Finset.exists_le_of_sum_le (Finset.card_pos.mp nn) (restricted.trans bound)
  have lab := (Finset.mem_filter.mp hi).2
  exact ⟨i,lab,by simpa [lab] using low⟩

theorem line_radius {m} (f : Fin (m+1) → ℝ) (e : ℝ) (h : ∀ j : Fin m, |f j.succ - f j.castSucc| ≤ e)
    (i : Fin (m+1)) : |f i-f 0| ≤ i.val*e := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · simp
  · calc
      _ ≤ |f j.succ-f j.castSucc| + |f j.castSucc-f 0| := abs_sub_le .. 
      _ ≤ e + j.castSucc.val*e := add_le_add (h j) ih
      _ = _ := by simp; ring

theorem grid_jump {m} (f : Cell m → ℝ) {e : ℝ} (he : 0 ≤ e) (u v : Cell m)
    (big : 4*m*e < f u - f v) :
    (∃ j : Fin m, ∃ h, e ≤ |f (j.succ,h)-f (j.castSucc,h)|) ∨
      ∃ j : Fin m, ∃ h, e ≤ |f (h,j.succ)-f (h,j.castSucc)| := by
  by_contra! small
  obtain ⟨hs,vs⟩ := small
  have rad (a : Cell m) : |f a - f (0,0)| ≤ 2*m*e := by
    calc
      _ ≤ |f a - f (0,a.2)| + |f (0,a.2)-f (0,0)| := abs_sub_le .. 
      _ ≤ a.1.val*e+a.2.val*e := add_le_add
        (line_radius (fun i => f (i,a.2)) e (fun j => (hs j _).le) _)
        (line_radius (fun i => f (0,i)) e (fun j => (vs j _).le) _)
      _ ≤ _ := by
        have hu : (a.1.val:ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ a.1.isLt
        have hv : (a.2.val:ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ a.2.isLt
        nlinarith [mul_le_mul_of_nonneg_right hu he,mul_le_mul_of_nonneg_right hv he]
  linarith [(abs_le.mp (rad u)).2,(abs_le.mp (rad v)).1]

end PrivateList
