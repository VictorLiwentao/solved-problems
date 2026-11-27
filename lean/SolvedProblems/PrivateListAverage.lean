module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrivateList

open scoped Classical

/-- Expectation for an exactly uniform finite population. -/
noncomputable def avg {I : Type} [Fintype I] (f : I → ℝ) := (∑ i, f i) / Fintype.card I

theorem avg_mono {I : Type} [Fintype I] {f g : I → ℝ} (h : ∀ i, f i ≤ g i) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h i) (Nat.cast_nonneg _)

theorem avg_const {I : Type} [Fintype I] [Nonempty I] (c : ℝ) : avg (fun _ : I => c) = c := by
  simp [avg, ne_of_gt (show (0:ℝ) < Fintype.card I by exact_mod_cast Fintype.card_pos)]

theorem avg_add {I : Type} [Fintype I] (f g : I → ℝ) :
    avg (fun i => f i + g i) = avg f + avg g := by simp [avg,Finset.sum_add_distrib,add_div]

theorem avg_mul {I : Type} [Fintype I] (a : ℝ) (f : I → ℝ) :
    avg (fun i => a*f i) = a*avg f := by rw [avg,← Finset.mul_sum,avg,mul_div_assoc]

theorem avg_sum {I J : Type} [Fintype I] [Fintype J] (f : I → J → ℝ) :
    avg (fun i => ∑ j, f i j) = ∑ j, avg (fun i => f i j) := by
  simp only [avg,div_eq_mul_inv, ← Finset.sum_mul];rw [Finset.sum_comm]

theorem avg_equiv {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J) (f : J → ℝ) :
    avg (fun i => f (e i)) = avg f := by rw [avg,avg,e.sum_comp,Fintype.card_congr e]

theorem avg_prod {I J : Type} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    avg f = avg (fun i => avg (fun j => f (i,j))) := by
  rw [avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  simp only [avg,div_eq_mul_inv,← Finset.sum_mul];ring

theorem avg_eval {I J : Type} [DecidableEq I] [Fintype I] [Fintype J] [Nonempty J] (i : I) (f : J → ℝ) :
    avg (fun u : I → J => f (u i)) = avg f := by
  let e := Equiv.funSplitAt i J
  calc
    _ = avg (fun p : J × ({j // j ≠ i} → J) => f p.1) := avg_equiv e _
    _ = _ := by rw [avg_prod];simp only [avg_const]

theorem avg_eval₂ {I J : Type} [DecidableEq I] [Fintype I] [Fintype J] [Nonempty J] {i j : I} (h : j ≠ i)
    (f : J → J → ℝ) : avg (fun u : I → J => f (u i) (u j)) = avg (fun a => avg (f a)) := by
  let e := Equiv.funSplitAt i J
  calc
    _ = avg (fun p : J × ({j // j ≠ i} → J) => f p.1 (p.2 ⟨j,h⟩)) := avg_equiv e _
    _ = _ := by
      rw [avg_prod];exact congrArg avg (funext fun a => avg_eval (⟨j,h⟩ : {t // t≠i}) (f a))

noncomputable def oneIf (p : Prop) : ℝ := if p then 1 else 0

theorem avg_single {I : Type} [Fintype I] (i : I) : avg (fun j => oneIf (j=i)) = 1/Fintype.card I := by
  simp [avg,oneIf]

theorem avg_hit_bound {s m : ℕ} [NeZero m] (x : Fin m) :
    avg (fun u : Fin s → Fin m => oneIf (∃ i, u i = x)) ≤ s/m := by
  calc
    _ ≤ avg (fun u : Fin s → Fin m => ∑ i, oneIf (u i=x)) := by
      apply avg_mono; intro u; by_cases h : ∃ i, u i = x
      · obtain ⟨i,hi⟩ := h
        have le := Finset.single_le_sum (f := fun j => oneIf (u j=x))
          (fun j _ => by unfold oneIf; split <;> norm_num) (Finset.mem_univ i)
        simpa [oneIf,hi,show ∃ i, u i = x from ⟨i,hi⟩] using le
      · simp [oneIf,show ∀ i, u i ≠ x from fun i hi => h ⟨i,hi⟩]
    _ = _ := by
      have each (i : Fin s) : avg (fun u : Fin s → Fin m => oneIf (u i=x)) = 1/(m:ℝ) :=
        (avg_eval i (fun a => oneIf (a=x))).trans (by simpa only [Fintype.card_fin] using avg_single x)
      rw [avg_sum];simp only [each,Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem avg_collision_bound {s m : ℕ} [NeZero m] :
    avg (fun u : Fin s → Fin m => oneIf (¬Function.Injective u)) ≤ s^2/m := by
  let F (u : Fin s → Fin m) (i j : Fin s) := if i=j then 0 else oneIf (u i=u j)
  have nn (u i j) : 0 ≤ F u i j := by dsimp [F,oneIf]; split <;> (try split) <;> norm_num
  calc
    _ ≤ avg (fun u => ∑ i, ∑ j, F u i j) := by
      apply avg_mono;intro u
      by_cases h : Function.Injective u
      · simp only [oneIf,h,not_true_eq_false,↓reduceIte]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => nn ..
      · obtain ⟨i,j,hit,ne⟩ : ∃ i j, u i=u j ∧ i≠j := by
          by_contra! all; exact h (fun i j e => all i j e)
        have a := Finset.single_le_sum (f := F u i) (fun j _ => nn u i j) (Finset.mem_univ j)
        have b := Finset.single_le_sum (f := fun i => ∑ j, F u i j) (fun i _ => Finset.sum_nonneg fun j _ => nn u i j) (Finset.mem_univ i)
        simpa [oneIf,h,F,ne,hit] using a.trans b
    _ = ∑ i, ∑ j, avg (fun u => F u i j) := by simp only [avg_sum]
    _ ≤ ∑ _i : Fin s, ∑ _j : Fin s, (1/(m:ℝ)) := by
      apply Finset.sum_le_sum;intro i _;apply Finset.sum_le_sum;intro j _
      by_cases h : i=j
      · simp [F,h,avg_const]
      · simp only [F,h,↓reduceIte]
        apply (avg_eval₂ (Ne.symm h) (fun a b : Fin m => oneIf (a=b))).le.trans
        have each (a : Fin m) : avg (fun b : Fin m => oneIf (a=b)) = 1/(m:ℝ) := by
          simpa only [eq_comm,Fintype.card_fin] using avg_single (I := Fin m) a
        simp only [each,avg_const,le_refl]
    _ = _ := by simp;ring

end PrivateList
