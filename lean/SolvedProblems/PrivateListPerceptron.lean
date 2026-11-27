module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PrivateList

noncomputable def dot {X : Type} [Fintype X] (weight v u : X → ℝ) : ℝ :=
  ∑ x, weight x * v x * u x

noncomputable def potential {X : Type} [Fintype X] (weight V w : X → ℝ) (l : ℝ) : ℝ :=
  ∑ x, weight x * (V x - l*w x)^2

theorem potential_step {X : Type} [Fintype X] (weight V w u : X → ℝ) (l : ℝ) :
    potential weight (fun x => V x + u x) w l =
      potential weight V w l + 2*dot weight V u - 2*l*dot weight w u + dot weight u u := by
  unfold potential dot
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem dot_neg {X : Type} [Fintype X] (weight v u : X → ℝ) :
    dot weight v (fun x => -u x) = -dot weight v u := by simp [dot]

theorem dot_neg_self {X : Type} [Fintype X] (weight u : X → ℝ) :
    dot weight (fun x => -u x) (fun x => -u x) = dot weight u u := by simp [dot]

/-- A threshold of height N in a margin representation forces at least d
perceptron mistakes when the binary search interval has 2^(d+1)-1 candidates. -/
theorem thresholdPerceptron {X : Type} [Fintype X] {N : ℕ} (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (u w : Fin N → X → ℝ) {a D : ℝ} (ha : 0 < a)
    (hu : ∀ i, dot p (u i) (u i) ≤ 2) (hw : ∀ i, dot p (w i) (w i) ≤ D)
    (lo : ∀ i j, j < i → dot p (w i) (u j) ≤ -a)
    (hi : ∀ i j, i < j → a ≤ dot p (w i) (u j))
    (d : ℕ) (hn : 2^(d+1)-1 ≤ N) : (d:ℝ)*a^2 ≤ 2*D := by
  let l := 2/a
  have hl : 0 < l := div_pos (by norm_num) ha
  have hla : l*a = 2 := div_mul_cancel₀ 2 ha.ne'
  have recur (n : ℕ) (s : ℕ) (hN : s + (2^(n+1)-1) ≤ N) (V : X → ℝ) :
      ∃ i : Fin N, s ≤ i.val ∧ i.val < s+(2^(n+1)-1) ∧
        2*(n:ℝ) ≤ potential p V (w i) l := by
    induction n generalizing s V with
    | zero =>
      refine ⟨⟨s,by simp at hN; omega⟩,le_rfl,by simp, ?_⟩
      simp only [Nat.cast_zero,mul_zero,potential]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (sq_nonneg _))
    | succ n ih =>
      let L := 2^(n+1)-1
      have pos : 0 < 2^(n+1) := Nat.two_pow_pos _
      have double : 2^(n+1+1)-1 = L+1+L := by
        rw [Nat.pow_succ]; dsimp [L];omega
      rw [double] at hN ⊢
      let j : Fin N := ⟨s+L,by omega⟩
      have advance (new : X → ℝ) (i : Fin N) (score : dot p V new ≤ 0)
          (margin : a ≤ dot p (w i) new) (cost : dot p new new ≤ 2) :
          potential p (fun x => V x + new x) (w i) l + 2 ≤ potential p V (w i) l := by
        rw [potential_step]
        have := mul_le_mul_of_nonneg_left margin hl.le
        linarith
      by_cases sign : dot p V (u j) ≤ 0
      · obtain ⟨i,lower,upper,deep⟩ := ih s (by change s+L ≤ _; omega) (fun x => V x + u j x)
        have lt : i < j := upper
        have step := advance (u j) i sign (hi i j lt) (hu j)
        refine ⟨i,lower,by change _ < s+L at upper; omega, ?_⟩
        push_cast; linarith
      · obtain ⟨i,lower,upper,deep⟩ := ih (s+L+1)
          (by change s+L+1+L ≤ _; omega) (fun x => V x + -u j x)
        have lt : j < i := by change j.val < i.val; dsimp [j];omega
        have negscore : dot p V (fun x => -u j x) ≤ 0 := by rw [dot_neg]; linarith
        have margin : a ≤ dot p (w i) (fun x => -u j x) := by rw [dot_neg]; linarith [lo i j lt]
        have step := advance (fun x => -u j x) i negscore margin ((dot_neg_self p _).le.trans (hu j))
        refine ⟨i,by omega,by change _ < s+L+1+L at upper;omega, ?_⟩
        push_cast; linarith
  obtain ⟨i,_,_,bound⟩ := recur d 0 (by simpa using hn) (fun _ => 0)
  have zero : potential p (fun _ => 0) (w i) l = l^2 * dot p (w i) (w i) := by
    unfold dot potential
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; ring
  rw [zero] at bound
  have est := bound.trans (mul_le_mul_of_nonneg_left (hw i) (sq_nonneg l))
  dsimp [l] at est
  field_simp at est
  nlinarith

end PrivateList
