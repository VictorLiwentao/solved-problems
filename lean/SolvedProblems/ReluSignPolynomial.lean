module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

open Polynomial
open scoped Polynomial

namespace ReluMoments

/-- Two points lie in the same open interval of the complement of finitely many cuts. -/
def SameCell (s : Finset ℝ) (x y : ℝ) : Prop :=
  x ∉ s ∧ y ∉ s ∧ ∀ c ∈ s, (x < c ↔ y < c)

private theorem sign_uniform (s : Set ℝ) (g : ℝ → ℝ)
    (h : ∀ x ∈ s, ∀ y ∈ s, 0 ≤ g x * g y) :
    (∀ x ∈ s, 0 ≤ g x) ∨ (∀ x ∈ s, g x ≤ 0) := by
  by_cases hp : ∀ x ∈ s, 0 ≤ g x
  · exact .inl hp
  · push Not at hp
    obtain ⟨x,hx,hneg⟩ := hp
    refine .inr fun y hy => ?_
    by_contra! hh
    exact (not_lt_of_ge (h x hx y hy)) (mul_neg_of_neg_of_pos hneg hh)

/-- A function of constant weak sign on every complementary interval has a
sign-matching polynomial of degree at most twice the number of cuts. Its real
zero set is exactly the given cuts, including cuts where the sign is unchanged. -/
theorem exists_sign_polynomial (s : Finset ℝ) (g : ℝ → ℝ)
    (hs : ∀ x y, SameCell s x y → 0 ≤ g x * g y) :
    ∃ q : ℝ[X], q.natDegree ≤ 2*s.card ∧
      (∀ x, q.eval x = 0 ↔ x ∈ s) ∧ (∀ x, 0 ≤ q.eval x * g x) ∧
      ∀ x y, (∀ c ∈ s, c < x) → (∀ c ∈ s, c < y) → 0 ≤ q.eval x * q.eval y := by
  classical
  induction s using Finset.induction_on_max generalizing g with
  | empty =>
    rcases sign_uniform Set.univ g (fun x _ y _ => hs x y (by simp [SameCell])) with hp | hn
    · exact ⟨1,by simp,by simp,fun x => by simpa using hp x trivial,by simp⟩
    · exact ⟨-1,by simp,by simp,fun x => by simpa using hn x trivial,by simp⟩
  | insert c s hmax ih =>
    let left := fun x => if x < c then g x else 0
    have hleft (x y) (hxy : SameCell s x y) : 0 ≤ left x * left y := by
      by_cases hx : x < c <;> by_cases hy : y < c <;> simp [left,hx,hy]
      exact hs x y ⟨by simp [hx.ne,hxy.1],by simp [hy.ne,hxy.2.1],
        fun k hk => by rcases Finset.mem_insert.mp hk with rfl|hk; exact iff_of_true hx hy; exact hxy.2.2 k hk⟩
    obtain ⟨q,hd,hzero,hweak,htail⟩ := ih left hleft
    have hw x (hx : x < c) : 0 ≤ q.eval x * g x := by simpa [left,hx] using hweak x
    have ht (x y : ℝ) (hx : c < x) (hy : c < y) :
        0 ≤ (q.eval x*g x) * (q.eval y*g y) := by
      have hq := htail x y (fun k hk => (hmax k hk).trans hx) (fun k hk => (hmax k hk).trans hy)
      have hnot (t : ℝ) (ht : c < t) (k : ℝ) (hk : k ∈ insert c s) : k < t := by
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact ht
        · exact (hmax _ hk).trans ht
      have hg := hs x y ⟨fun h => (hnot _ hx _ h).false,fun h => (hnot _ hy _ h).false,
        fun k hk => iff_of_false (not_lt_of_ge (hnot _ hx _ hk).le) (not_lt_of_ge (hnot _ hy _ hk).le)⟩
      nlinarith only [mul_nonneg hq hg]
    have hc : c ∉ s := fun hc => (hmax c hc).false
    have hfactor : (X-C c : ℝ[X]).natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    have hfactor' : (C c-X : ℝ[X]).natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    rcases sign_uniform (Set.Ioi c) (fun x => q.eval x*g x) (fun x hx y hy => ht x y hx hy) with hp | hn
    · refine ⟨q * (X-C c)^2,?_,?_,?_,?_⟩
      · rw [Finset.card_insert_of_notMem hc]
        have hk := natDegree_pow_le (p := (X-C c : ℝ[X])) (n := 2)
        exact (natDegree_mul_le).trans (by omega)
      · intro x
        simp [hzero,sub_eq_zero,or_comm]
      · intro x
        have hmul : 0 ≤ (x-c)^2 := sq_nonneg _
        simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C]
        rcases lt_trichotomy x c with hx|rfl|hx
        · nlinarith only [mul_nonneg hmul (hw x hx)]
        · simp
        · nlinarith only [mul_nonneg hmul (hp x hx)]
      · intro x y hx hy
        have hq := htail x y (fun k hk => hx k (Finset.mem_insert_of_mem hk))
          (fun k hk => hy k (Finset.mem_insert_of_mem hk))
        simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C]
        nlinarith only [mul_nonneg hq (mul_nonneg (sq_nonneg (x-c)) (sq_nonneg (y-c)))]
    · refine ⟨q * (C c-X),?_,?_,?_,?_⟩
      · rw [Finset.card_insert_of_notMem hc]
        exact natDegree_mul_le.trans (by omega)
      · intro x
        simp [hzero,sub_eq_zero,or_comm,eq_comm]
      · intro x
        simp only [eval_mul,eval_sub,eval_X,eval_C]
        rcases lt_trichotomy x c with hx|rfl|hx
        · nlinarith only [mul_nonneg (sub_nonneg.mpr hx.le) (hw x hx)]
        · simp
        · nlinarith only [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx.le) (hn x hx)]
      · intro x y hx hy
        have hq := htail x y (fun k hk => hx k (Finset.mem_insert_of_mem hk))
          (fun k hk => hy k (Finset.mem_insert_of_mem hk))
        have hprod := mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (hx c (Finset.mem_insert_self _ _)).le)
          (sub_nonpos.mpr (hy c (Finset.mem_insert_self _ _)).le)
        simp only [eval_mul,eval_sub,eval_X,eval_C]
        nlinarith only [mul_nonneg hq hprod]

end ReluMoments
