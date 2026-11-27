module

public import Mathlib.Computability.TuringDegree
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open Filter
namespace StrongSettling

/-- A computably enumerable set is presented by its increasing computable
array of 0/1 stage approximations. Stage zero may already contain entries. -/
structure Enumeration where
  read : ℕ → ℕ → ℕ
  effective : Computable₂ read
  bit : ∀ s x, read s x ≤ 1
  increases : ∀ {s t}, s ≤ t → ∀ x, read s x ≤ read t x

namespace Enumeration

noncomputable def answer (E : Enumeration) (x : ℕ) : ℕ := by
  classical
  exact if ∃ s, E.read s x = 1 then 1 else 0

theorem read_le (E : Enumeration) (s x : ℕ) : E.read s x ≤ E.answer x := by
  classical
  unfold answer
  split
  · exact E.bit _ _
  · rename_i h
    have v := E.bit s x
    have n : E.read s x ≠ 1 := fun e => h ⟨_,e⟩
    exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne v n)

theorem attains (E : Enumeration) (x : ℕ) : ∃ s, E.read s x = E.answer x := by
  classical
  by_cases h : ∃ s, E.read s x = 1
  · simp [answer,h]
  · have bound := E.read_le 0 x
    simp only [answer,h,ite_false] at bound ⊢
    exact ⟨0,Nat.eq_zero_of_le_zero bound⟩

/-- A pairing code for exactly the answers at inputs 0 through x. -/
def prefixCode (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | x+1 => Nat.pair (prefixCode f x) (f (x+1))

theorem prefix_eq {f g : ℕ → ℕ} (x : ℕ) :
    prefixCode f x = prefixCode g x ↔ ∀ i ≤ x, f i = g i := by
  induction x with
  | zero => simp [prefixCode]
  | succ x ih =>
    rw [prefixCode,prefixCode,Nat.pair_eq_pair,ih]
    constructor
    · rintro ⟨h,last⟩ i hi
      by_cases eq : i=x+1
      · simpa [eq] using last
      · exact h _ (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hi eq))
    · intro h
      exact ⟨fun i hi => h _ (Nat.le_succ_of_le hi), h _ le_rfl⟩

theorem stable_prefix (E : Enumeration) (x : ℕ) :
    ∃ s, prefixCode (E.read s) x = prefixCode E.answer x := by
  induction x with
  | zero => simpa [prefixCode] using E.attains 0
  | succ x ih =>
    obtain ⟨s,h⟩ := ih
    obtain ⟨t,ht⟩ := E.attains (x+1)
    use max s t
    apply (prefix_eq _).mpr
    intro i hi
    apply le_antisymm (E.read_le _ _)
    by_cases eq : i=x+1
    · subst i
      rw [← ht]
      exact E.increases (le_max_right _ _) _
    · rw [← (prefix_eq _).mp h i (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hi eq))]
      exact E.increases (le_max_left _ _) _

/-- The first stage by which every answer up to x is final, equivalently
the last entry stage below or at x (zero when nothing enters). -/
noncomputable def modulus (E : Enumeration) (x : ℕ) : ℕ := by
  classical
  exact Nat.find (E.stable_prefix x)

theorem final_at (E : Enumeration) {x s : ℕ} (hs : E.modulus x ≤ s) (i : ℕ) (hi : i ≤ x) :
    E.read s i = E.answer i := by
  classical
  have h : prefixCode (E.read (E.modulus x)) x = prefixCode E.answer x := Nat.find_spec (E.stable_prefix x)
  apply le_antisymm (E.read_le _ _)
  rw [← (prefix_eq _).mp h i hi]
  exact E.increases hs _

theorem modulus_le_iff (E : Enumeration) (x s : ℕ) :
    E.modulus x ≤ s ↔ ∀ i ≤ x, E.read s i = E.answer i := by
  classical
  exact ⟨fun h => E.final_at h,fun h => Nat.find_min' (E.stable_prefix x) ((prefix_eq _).mpr h)⟩

theorem modulus_mono (E : Enumeration) : Monotone E.modulus := by
  intro x y h
  apply (E.modulus_le_iff _ _).mpr
  exact fun i hi => E.final_at (x:=y) le_rfl i (hi.trans h)

end Enumeration

/-- Strong settling-time domination in the sense of Csima and Shore. -/
def Strong (A B : Enumeration) : Prop :=
  ∀ f g : ℕ → ℕ, Computable f → Computable g →
    ∀ᶠ x in atTop, f (A.modulus (g x)) < B.modulus x

end StrongSettling
