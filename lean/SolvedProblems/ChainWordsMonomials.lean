module

public import SolvedProblems.ChainWords
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace ChainWords

/-- A monomial is its multiset of positive-variable indices, shifted to start at
zero. The order of a list of indices has no effect on this coefficient. -/
def IsPPartition {α : Type*} [PartialOrder α] (f t : α → ℕ) : Prop :=
  ∀ ⦃x y⦄, x < y → t x < t y ∨ t x = t y ∧ f x < f y

def Colorings {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ) (v : List ℕ) :=
  {t : α → ℕ // IsPPartition f t ∧ ((Finset.univ : Finset α).toList.map t).Perm v}

noncomputable def monomialCoefficient {α : Type*} [Fintype α] [PartialOrder α]
    (f : α → ℕ) (v : List ℕ) : ℕ := Nat.card (Colorings f v)

def key {α : Type*} (f t : α → ℕ) (x : α) : ℕ ×ₗ ℕ := toLex (t x, f x)

theorem key_injective {α : Type*} {f : α → ℕ} (hf : Function.Injective f) (t : α → ℕ) :
    Function.Injective (key f t) := by
  intro x y h
  exact hf (congrArg Prod.snd (toLex_inj.mp h))

/-- On a finite poset the usual cover inequalities suffice: assignments are
nondecreasing along every cover and strictly increase when the labels descend. -/
theorem partition_iff_covers {α : Type*} [Fintype α] [PartialOrder α] (f : α ↪ ℕ) (t : α → ℕ) :
    IsPPartition f t ↔ ∀ ⦃x y⦄, x ⋖ y → t x ≤ t y ∧ (color f x y = false → t x < t y) := by
  constructor
  · intro hp x y he
    rcases hp he.lt with lt | ⟨eq,hl⟩
    · exact ⟨lt.le,fun _ => lt⟩
    · exact ⟨eq.le,fun h => False.elim ((by simpa [color] using h : f y < f x).asymm hl)⟩
  · classical
    intro hc x y hxy
    let _ := Fintype.toLocallyFiniteOrder (α := α)
    have step {a b : α} (he : a ⋖ b) : key f t a < key f t b := by
      obtain ⟨hle,hs⟩ := hc he
      apply Prod.Lex.toLex_lt_toLex.mpr
      rcases hle.lt_or_eq with lt | eq
      · exact Or.inl lt
      · refine Or.inr ⟨eq,?_⟩
        have ne := f.injective.ne he.ne
        by_contra! hn
        have hdrop := lt_of_le_of_ne hn ne.symm
        exact (hs (by simpa [color] using hdrop)).ne eq
    have hkey : key f t x < key f t y := by
      induction lt_iff_transGen_covBy.mp hxy with
      | single he => exact step he
      | @tail z y hp he ih => exact (ih (lt_iff_transGen_covBy.mpr hp)).trans (step he)
    exact Prod.Lex.toLex_lt_toLex.mp hkey

/-- The allowed equalities of consecutive levels are a word. A false entry opens
a new level, where a descent of the vertex labels may occur. -/
def levels (a : ℕ) : List Bool → List ℕ
  | [] => [a]
  | b :: s => a :: levels (if b then a else a + 1) s

theorem levels_head (a : ℕ) (s : List Bool) : (levels a s).head? = some a := by cases s <;> rfl

theorem levels_length (a : ℕ) (s : List Bool) : (levels a s).length = s.length + 1 := by
  induction s generalizing a with
  | nil => rfl
  | cons b s ih => simp [levels,ih]

theorem levels_sorted (a : ℕ) (s : List Bool) : (levels a s).Pairwise (· ≤ ·) := by
  induction s generalizing a with
  | nil => simp [levels]
  | cons b s ih =>
    let a' := if b then a else a+1
    have ha : a ≤ a' := by cases b <;> simp [a']
    have hhead := levels_head a' s
    generalize hv : levels a' s = v at hhead
    obtain _ | ⟨y,l⟩ := v
    · simp at hhead
    · have hy : y = a' := by simpa using hhead
      have hv' := ih a'
      rw [hv] at hv'
      change (a :: levels a' s).Pairwise _
      rw [hv,List.pairwise_cons_cons_iff_of_trans]
      exact ⟨hy ▸ ha,hv'⟩

def Allows (mask word : List Bool) : Prop :=
  List.Forall₂ (fun m d => m = false ∨ d = true) mask word

theorem keyed_iff {α : Type*} (f t : α → ℕ) (l : List α) (mask : List Bool) (a : ℕ)
    (hv : l.map t = levels a mask) :
    l.Pairwise (fun x y => key f t x ≤ key f t y) ↔ Allows mask (descWord f l) := by
  induction mask generalizing a l with
  | nil =>
    have hl := congrArg List.length hv
    simp [levels] at hl
    rcases l with _ | ⟨x, _ | ⟨y,l⟩⟩ <;> simp_all [Allows,descWord]
  | cons b mask ih =>
    rcases l with _ | ⟨x, _ | ⟨y,l⟩⟩
    · simp [levels] at hv
    · have hl := congrArg List.length hv
      simp [levels_length] at hl
    · let a' := if b then a else a+1
      change t x :: (y :: l).map t = a :: levels a' mask at hv
      obtain ⟨hx,hy⟩ := List.cons.inj hv
      have hhead := congrArg List.head? hy
      rw [levels_head] at hhead
      have hy' : t y = a' := by simpa using hhead
      let _ : IsTrans α (fun x y => key f t x ≤ key f t y) := ⟨fun _ _ _ => le_trans⟩
      rw [List.pairwise_cons_cons_iff_of_trans, ih _ _ hy]
      change (_ ∧ _) ↔ List.Forall₂ _ (b :: mask) (color f x y :: descWord f (y :: l))
      rw [List.forall₂_cons]
      apply and_congr_left'
      cases b <;> simp [key,Prod.Lex.toLex_le_toLex,hx,hy',a',color]

theorem map_exists {α : Type*} (l : List α) (hn : l.Nodup) (v : List ℕ) (h : l.length = v.length) :
    ∃ t : α → ℕ, l.map t = v := by
  classical
  induction l generalizing v with
  | nil =>
    have : v = [] := List.length_eq_zero_iff.mp h.symm
    exact ⟨fun _ => 0, this.symm⟩
  | cons x l ih =>
    rcases v with _ | ⟨y,v⟩
    · simp at h
    · obtain ⟨t,ht⟩ := ih (List.nodup_cons.mp hn).2 v (by simpa using h)
      refine ⟨Function.update t x y, ?_⟩
      simp only [List.map_cons,Function.update_self,List.cons.injEq,true_and]
      rw [← ht]
      apply List.map_inj_left.mpr
      intro z hz
      have hzx : z ≠ x := by rintro rfl; exact (List.nodup_cons.mp hn).1 hz
      exact Function.update_of_ne hzx ..

theorem key_sorted_extension {α : Type*} [PartialOrder α] {f t : α → ℕ} (ht : IsPPartition f t)
    {l : List α} (hkey : l.Pairwise (fun x y => key f t x ≤ key f t y)) :
    l.Pairwise (fun x y => ¬ y < x) := by
  apply hkey.imp
  intro x y hk hyx
  have hs : key f t y < key f t x := Prod.Lex.toLex_lt_toLex.mpr (ht hyx)
  exact hs.not_ge hk

theorem partition_of_key_sorted {α : Type*} [PartialOrder α] {f t : α → ℕ}
    (hf : Function.Injective f) {l : List α} (he : IsExtension Set.univ l)
    (hkey : l.Pairwise (fun x y => key f t x ≤ key f t y)) : IsPPartition f t := by
  intro x y hxy
  have mem (x : α) : x ∈ l := (he.2.1 x).mpr (Set.mem_univ _)
  have all : l.Pairwise (fun a b => a < b → key f t a < key f t b) := by
    apply hkey.imp
    intro a b hk hab
    exact lt_of_le_of_ne hk ((key_injective hf t).ne hab.ne)
  have rev : l.Pairwise (fun a b => b < a → key f t b < key f t a) :=
    he.2.2.imp (fun hn hh => False.elim (hn hh))
  have h := List.Pairwise.forall_of_forall_of_flip (R := fun a b => a < b → key f t a < key f t b)
    (fun _ _ h => False.elim (lt_irrefl _ h)) all rev (mem x) (mem y) hxy
  exact Prod.Lex.toLex_lt_toLex.mp h

end ChainWords
