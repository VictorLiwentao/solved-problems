module

public import Std

@[expose] public section

namespace PackingSeparator

/-- Zero-based ranks of a length-k permutation. At overlap m its prefix and suffix
induce the same relative order on their m physical positions. -/
structure Pattern (k m : Nat) where
  rank : Nat → Nat
  short : m < k
  bounded : ∀ i < k, rank i < k
  distinct : ∀ i < k, ∀ j < k, rank i = rank j → i = j
  onto : ∀ r < k, ∃ i < k, rank i = r
  agrees : ∀ i < m, ∀ h < m,
    rank i ≤ rank h ↔ rank (k-m+i) ≤ rank (k-m+h)

/-- An occurrence is represented by its home window and local rank. Move up the
chain of ranks in a window, or cross an identified physical position in either
direction. The resulting paths generate precisely the packing comparisons. -/
inductive Below {k m} (p : Pattern k m) (j w r : Nat) : Nat → Nat → Prop
  | refl : Below p j w r w r
  | rise {v s t} : Below p j w r v s → s ≤ t → t < k → Below p j w r v t
  | right {v i} : Below p j w r v (p.rank (k-m+i)) → i < m → v+1 < j →
      Below p j w r (v+1) (p.rank i)
  | left {v i} : Below p j w r (v+1) (p.rank i) → i < m →
      Below p j w r v (p.rank (k-m+i))

/-- Choose a home and local rank in the packing with j windows. -/
abbrev Mark (k j : Nat) := Fin j × Fin k

/-- Weak comparison of two marked vertices in the generated order. -/
def LEPos {k m j} (p : Pattern k m) (x y : Mark k j) :=
  Below p j x.1.val x.2.val y.1.val y.2.val

/-- The marked vertex compares with every physical position. Each of its strict
lower and strict upper sets contains two incomparable positions. -/
def SeparatesBy {k j} (le : Mark k j → Mark k j → Prop) (x : Mark k j) := ∃ a b c d : Mark k j,
  (∀ y, le x y ∨ le y x) ∧
  (le a x ∧ ¬ le x a) ∧ (le b x ∧ ¬ le x b) ∧
  (¬ le a b ∧ ¬ le b a) ∧
  (le x c ∧ ¬ le c x) ∧ (le x d ∧ ¬ le d x) ∧
  (¬ le c d ∧ ¬ le d c)

/-- Existence of a separator in the generated packing order. -/
def HasSeparator {k m} (p : Pattern k m) (j : Nat) :=
  ∃ x : Mark k j, SeparatesBy (LEPos p) x

/-- The least reachable rank on the other side of an overlap, or k when there
is none. Index i names the same physical letter on both sides. -/
def advance (k : Nat) (a z : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => k
  | n+1 => if x ≤ a n then min (advance k a z x n) (z n) else advance k a z x n

/-- The rank test compares the two marked slots using at most m+1 crossings
from the first window towards the second. -/
def RankTest {k m j} (p : Pattern k m) (x y : Mark k j) :=
  let f := if x.1.val ≤ y.1.val then
    (fun s => advance k (fun i => p.rank (k-m+i)) p.rank s m)
    else (fun s => advance k p.rank (fun i => p.rank (k-m+i)) s m)
  Nat.rec x.2.val (fun _ r => f r)
    (min (m+1) ((y.1.val - x.1.val) + (x.1.val - y.1.val))) ≤ y.2.val

instance {k m j} (p : Pattern k m) (x y : Mark k j) : Decidable (RankTest p x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

def decideExistsMark {k j} (q : Mark k j → Prop) [DecidablePred q] : Decidable (∃ x, q x) :=
  decidable_of_iff (∃ w, ∃ r, q (w,r)) ⟨fun ⟨w,r,h⟩ => ⟨(w,r),h⟩, fun ⟨⟨w,r⟩,h⟩ => ⟨w,r,h⟩⟩

def decideForallMark {k j} (q : Mark k j → Prop) [DecidablePred q] : Decidable (∀ x, q x) :=
  decidable_of_iff (∀ w r, q (w,r)) ⟨fun h ⟨w,r⟩ => h w r, fun h w r => h (w,r)⟩

/-- Search the capped number of windows and their ranks using bounded comparisons. -/
def separatorTest {k m} (p : Pattern k m) (j : Nat) : Bool :=
  let n := min j (6*(m+1)+1)
  @decide (∃ x : Mark k n, SeparatesBy (RankTest p) x) (by
    unfold SeparatesBy
    iterate 5 (refine @decideExistsMark _ _ _ ?_; intro)
    refine @instDecidableAnd _ _ ?_ ?_
    · refine @decideForallMark _ _ _ ?_; intro; infer_instance
    · infer_instance)

end PackingSeparator
