module

public import Std

@[expose] public section

namespace PackingPowers

/-- Positions in n+1 windows. A boundary contains its left and right anchors.
Each window has one private A, c middle positions, and b final-chain positions. -/
inductive Site (n b c : Nat) where
  | l (i : Fin (n+2))
  | r (i : Fin (n+2))
  | a (i : Fin (n+1))
  | mid (i : Fin (n+1)) (m : Fin c)
  | tail (i : Fin (n+1)) (m : Fin b)
  deriving DecidableEq

/-- Physical, zero-based index of a position in the permutation. Each window
begins at its L,R pair. Its final two positions begin the next window. -/
def position {n b c} : Site n b c → Nat
  | .l i => i.val*(b+c+3)
  | .r i => i.val*(b+c+3)+1
  | .a i => i.val*(b+c+3)+2
  | .mid i t => i.val*(b+c+3)+3+t.val
  | .tail i t => i.val*(b+c+3)+3+c+t.val

/-- The relative order in window i is L, A, R, the increasing middle chain,
the next L, the increasing tail chain, and the next R. The direct anchor
comparisons also cover an empty middle or tail. -/
def Window {n b c} (lt : Site n b c → Site n b c → Prop) (i : Fin (n+1)) : Prop :=
  lt (.l i.castSucc) (.a i) ∧ lt (.a i) (.r i.castSucc) ∧
  lt (.r i.castSucc) (.l i.succ) ∧ lt (.l i.succ) (.r i.succ) ∧
  (∀ t, lt (.r i.castSucc) (.mid i t) ∧ lt (.mid i t) (.l i.succ)) ∧
  (∀ a z : Fin c, a < z → lt (.mid i a) (.mid i z)) ∧
  (∀ t, lt (.l i.succ) (.tail i t) ∧ lt (.tail i t) (.r i.succ)) ∧
  (∀ a z : Fin b, a < z → lt (.tail i a) (.tail i z))

/-- A packing is a strict total order of the physical positions with the
prescribed relative order on each window. Sorting the positions gives their permutation ranks. -/
def Packing (n b c : Nat) := {lt : Site n b c → Site n b c → Prop //
  (∀ x, ¬ lt x x) ∧ (∀ x y z, lt x y → lt y z → lt x z) ∧
  (∀ x y, x ≠ y → lt x y ∨ lt y x) ∧ ∀ i, Window lt i}

/-- The physical positions exhaust the interval from zero through the last
right anchor, with each position represented exactly once. -/
def Physical (n b c : Nat) : Prop :=
  (∀ x y : Site n b c, position x = position y → x = y) ∧
  (∀ x : Site n b c, position x < (n+1)*(b+c+3)+2) ∧
  ∀ z < (n+1)*(b+c+3)+2, ∃ x : Site n b c, position x = z

/-- For every base k and every allowed pattern length K, the explicit overlap-two
pattern has k to the power n packings of n+1 windows, by a bijection with n independent choices. -/
theorem everyPower {k K : Nat} (positive : 1 ≤ k) (length : k+4 ≤ K) :
    ∃ b c : Nat, b+c+5 = K ∧ ∀ n,
      Physical n b c ∧ ∃ f : Fin (k^n) → Packing n b c,
        (∀ s t, f s = f t → s = t) ∧ ∀ p, ∃ s, f s = p := by sorry

end PackingPowers
