module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace PackingFactorization

/-- The graph of a permutation, local position to zero-based rank. -/
abbrev Pattern (K : Nat) := Fin K ≃ Fin K

/-- Local physical slot of a prefix or suffix entry. Both bounds follow from
the standard inclusions of finite intervals. -/
def prefixSlot {K n : Nat} (hn : n < K) (i : Fin n) : Fin K :=
  Fin.castLE (Nat.le_of_lt hn) i

def suffixSlot {K n : Nat} (hn : n < K) (i : Fin n) : Fin K :=
  Fin.cast (Nat.sub_add_cancel (Nat.le_of_lt hn)) (Fin.natAdd (K-n) i)

/-- A legal boundary is a positive proper overlap whose physical prefix and
suffix slots have the same relative order. -/
structure Overlap {K : Nat} (p : Pattern K) where
  size : Nat
  positive : 0 < size
  proper : size < K
  agrees : ∀ i h : Fin size,
    p (prefixSlot proper i) ≤ p (prefixSlot proper h) ↔
      p (suffixSlot proper i) ≤ p (suffixSlot proper h)

/-- A cut counts ranks strictly below the frontier, including both sentinels. -/
abbrev Cut (K : Nat) := Fin (K+1)

def anchorCount {K} {p : Pattern K} (a : Overlap p) (suffix : Bool) (c : Cut K) : Nat :=
  (Finset.univ.filter (fun i : Fin a.size =>
    let slot : Fin K := if suffix then suffixSlot a.proper i
      else prefixSlot a.proper i
    (p slot).val < c.val)).card

/-- At an outward step the two cuts must contain exactly the same shared ranks.
When walking to the right the current window uses its suffix. -/
def Cross {K} {p : Pattern K} (right : Bool) (a : Overlap p) (c d : Cut K) : Prop :=
  anchorCount a right c = anchorCount a (!right) d

/-- The list records all cuts after the initial cut, in the outward direction. -/
inductive Walk {K} {p : Pattern K} (right : Bool) :
    Cut K → List (Overlap p) → List (Cut K) → Prop
  | nil (c) : Walk right c [] []
  | step {a c d w ds} : Cross right a c d → Walk right d w ds →
      Walk right c (a::w) (d::ds)

def Profile {K} {p : Pattern K} (right : Bool) (m : Overlap p) (h : Nat)
    (w : List (Overlap p)) (cs : List (Cut K)) : Prop :=
  ∃ c ds, cs = c::ds ∧ anchorCount m (!right) c = h ∧ Walk right c w ds

def TwoProfiles {K} {p : Pattern K} (right : Bool) (m : Overlap p) (h : Nat)
    (w : List (Overlap p)) := ∃ cs ds, Profile right m h w cs ∧ Profile right m h w ds ∧ cs ≠ ds

/-- The finite test compares all cut walks through at most K+1 added windows.
A discrepancy is an immediately occupiable seam gap. -/
def Marked {K} {p : Pattern K} (A : Set (Overlap p)) (right : Bool) (m : Overlap p) (h : Nat) :=
  ∃ w, (∀ a ∈ w, a ∈ A) ∧ w.length ≤ K+1 ∧ TwoProfiles right m h w

end PackingFactorization
