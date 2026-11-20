module

public import Std

@[expose] public section

namespace PackingCutoff

/-- The three positions in each consecutive block, in physical order. -/
inductive Lane | x | y | z deriving DecidableEq

/-- A position in the one-line word with `n` blocks. -/
abbrev Pos (n : Nat) := Fin n × Lane

/-- Integer label of a slot in the pattern. The block index starts at zero in each window. -/
def label (d block : Nat) : Lane → Nat
  | .x => 3 * block
  | .y => 3 * (block + d) + 1
  | .z => 3 * (block + 2*d) + 2

/-- A permutation represented by its strict total order on the labelled positions. -/
def linear {α : Type} (r : α → α → Prop) :=
  (∀ a, ¬r a a) ∧ (∀ a b c, r a b → r b c → r a c) ∧ (∀ a b, a ≠ b → r a b ∨ r b a)

/-- In `w+t` blocks there are `t+1` prescribed windows of width `w`, starting at blocks
`0,…,t`. Each comparison uses the slots’ indices relative to the start of its window. -/
def packs (w d t : Nat) (r : Pos (w+t) → Pos (w+t) → Prop) :=
  linear r ∧ ∀ (i : Nat), i ≤ t → ∀ a b, i ≤ a.1.val → a.1.val < i+w →
    i ≤ b.1.val → b.1.val < i+w → (r a b ↔ label d (a.1.val-i) a.2 < label d (b.1.val-i) b.2)

/-- Exactly one permutation satisfies all prescribed window comparisons. -/
def one (w d t : Nat) := ∃ r, packs w d t r ∧ ∀ s, packs w d t s → s = r

/-- Packing counts are unbounded if some prescribed window count admits at least
`m` different permutations for every finite `m`. -/
def unbounded (w d : Nat) := ∀ m, ∃ t,
  ∃ f : Fin m → (Pos (w+t) → Pos (w+t) → Prop),
    (∀ i, packs w d t (f i)) ∧ ∀ i j, f i = f j → i = j

end PackingCutoff
