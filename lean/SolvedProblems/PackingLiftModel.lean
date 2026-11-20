module

public import Std

@[expose] public section

namespace PackingLift

/-- One-line, zero-based rank permutation. The stride is the window length
minus the prescribed overlap. Prefix and suffix positions have disjoint indices. -/
structure Seed where
  overlap : Nat
  stride : Nat
  positive : 0 < overlap
  disjoint : overlap ≤ stride
  rank : Fin (stride + overlap) → Fin (stride + overlap)
  injective : ∀ a b, rank a = rank b → a = b
  onto : ∀ b, ∃ a, rank a = b
  admissible : ∀ a b : Fin overlap,
    ((rank ⟨a, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_left _ _)⟩).val ≤ (rank ⟨b, Nat.lt_of_lt_of_le b.isLt (Nat.le_add_left _ _)⟩).val ↔
     (rank ⟨stride+a, Nat.add_lt_add_left a.isLt _⟩).val ≤ (rank ⟨stride+b, Nat.add_lt_add_left b.isLt _⟩).val)
  minimumInPrefix : ∃ a : Fin overlap, (rank ⟨a, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_left _ _)⟩).val = 0

/-- Reflexive transitive closure of the window rank comparisons. -/
inductive Reaches {α : Type} (edge : α → α → Prop) : α → α → Prop
  | refl (x) : Reaches edge x x
  | snoc {x y z} : Reaches edge x y → edge y z → Reaches edge x z

abbrev Slot (p : Seed) := Fin (p.stride + p.overlap)
abbrev Old (p : Seed) (j : Nat) := Fin (j*p.stride + p.overlap)

/-- A slot in window number i lies below the final endpoint of j windows. -/
theorem windowBound {i j stride tail slot : Nat} (hi : i < j) (hs : slot < stride + tail) :
    i * stride + slot < j * stride + tail := by
  have h := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h
  have hslot := Nat.add_lt_add_left hs (i * stride)
  rw [← Nat.add_assoc] at hslot
  exact Nat.lt_of_lt_of_le hslot (Nat.add_le_add_right h tail)

def oldAt (p : Seed) {j} (i : Fin j) (a : Slot p) : Old p j :=
  ⟨i.val*p.stride + a.val, windowBound i.isLt a.isLt⟩

def OldEdge (p : Seed) (j : Nat) (x y : Old p j) :=
  ∃ (i : Fin j) (a b : Slot p), x = oldAt p i a ∧ y = oldAt p i b ∧ p.rank a ≤ p.rank b

/-- The fresh physical positions are numbered from the last window back to
the first, in blocks D_j,H_j,D_{j-1},...,H_1,D_0. The total size is
j*(t+h)+t = (j+1)*t+j*h. This is only a numbering of positions. -/
abbrev Fresh (j t h : Nat) := Fin (j * (t+h) + t)
abbrev Lifted (p : Seed) (j t h : Nat) := Sum (Fresh j t h) (Old p j)

/-- Within a window, fresh ranks 0..t-1 are the new suffix, the next h
are the new middle, and the final t are the new prefix. The old positions
retain their one-line order within each of those three physical blocks. -/
abbrev LiftSlot (p : Seed) (t h : Nat) := Sum (Fin ((t+h)+t)) (Slot p)

def newAt {j t h} (i : Fin j) (a : Fin ((t+h)+t)) : Fresh j t h :=
  ⟨(j-1-i.val)*(t+h) + a.val, by
    exact windowBound (Nat.sub_lt_of_lt (Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) Nat.zero_lt_one)) a.isLt⟩

def liftAt (p : Seed) {j t h} (i : Fin j) : LiftSlot p t h → Lifted p j t h
  | .inl a => .inl (newAt i a)
  | .inr a => .inr (oldAt p i a)

def liftRank (p : Seed) {t h} : LiftSlot p t h → Nat
  | .inl a => a.val
  | .inr a => ((t+h)+t) + (p.rank a).val

def LiftEdge (p : Seed) (j t h : Nat) (x y : Lifted p j t h) :=
  ∃ (i : Fin j) (a b : LiftSlot p t h),
    x = liftAt p i a ∧ y = liftAt p i b ∧ liftRank p a ≤ liftRank p b

/-- The ordinal sum of the chain on all fresh positions and the original packing poset. -/
def Ordinal (p : Seed) {j t h} : Lifted p j t h → Lifted p j t h → Prop
  | .inl a, .inl b => a.val ≤ b.val
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr a, .inr b => Reaches (OldEdge p j) a b

end PackingLift

namespace PackingLift

/-- A packing as actual permutation ranks: each integer below n occurs
precisely once, and the rank assignment extends the window constraints. -/
structure Ranking (α : Type) (n : Nat) (le : α → α → Prop) where
  rank : α → Fin n
  injective : ∀ x y, rank x = rank y → x = y
  onto : ∀ r, ∃ x, rank x = r
  respects : ∀ x y, le x y → rank x ≤ rank y

/-- Splice the s smallest ranks in front of an existing ranking. -/
def insertChain {α : Type} {n : Nat} (s : Nat) (f : α → Fin n) : Fin s ⊕ α → Fin (s+n)
  | .inl x => ⟨x.val, Nat.lt_add_right n x.isLt⟩
  | .inr x => ⟨s+(f x).val, Nat.add_lt_add_left (f x).isLt s⟩

abbrev OldRanking (p : Seed) (j : Nat) :=
  Ranking (Old p j) (j*p.stride+p.overlap) (Reaches (OldEdge p j))

abbrev LiftRanking (p : Seed) (j t h : Nat) :=
  Ranking (Lifted p j t h) ((j*(t+h)+t)+(j*p.stride+p.overlap)) (Reaches (LiftEdge p j t h))

/-- An explicit bijection between the sets of rank permutations. -/
def PreservesCounts (p : Seed) (j t h : Nat) :=
  ∃ f : OldRanking p j → LiftRanking p j t h,
    (∀ r, (f r).rank = insertChain (j*(t+h)+t) r.rank) ∧
    (∀ r s, f r = f s → r = s) ∧ ∀ z, ∃ r, f r = z

/-- Left-to-right offset of a slot in the lifted one-line pattern, before
assigning any ranks. The blocks are new prefix, old prefix, new middle,
old middle, new suffix, old suffix. -/
def offset (p : Seed) {t h : Nat} : LiftSlot p t h → Nat
  | .inl a => if a.val < t then p.stride+t+h+a.val
        else if a.val < t+h then p.overlap+a.val else a.val-(t+h)
  | .inr a => if a.val < p.overlap then t+a.val
        else if a.val < p.stride then t+h+a.val else t+h+t+a.val

theorem offset_bounds (p : Seed) {t h} (a : LiftSlot p t h) :
    offset p a < (p.stride+t+h)+(p.overlap+t) := by
  cases a with
  | inl a =>
    simp only [offset]
    split
    · rename_i ha
      exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le ha (Nat.le_add_left _ _)) _
    · split
      · rename_i ha
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.lt_add_right (p.stride+t) (Nat.add_lt_add_left ha p.overlap)
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.lt_add_right (p.stride+p.overlap) (Nat.sub_lt_of_lt (b := t+h) a.isLt)
  | inr a =>
    simp only [offset]
    split
    · rename_i ha
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.lt_add_right (p.stride+t+h) (Nat.add_lt_add_left ha t)
    · split
      · rename_i ha
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.lt_add_right (p.overlap+t) (Nat.add_lt_add_left ha (t+h))
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.add_lt_add_left a.isLt (t+h+t)

def position (p : Seed) {j t h} (i : Fin j) (a : LiftSlot p t h) :
    Fin (j*(p.stride+t+h)+(p.overlap+t)) :=
  ⟨i.val*(p.stride+t+h)+offset p a, windowBound i.isLt (offset_bounds p a)⟩

end PackingLift
