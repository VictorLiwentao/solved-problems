module

public import Std

@[expose] public section

namespace GenerationThreshold

/-- Keep one representative of each datum. Its position in this list is immaterial. -/
def distinct [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then distinct xs else x :: distinct xs

abbrev Language := Nat → Prop
abbrev Class := Language → Prop

/-- Smaller endpoint first, so an unordered observation has just one encoding. -/
structure Edge where
  lo : Nat
  hi : Nat
  ordered : lo < hi
  deriving DecidableEq

def crosses (H : Language) (e : Edge) := ¬ (H e.lo ↔ H e.hi)
def fresh (s : List Edge) (x : Nat) := ∀ e ∈ s, x ≠ e.lo ∧ x ≠ e.hi

noncomputable def violations (H : Language) (s : List Edge) : Nat := by
  classical exact (s.filter (fun e => decide (¬ crosses H e))).length

def works (G : List Edge → Nat) (H : Language) (k t : Nat) :=
  ∀ s, t ≤ (distinct s).length → violations H s ≤ k → fresh s (G s) ∧ H (G s)

def uniform (C : Class) (k t : Nat) := ∃ G, ∀ H, C H → works G H k t

def obstruction (C : Class) (k : Nat) (E : List Edge) :=
  (∃ H, C H ∧ violations H E ≤ k) ∧
  ¬ ∃ x, fresh E x ∧ ∀ H, C H → violations H E ≤ k → H x

/-- Lists model finite samples and finite transversals. -/
def hits (answers sample : List Nat) (H : Language) :=
  ∃ x ∈ answers, x ∉ sample ∧ H x

def listUniform (C : Class) (k t : Nat) :=
  ∃ G : List Nat → List Nat, ∀ s, (G s).length ≤ k ∧
    ∀ H, C H → (∀ x ∈ s, H x) → t ≤ (distinct s).length → hits (G s) s H

def listObstruction (C : Class) (k : Nat) (I : List Nat) :=
  ∃ F : Class, (∃ H, F H) ∧ (∀ H, F H → C H) ∧
    (∀ x, x ∈ I ↔ ∀ H, F H → H x) ∧
    ¬ ∃ a : List Nat, a.length ≤ k ∧ ∀ H, F H → hits a I H

end GenerationThreshold

namespace GenerationThreshold

/-- B₀,B₁,B₂,N are the four residue classes modulo four. -/
def threeSupport (i : Fin 3) (x : Nat) := x % 4 < 3 ∧ x % 4 ≠ i.val

end GenerationThreshold
