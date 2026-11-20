module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace FussDyck

/-- The number of north steps immediately before each successive east step.
Expanding entry vᵢ into vᵢ north steps followed by one east step recovers the path.
For m > 0, a path to (m*n,n) above x = m*y must end in an east step:
its predecessor cannot be (m*n,n-1). -/
abbrev Word (n b : Nat) := Fin b → Fin (n+1)

def prefixN (v : Word n b) (t : Nat) : Nat :=
  ((List.ofFn (fun i => (v i).val)).take t).sum

def positions (v : Word n b) (h : Nat) : Finset (Fin b) :=
  Finset.univ.filter (fun i => h < (v i).val)

/-- Each positive run ends in one NE and each run of length at least two
ends in one NNE. The first condition fixes the total number of north steps. -/
def Stats (v : Word n b) (k j : Nat) :=
  prefixN v b = n ∧ (positions v 0).card = k ∧ (positions v 1).card = j

def RationalPath (v : Word n b) := ∀ t ≤ b, n*t ≤ b * prefixN v t

/-- At the end of each east step x = t and y is the number of north steps so far. -/
def FussPath (m : Nat) (v : Word n (m*n)) := ∀ t ≤ m*n, t ≤ m * prefixN v t

noncomputable def freeCount (n b k j : Nat) : Nat := by
  classical
  exact Fintype.card {v : Word n b // Stats v k j}

noncomputable def rationalCount (n b k j : Nat) : Nat := by
  classical
  exact Fintype.card {v : Word n b // Stats v k j ∧ RationalPath v}

noncomputable def pathCount (m n k j : Nat) : Nat := by
  classical
  exact Fintype.card {v : Word n (m*n) // Stats v k j ∧ FussPath m v}

def hCoeff (k s j : Nat) : Nat :=
  if s = 0 then if j = 0 then 1 else 0
  else if j = 0 then 0 else k.choose j * (s-1).choose (j-1)

end FussDyck
