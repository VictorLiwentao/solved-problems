module

public import SolvedProblems.ProjectiveFiniteTypes
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes

/-- A tuple of `k` coded finite/cofinite sets over an arbitrary structure. -/
abbrev Codes (A : Type*) (k : ℕ) := Fin k → Bool × Finset A

/-- Replace each position in a finite mask by the element at that position in the tuple. -/
noncomputable def decode {A B : Type*} {k : ℕ} (v : A → B) (p : Codes A k) : Codes B k :=
  open Classical in fun j => ((p j).1, (p j).2.image v)

/-- A relation symbol on `n` entries specifies two finite/cofinite codes on these
positions. Repeated positions between coordinates and empty masks are allowed. -/
def graphLanguage (k : ℕ) : Language where
  Functions _ := Empty
  Relations n := Codes (Fin n) k × Codes (Fin n) k

/-- Use every such relation to record the graph of a single self-map. -/
@[instance_reducible] noncomputable def graphStructure {A : Type*} {k : ℕ} (f : Codes A k → Codes A k) :
    (graphLanguage k).Structure A where
  funMap := fun {_} e => nomatch e
  RelMap := fun {_} r v => f (decode v r.1) = decode v r.2

/-- The relation on codes interpreted in the second model. The number of entries
and the two masks range freely; no bound on unknown output lengths is imposed. -/
def recorded {A : Type*} {k : ℕ} [(graphLanguage k).Structure A] (x y : Codes A k) : Prop :=
  ∃ (n : ℕ) (p q : Codes (Fin n) k) (v : Fin n → A),
    decode v p = x ∧ decode v q = y ∧ Structure.RelMap (L := graphLanguage k) (p,q) v

/-- Finitely many full first-order types at each finite arity. -/
def FiniteTypes (L : Language) (A : Type*) [L.Structure A] : Prop :=
  ∀ (ι : Type) [Finite ι], (typesIn L A ι).Finite

end ProjectiveTransfer
