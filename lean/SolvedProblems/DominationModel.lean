module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace DominationVC

/-- Two vertices belong to each other's closed incomparability neighborhood
exactly when neither is strictly below the other. Equality is allowed. -/
def Visible {V : Type*} [PartialOrder V] (v w : V) : Prop := ¬v < w ∧ ¬w < v

def incomparability (V : Type*) [PartialOrder V] : SimpleGraph V where
  Adj v w := v ≠ w ∧ Visible v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The set family of the actual closed graph neighborhoods. -/
noncomputable def closedFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.image fun v => Finset.univ.filter fun w => w = v ∨ G.Adj v w

/-- An arbitrary graph whose two labeled sides are cliques. The supplied relation
prescribes all cross-edges. -/
def twoCliques {a b : ℕ} (P : Fin a → Fin b → Prop) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj
    | .inl x, .inl y => x ≠ y
    | .inr x, .inr y => x ≠ y
    | .inl x, .inr y => P x y
    | .inr y, .inl x => P x y
  symm := ⟨fun x y => by
    cases x <;> cases y
    · exact Ne.symm
    · exact id
    · exact id
    · exact Ne.symm⟩
  loopless := ⟨fun x => by cases x <;> exact fun h => h rfl⟩

/-- Twice the number of locations required by the two blocks and the marker pairs. -/
def threshold (a b : ℕ) : ℕ := 2 * (2*a + 2*max 1 (Nat.clog 2 (b^2)))

end DominationVC
