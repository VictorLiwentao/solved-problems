module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Minimal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MISQueries

/-- An answer is legal when it is an inclusion-maximal independent subset of the query. -/
def Legal {V : Type*} (G : SimpleGraph V) (Q A : Finset V) : Prop :=
  Maximal (fun S : Finset V => S ⊆ Q ∧ ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y) A

abbrev Oracle (V : Type*) := Finset V → Finset V

def LegalOracle {V : Type*} (G : SimpleGraph V) (O : Oracle V) : Prop := ∀ Q, Legal G Q (O Q)

/-- A deterministic nonadaptive learner consists of a list of queries, followed by
a decoder acting on the list of oracle answers. -/
abbrev Strategy (n t : ℕ) :=
  (Fin t → Finset (Fin n)) × ((Fin t → Finset (Fin n)) → SimpleGraph (Fin n))

/-- A finite distribution on *all* deterministic behaviors models arbitrary coins.
Both the spaces of query schedules and answer decoders are finite. -/
def Distribution {X : Type*} [Fintype X] (w : X → ℝ) : Prop := (∀ x, 0 ≤ w x) ∧ ∑ x, w x = 1

noncomputable def error {n t : ℕ} (w : Strategy n t → ℝ) (G : SimpleGraph (Fin n)) (O : Oracle (Fin n)) : ℝ := by
  classical
  exact ∑ s, w s * (if s.2 (fun i => O (s.1 i)) = G then 0 else 1)

noncomputable def DegreeBound {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ) : Prop := by
  classical
  exact ∀ v, G.degree v ≤ D

/-- The guarantee quantifies over every legal oracle, including the worst choices
of maximal independent answers, on every graph with the stated upper degree bound. -/
def Learns {n t : ℕ} (w : Strategy n t → ℝ) (D : ℕ) (ε : ℝ) :=
  ∀ (G : SimpleGraph (Fin n)), DegreeBound G D → ∀ O, LegalOracle G O → error w G O ≤ ε

end MISQueries
