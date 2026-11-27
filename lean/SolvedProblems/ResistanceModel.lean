module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

open scoped Matrix

namespace ResistanceLifts

/-- The two sheets over each vertex of the 39-vertex base graph. -/
abbrev Vertex := Fin 39 × Bool

/-- Literal signatures keep the old color and the multiset of labeled neighbors' colors.
Every vertex occurs in the multiset, including the vertex at distance zero. -/
def Color (D A : Type u) : ℕ → Type u
  | 0 => A
  | n + 1 => Color D A n × Multiset (D × Color D A n)

/-- The histogram of a vertex labeling, with one occurrence per vertex. -/
def histogram {V A : Type*} [Fintype V] (f : V → A) : Multiset A :=
  (Finset.univ : Finset V).val.map f

def refine {V : Type*} {D A : Type u} [Fintype V] (dist : V → V → D) (initial : V → A) :
    (n : ℕ) → V → Color D A n
  | 0, v => initial v
  | n + 1, v => (refine dist initial n v, histogram fun w => (dist v w, refine dist initial n w))

/-- Kirchhoff's equations for one unit of current injected at `a` and removed at `b`
with a unit conductance on each edge. -/
noncomputable def UnitPotential {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V) (u : V → ℝ) : Prop := by
  classical
  exact G.lapMatrix ℝ *ᵥ u = fun i => (if i = a then 1 else 0) - (if i = b then 1 else 0)

/-- Effective resistance is the voltage drop under a unit current. The fallback is
only relevant if Kirchhoff's equations are insoluble, e.g. in disconnected graphs. -/
noncomputable def resistance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V) : ℝ := by
  classical
  exact if h : ∃ u, UnitPotential G a b u then h.choose a - h.choose b else 0

/-- The characteristic polynomial records the full ordinary Laplacian spectrum
with multiplicities. -/
noncomputable def laplacianPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial ℝ := by
  classical
  exact (G.lapMatrix ℝ).charpoly

end ResistanceLifts
