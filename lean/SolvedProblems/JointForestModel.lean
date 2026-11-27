module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace JointForest

open SimpleGraph

/-- The unit-resistor effective resistance. Ground `v`, inject one unit at `u`,
and read the voltage at `u` from the inverse grounded Laplacian. The theorems
using this encoding assume that the graph is connected. -/
noncomputable def resistance {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : ℚ := by
  classical
  exact if h : u = v then 0 else
    ((G.lapMatrix ℚ).submatrix (Subtype.val : {w // w ≠ v} → V) (Subtype.val : {w // w ≠ v} → V))⁻¹ ⟨u,h⟩ ⟨u,h⟩

/-- Every color records the multiset itself, an injective choice of encoding. -/
abbrev Color : ℕ → Type
  | 0 => Unit
  | n + 1 => Multiset (ℕ × ℚ × Color n)

/-- Joint distance refinement, parameterized by its two pair labels. -/
noncomputable def color {V : Type*} [Fintype V] (labels : V → V → ℕ × ℚ) :
    (n : ℕ) → V → Color n
  | 0, _ => ()
  | n + 1, u => Finset.univ.val.map fun v =>
      ((labels u v).1, (labels u v).2, color labels n v)

noncomputable def jointLabels {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : ℕ × ℚ :=
  (G.dist u v, resistance G u v)

/-- Hosts agree if their vertex-color histograms agree at every finite round. -/
def Equivalent {V W : Type*} [Fintype V] [Fintype W]
    (a : V → V → ℕ × ℚ) (b : W → W → ℕ × ℚ) : Prop :=
  ∀ n, Finset.univ.val.map (color a n) = Finset.univ.val.map (color b n)

/-- Ordinary, unnormalized homomorphism counts, including repeated images. -/
noncomputable def homCount {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V) : ℕ :=
  Nat.card (F →g G)

end JointForest
