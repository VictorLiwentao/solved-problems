module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace ProjectiveBlocks

/-- A finite core and countably many blocks, each with `d` labelled positions. -/
abbrev Point (c d : ℕ) := Fin c ⊕ (ℕ × Fin d)

/-- Each of the `k` coordinates stores its finite/cofinite flag and its finite part. -/
abbrev Code (c d k : ℕ) := Fin k → Bool × Finset (Point c d)

/-- A block permutation fixes the core and preserves the position inside each block. -/
def relabel {c d : ℕ} (σ : Equiv.Perm ℕ) : Equiv.Perm (Point c d) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr σ (Equiv.refl _))

/-- Transport the actual finite subsets by the positionwise action. -/
def rename {c d k : ℕ} (σ : Equiv.Perm ℕ) (x : Code c d k) : Code c d k :=
  fun j => ((x j).1, (x j).2.map (relabel σ).toEmbedding)

/-- The self-map commutes with every block permutation. -/
def Equivariant {c d k : ℕ} (g : Code c d k → Code c d k) : Prop :=
  ∀ σ x, g (rename σ x) = rename σ (g x)

/-- The core and flags have `2^(k(1+c))` states, and there are `q` possible
patterns of a block, giving `q^q` output tables on input patterns. -/
def orbitBound (c d k : ℕ) : ℕ :=
  let q := 2 ^ (d * k)
  2 ^ (k * (1 + c)) * q ^ q

end ProjectiveBlocks
