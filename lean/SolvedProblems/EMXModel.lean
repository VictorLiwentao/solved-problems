module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace EMX

/-- Block index j represents the manuscript parameter t = j+2. -/
abbrev width (j : ℕ) := j+2
abbrev Row (j : ℕ) := Fin (2^width j)
abbrev Col (j : ℕ) := Fin (width j)
abbrev Cell (j : ℕ) := Row j × Col j
abbrev Point := (j : ℕ) × Cell j
abbrev Holes (j : ℕ) := {s : Finset (Cell j) // s.card = width j}
abbrev Hyp := (j : ℕ) × Holes j

def support (h : Hyp) : Finset Point :=
  h.2.1ᶜ.map (Function.Embedding.sigmaMk h.1)

def omittedRow (j : ℕ) (i : Row j) : Holes j :=
  ⟨Finset.univ.image (fun k : Col j => (i,k)), by
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
    simp⟩

def baseline : Hyp := ⟨0, omittedRow 0 0⟩

/-- An ordered message of length at most d. The decoder can see an auxiliary
symbol and the sample-size bound through its choice of decoding function. -/
abbrev Message (X : Type) (d : ℕ) := (l : Fin (d+1)) × (Fin l.val → X)

def Reconstructs (d a m : ℕ) (D : Fin a → Message Point d → Hyp) : Prop :=
  ∀ xs : Fin m → Point, (∃ h : Hyp, ∀ i, xs i ∈ support h) →
    ∃ b w, (∀ i, ∃ k, w.2 i = xs k) ∧ ∀ i, xs i ∈ support (D b w)

end EMX
