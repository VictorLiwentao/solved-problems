module

public import SolvedProblems.SingletonDensityModel

@[expose] public section

namespace SingletonDensity

/-- Left endpoint of block j. Consecutive block lengths are j+3. -/
def start : Nat → Nat := Nat.rec 0 (fun j s => s+j+3)

/-- The finite block [start j,start (j+1)). -/
def block (j : Nat) : Finset Nat := (Finset.range (start (j+1))) \ (Finset.range (start j))

/-- Number of ranks in A in block j. -/
noncomputable def blockCount (A : Set Nat) (j : Nat) : Nat := by
  classical
  exact ((block j).filter (fun x => x ∈ A)).card

end SingletonDensity
