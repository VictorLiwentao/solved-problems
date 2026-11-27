module

public import SolvedProblems.ResistanceKernel

@[expose] public section

namespace ResistanceLifts

set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Direct integer verification of all columns of the analytic Green kernel. -/
theorem green_columns : ∀ t z x, columnHolds t z x := by decide +kernel

/-- Kept as an integer comparison so that every pair of resistances is checked
exactly, without numerical linear algebra or floating point. -/
def samePair (t : Bool) (a b : Fin 39) (e : Bool) : Prop :=
  ∃ flip : Bool, ∀ sheet : Bool,
    numerator t (a,e) (b,sheet) = numerator false (a,false) (b,xor sheet flip)

instance (t : Bool) (a b : Fin 39) (e : Bool) : Decidable (samePair t a b e) :=
  inferInstanceAs (Decidable (∃ _ : Bool, ∀ _ : Bool, (_ : ℤ) = _))

theorem green_pairs : ∀ t a b e, samePair t a b e := by decide +kernel

end ResistanceLifts
