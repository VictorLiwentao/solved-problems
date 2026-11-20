module

public import Std

@[expose] public section

namespace SelectedDisagreement

/-- Ordinary points are natural numbers. Each marker names a finite subset by its binary mask. -/
inductive Point
  | ordinary (i : Nat)
  | marker (a : Nat)
  deriving DecidableEq

/-- The central and fallback hypotheses together with one hypothesis per binary mask. -/
inductive Hyp
  | central
  | fallback
  | named (a : Nat)
  deriving DecidableEq

/-- Zero is shared. Each other label identifies its unique owner. -/
def label : Hyp → Point → Nat
  | .central, _ => 0
  | .fallback, .ordinary _ => 0
  | .fallback, .marker _ => 1
  | .named a, .ordinary i => if a.testBit i then a + 2 else 0
  | .named a, .marker b => if a = b then 0 else a + 2

/-- Agreement with the labels on a finite sample. -/
def fits (g : Hyp) (s : List (Point × Nat)) := ∀ x y, (x,y) ∈ s → label g x = y

/-- The learner prefers the fallback when possible, then a consistent named hypothesis,
and finally the central hypothesis. On realizable samples the named choice, when needed, is unique. -/
noncomputable def select (s : List (Point × Nat)) : Hyp := by
  classical
  exact if fits .fallback s then .fallback else
    if h : ∃ a, fits (.named a) s then .named h.choose else .central

/-- Label the sample using the specified target hypothesis. -/
def observe (t : Hyp) (s : List Point) := s.map fun x => (x, label t x)

end SelectedDisagreement
