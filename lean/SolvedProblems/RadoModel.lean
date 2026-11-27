module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.WellFounded

@[expose] public section

namespace RadoSelection

/-- An unordered finite subset: only its membership predicate is data. Existence of
a listing is a proposition and supplies no simultaneous choice of enumerations. -/
structure Sample (A : Type u) where
  contains : A → Prop
  finite : ∃ l : List A, ∀ x, contains x ↔ x ∈ l

instance {A : Type u} : Membership A (Sample A) := ⟨Sample.contains⟩

namespace Sample
variable {A : Type u}

theorem ext {s t : Sample A} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  cases s with | mk s hs =>
    cases t with | mk t ht =>
      have e : s = t := funext fun x => propext (h x)
      cases e
      rfl

def ofList (l : List A) : Sample A := ⟨(· ∈ l), ⟨l, fun _ => Iff.rfl⟩⟩

def adjoin (a : A) (s : Sample A) : Sample A where
  contains x := x = a ∨ x ∈ s
  finite := by
    obtain ⟨l, hl⟩ := s.finite
    exact ⟨a :: l, fun x => (or_congr Iff.rfl (hl x)).trans List.mem_cons.symm⟩

theorem mem_adjoin {x a : A} {s : Sample A} : x ∈ adjoin a s ↔ x = a ∨ x ∈ s := Iff.rfl

/-- Finite induction into propositions never selects a listing as a function of s. -/
@[elab_as_elim] theorem induction {P : Sample A → Prop} (s : Sample A)
    (empty : P (ofList [])) (step : ∀ a s, P s → P (adjoin a s)) : P s := by
  obtain ⟨l, hl⟩ := s.finite
  have eq : s = ofList l := ext hl
  rw [eq]
  clear eq hl
  induction l with
  | nil => exact empty
  | cons a l ih =>
    have eq' : ofList (a :: l) = adjoin a (ofList l) :=
      ext fun _ => List.mem_cons
    exact eq' ▸ step a _ ih

end Sample

/-- A strict linear order on the indicated domain. -/
structure StrictOn {A : Type u} (D : A → Prop) (r : A → A → Prop) : Prop where
  irrefl : ∀ x, D x → ¬ r x x
  trans : ∀ {x y z}, D x → D y → D z → r x y → r y z → r x z
  compare : ∀ {x y}, D x → D y → x ≠ y → r x y ∨ r y x

/-- A proper ultrafilter on unordered finite samples containing every point cone.
All operations act on predicates, so the definition requires no decidable equality. -/
structure Fine {A : Type u} (U : (Sample A → Prop) → Prop) : Prop where
  proper : ¬ U (fun _ => False)
  mono : ∀ {p q : Sample A → Prop}, (∀ s, p s → q s) → U p → U q
  inter : ∀ {p q : Sample A → Prop}, U p → U q → U (fun s => p s ∧ q s)
  decide : ∀ p, U p ∨ U (fun s => ¬ p s)
  cone : ∀ x, U (fun s => x ∈ s)

/-- An extensional transitive membership system equipped with decreasing ranks.
Every member of a point of the system is represented by another point of the system. -/
structure Hierarchy (A : Type u) (I : Type v) [LT I] where
  rank : A → I
  mem : A → A → Prop
  lower : ∀ {t x}, mem t x → rank t < rank x
  ext : ∀ {x y}, (∀ t, mem t x ↔ mem t y) → x = y

end RadoSelection
