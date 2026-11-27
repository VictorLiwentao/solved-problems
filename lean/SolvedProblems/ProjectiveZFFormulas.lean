module

public import SolvedProblems.ProjectiveZFLogic

@[expose] public section

namespace ProjectiveZF

open FirstOrder FirstOrder.Language

variable {V ι κ : Type*} [Membership V V]

/-- Substituting projections and set parameters into a definable predicate
preserves pure first-order definability. -/
theorem defSubst {P : (ι → V) → Prop} (h : Definable P) (u : ι → (κ → V) → V) (hu : ∀ i, Term (u i)) :
    Definable (fun v => P (fun i => u i v)) := by
  obtain ⟨φ,hφ⟩ := h
  choose a ha using hu
  let idx : V ⊕ ι → V ⊕ κ := Sum.elim Sum.inl fun i => match a i with | .var j => .inr j | .param b => .inl b
  refine ⟨φ.relabel idx,fun v => ?_⟩
  rw [Formula.realize_relabel]
  have cut : (Sum.elim id v) ∘ idx = Sum.elim id (fun i => u i v) := by
    funext j
    rcases j with j|i
    · rfl
    · have eq := ha i v
      rcases hj : a i with j|c <;> simpa [idx,hj,Atom.eval] using eq
  rw [cut]
  exact hφ _

/-- Pure first-order definability with one or two displayed free arguments. -/
def Unary (P : V → Prop) := Definable (fun v : Unit → V => P (v ()))
def Binary (P : V → V → Prop) := Definable (fun v : Bool → V => P (v false) (v true))

theorem defUnary {P : V → Prop} (h : Unary P) {s : (ι → V) → V} (hs : Term s) :
    Definable (fun v => P (s v)) := defSubst h (fun _ => s) (fun _ => hs)

theorem defBinary {P : V → V → Prop} (h : Binary P) {s t : (ι → V) → V} (hs : Term s) (ht : Term t) :
    Definable (fun v => P (s v) (t v)) :=
  defSubst h (fun b => if b then t else s) (fun b => by cases b <;> assumption)

/-- Membership-language descriptions of singletons, unordered pairs, and
Kuratowski ordered pairs, with the represented set as the last argument. -/
def IsSingle (a z : V) : Prop := ∀ w, w ∈ z ↔ w = a
def IsDouble (a b z : V) : Prop := ∀ w, w ∈ z ↔ w = a ∨ w = b
def IsPair (a b z : V) : Prop := ∀ w, w ∈ z ↔ IsSingle a w ∨ IsDouble a b w

def Edge (f x y : V) : Prop := ∃ p, IsPair x y p ∧ p ∈ f

/-- Discharge the syntactic obligations left by a fixed first-order formula. -/
macro "zf_terms" : tactic => `(tactic| first | assumption | exact termVar _ | exact termParam _ | (simp only [Function.comp_assoc]; apply termReindex; assumption) | solve_by_elim (maxDepth := 6) only [*, termLift])

macro "zf_logic" : tactic => `(tactic| repeat' first
  | assumption
  | apply defIff | apply defAnd | apply defOr | apply defNot | apply defEx | apply defAll | apply defImp
  | apply defMem | apply defEq | zf_terms)

theorem defSingle {s t : (ι → V) → V} (hs : Term s) (ht : Term t) : Definable (fun v => IsSingle (s v) (t v)) := by
  unfold IsSingle
  zf_logic

theorem defDouble {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => IsDouble (s v) (t v) (u v)) := by unfold IsDouble; zf_logic

theorem defPair {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => IsPair (s v) (t v) (u v)) := by
  unfold IsPair
  apply defAll
  apply defIff
  · apply defMem <;> zf_terms
  · apply defOr
    · apply defSingle <;> zf_terms
    · apply defDouble <;> zf_terms

theorem defEdge {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => Edge (s v) (t v) (u v)) := by
  unfold Edge
  apply defEx
  apply defAnd
  · apply defPair <;> zf_terms
  · apply defMem <;> zf_terms

/-- A set of ordered pairs qualifying as a function from `X` into `Y`.
The last condition gives uniqueness for the entire range of the graph. -/
def IsMap (X Y f : V) : Prop :=
  (∀ p, p ∈ f → ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧ IsPair x y p) ∧
  (∀ x, x ∈ X → ∃ y, Edge f x y) ∧
  (∀ x y z, Edge f x y → Edge f x z → y = z)

macro "zf_map_formula" : tactic => `(tactic| repeat' first
  | assumption
  | apply defPair | apply defEdge
  | apply defIff | apply defAnd | apply defOr | apply defNot | apply defEx | apply defAll | apply defImp
  | apply defMem | apply defEq | zf_terms)

theorem defMap {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => IsMap (s v) (t v) (u v)) := by unfold IsMap; zf_map_formula

end ProjectiveZF
