module

public import SolvedProblems.ProjectiveZFCore

@[expose] public section

namespace ProjectiveZF

open Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- The actual elements, relative to the membership relation of the model. -/
abbrev El (s : V) := {a : V // a ∈ s}

include M

theorem edge_typed {X Y f a b : V} (hf : IsMap X Y f) (he : Edge f a b) : a ∈ X ∧ b ∈ Y := by
  obtain ⟨p,pair,mem⟩ := he
  obtain ⟨x,hx,y,hy,rep⟩ := hf.1 _ mem
  obtain ⟨rfl,rfl⟩ := pair_coords M pair rep
  exact ⟨hx,hy⟩

theorem graph_ext {X Y f g : V} (hf : IsMap X Y f) (hg : IsMap X Y g)
    (same : ∀ a ∈ X, ∀ b, Edge f a b ↔ Edge g a b) : f = g := by
  apply M.ext
  have sub {s t : V} (hs : IsMap X Y s) (h : ∀ a ∈ X, ∀ b, Edge s a b → Edge t a b) : ∀p, p ∈ s → p ∈ t := by
    intro p hp
    obtain ⟨a,ha,b,_,pair⟩ := hs.1 _ hp
    obtain rfl := (pair_iff M _ _ _).mp pair
    exact (edge_iff M _ _ _).mp (h a ha b ((edge_iff M _ _ _).mpr hp))
  exact fun p => ⟨sub hf (fun a ha b => (same a ha b).mp) p,sub hg (fun a ha b => (same a ha b).mpr) p⟩

/-- Every definable binary relation gives an internal set of ordered pairs
on prescribed domains, by a single instance of Separation. -/
theorem graphSeparation (X Y : V) (R : V → V → Prop) (h : Binary R) :
    ∃ f : V, (∀ p, p ∈ f ↔ ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧ R x y ∧ IsPair x y p) ∧
      ∀ x y, Edge f x y ↔ x ∈ X ∧ y ∈ Y ∧ R x y := by
  let P (p : V) := ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧ R x y ∧ IsPair x y p
  have d : Unary P := by
    unfold Unary P
    repeat' first | apply defBinary h | apply defPair | apply defMem | apply defAnd | apply defEx | zf_terms
  obtain ⟨f,rep⟩ := M.separation (pairBound M X Y) P d
  have mem (p : V) : p ∈ f ↔ P p := by
    rw [rep]
    refine ⟨And.right,fun hp => ⟨?_,hp⟩⟩
    obtain ⟨x,hx,y,hy,_,pair⟩ := hp
    exact (pair_iff M _ _ _).mp pair ▸ pair_mem_bound M hx hy
  refine ⟨f,mem,?_⟩
  intro x y
  rw [edge_iff M,mem]
  constructor
  · rintro ⟨a,ha,b,hb,r,p⟩
    obtain ⟨rfl,rfl⟩ := ordered_inj M ((pair_iff M _ _ _).mp p)
    exact ⟨ha,hb,r⟩
  · rintro ⟨hx,hy,r⟩
    exact ⟨x,hx,y,hy,r,(pair_iff M _ _ _).mpr rfl⟩

/-- A definable total functional relation has an internal function graph.
The graph is supplied by Separation; there is no selection of internal
preimages using the ambient axiom of choice. -/
theorem mapFrom (X Y : V) (R : V → V → Prop) (h : Binary R)
    (total : ∀ x ∈ X, ∃ y, y ∈ Y ∧ R x y)
    (unique : ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Y, R x y → R x z → y = z) :
    ∃ f : V, IsMap X Y f ∧ ∀ x y, Edge f x y ↔ x ∈ X ∧ y ∈ Y ∧ R x y := by
  obtain ⟨f,mem,edge⟩ := graphSeparation M X Y R h
  refine ⟨f,⟨?_,?_,?_⟩,edge⟩
  · intro p hp
    obtain ⟨a,ha,b,hb,_,rep⟩ := (mem p).mp hp
    exact ⟨a,ha,b,hb,rep⟩
  · intro a ha
    obtain ⟨b,hb,rel⟩ := total a ha
    exact ⟨b,(edge a b).mpr ⟨ha,hb,rel⟩⟩
  · intro x y z hy hz
    obtain ⟨hx,hy,ry⟩ := (edge x y).mp hy
    obtain ⟨_,hz,rz⟩ := (edge x z).mp hz
    exact unique x hx y hy z hz ry rz

/-- The internal exponential contains precisely the function graphs that are
sets of the model. It is obtained by separating them from a power set. -/
noncomputable def exponential (X I : V) : V :=
  (M.separation (power M (pairBound M I X)) (IsMap I X) (defMap (termParam _) (termParam _) (termVar ()))).choose

@[simp] theorem mem_exponential {X I f : V} : f ∈ exponential M X I ↔ IsMap I X f := by
  have rule := (M.separation (power M (pairBound M I X)) (IsMap I X)
    (defMap (termParam _) (termParam _) (termVar ()))).choose_spec f
  change f ∈ exponential M X I ↔ _ at rule
  rw [rule]
  refine ⟨And.right,fun h => ⟨(mem_power M).mpr ?_,h⟩⟩
  intro t ht
  obtain ⟨a,ha,b,hb,rep⟩ := h.1 _ ht
  exact (pair_iff M _ _ _).mp rep ▸ pair_mem_bound M ha hb

end ProjectiveZF
