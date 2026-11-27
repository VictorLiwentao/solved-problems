module

public import SolvedProblems.ProjectiveZFOmega
public import Mathlib.Order.RelClasses

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- A pure first-order graph relation defining a map between two displayed
carrier sets, including the possibility of a definable class graph. -/
def Represents {X Y : V} (R : V → V → Prop) (f : El X → El Y) : Prop :=
  ∀ a b, R a.val b.val ↔ f a = b

include M

/-- A surjective definable map transfers the finite/cofinite property to its
image. An arbitrary internal subset is pulled back by a Separation formula. -/
theorem small_of_surjection {X Y : V} (small : SmallSubsets X) (r : V → V → Prop) (dr : Binary r)
    (f : El X → El Y) (rep : Represents r f) (surj : Surjective f) : SmallSubsets Y := by
  intro T
  let P (a : V) := ∃ b, b ∈ Y ∧ b ∈ T ∧ r a b
  have d : Unary P := by
    unfold Unary P
    repeat' first | apply defBinary dr | apply defEx | apply defAnd | apply defMem | zf_terms
  have eq (a : El X) : P a.val = ((f a).val ∈ T) := by
    apply propext
    refine ⟨fun ⟨b,by',bt,rel⟩ => ?_,fun h => ⟨(f a).val,(f a).property,h,(rep a (f a)).mpr rfl⟩⟩
    have v := (rep a ⟨b,by'⟩).mp rel
    exact (congrArg Subtype.val v) ▸ bt
  have cut {S : Set (El Y)} (h : (f ⁻¹' S).Finite) : S.Finite := (Set.image_preimage_eq S surj) ▸ h.image f
  have side := small_definable M small d
  simp only [eq] at side
  exact side.imp cut cut

/-- Finite image for maps from the atoms into an internally definable linear
order. This version may be used when only the graph relation has been supplied. -/
theorem finiteDefinableImage {X Y : V} (small : SmallSubsets X) [LinearOrder (El Y)]
    (O : V → V → Prop) (orderForm : Binary O) (ord : ∀ a b : El Y, O a.val b.val ↔ a < b)
    (R : V → V → Prop) (relForm : Binary R) (f : El X → El Y) (rep : Represents R f) : (range f).Finite := by
  classical
  let P (b : V) := ∃ a, a ∈ X ∧ R a b
  have defP : Unary P := by
    unfold Unary P
    repeat' first | apply defBinary relForm | apply defEx | apply defAnd | apply defMem | zf_terms
  obtain ⟨Z,hZ⟩ := M.separation Y P defP
  let g (x : El X) : El Z := ⟨(f x).val,(hZ _).mpr ⟨(f x).property,x.val,x.property,(rep x (f x)).mpr rfl⟩⟩
  let lift (z : El Z) : El Y := ⟨z.val,((hZ _).mp z.property).1⟩
  have inj : Injective lift := fun x y eq => Subtype.ext (congrArg (Subtype.val : El Y → V) eq)
  have onto : Surjective g := by
    intro z
    obtain ⟨_,a,ha,rel⟩ := (hZ z.val).mp z.property
    exact ⟨⟨a,ha⟩,Subtype.ext <| congrArg (Subtype.val : El Y → V) ((rep ⟨a,ha⟩ (lift z)).mp rel)⟩
  have rz : Represents R g := fun a z => (rep a (lift z)).trans (by exact ⟨fun h => Subtype.ext (congrArg (Subtype.val : El Y → V) h),fun h => Subtype.ext (congrArg (Subtype.val : El Z → V) h)⟩)
  have sm := small_of_surjection M small R relForm g rz onto
  let : LinearOrder (El Z) := LinearOrder.lift' lift inj
  let := finiteOfDefinableOrder M Z sm O orderForm (fun a b => ord (lift a) (lift b))
  have factor : lift ∘ g = f := rfl
  rw [← factor]
  exact (Set.finite_range lift).subset (Set.range_comp_subset_range g lift)

/-- The internally represented image of a function. -/
def ImageOf (X f Z : V) : Prop := ∀ y, y ∈ Z ↔ ∃ x, x ∈ X ∧ Edge f x y

/-- For an internally amorphous set in a pure omega-standard membership
model, every internal function into an internal linear order has an internally
finite image. The codomain, its order relation, the function and the image
are all sets of the model. -/
theorem orderedImageFinite {ω : V} (std : StandardOmega ω) {X Y : V} (am : AmorphousIn ω X)
    (order f : V) (lin : IsStrictTotalOrder (El Y) (fun a b => Edge order a.val b.val)) (map : IsMap X Y f) :
    ∃ Z : V, ImageOf X f Z ∧ FiniteIn ω Z := by
  classical
  let rel (a b : El Y) := Edge order a.val b.val
  let : IsStrictTotalOrder (El Y) rel := lin
  let : LinearOrder (El Y) := linearOrderOfSTO rel
  choose value hv using fun a : El X => map.2.1 a.val a.property
  let g (a : El X) : El Y := ⟨value a,(edge_typed M map (hv a)).2⟩
  have rep : Represents (Edge f) g := fun a b => ⟨fun h => Subtype.ext (map.2.2 _ _ _ (hv a) h),fun h => (congrArg Subtype.val h) ▸ hv a⟩
  have edgeF (z : V) : Binary (Edge z) := defEdge (termParam z) (termVar false) (termVar true)
  have small := (amorphousIn_iff M std X).mp am
  have finite := finiteDefinableImage M small.2 (Edge order) (edgeF order) (fun _ _ => Iff.rfl) (Edge f) (edgeF f) g rep
  obtain ⟨Z,hZ⟩ := representsFinite M Y (finite.image Subtype.val)
  have cut (z : V) : z ∈ Z ↔ ∃ a : El X, (g a).val = z := by
    change z ∈ elts Z ↔ _
    rw [hZ]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,h⟩
      exact ⟨a,h⟩
    · rintro ⟨a,h⟩
      exact ⟨g a,⟨a,rfl⟩,h⟩
  refine ⟨Z,?_,(finiteIn_iff M std Z).mpr ?_⟩
  · intro z
    rw [cut]
    constructor
    · rintro ⟨a,eq⟩
      exact ⟨a.val,a.property,eq ▸ hv a⟩
    · rintro ⟨a,ha,h⟩
      exact ⟨⟨a,ha⟩,map.2.2 _ _ _ (hv _) h⟩
  · exact ((hZ ▸ finite.image Subtype.val : (elts Z).Finite)).to_subtype

end ProjectiveZF
