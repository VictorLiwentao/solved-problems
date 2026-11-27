module

public import SolvedProblems.ProjectiveZFFunctions
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Range

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

include M

/-- The members of any externally finite set of model elements can be collected
into a single internal set using Pairing, Union and an empty Separation. -/
theorem representsFinite (seed : V) {S : Set V} (finite : S.Finite) : ∃ t : V, elts t = S := by
  classical
  induction S,finite using Set.Finite.induction_on with
  | empty =>
    obtain ⟨t,ht⟩ := M.separation seed (fun x => x ≠ x) (defNot (defEq (termVar ()) (termVar ())))
    refine ⟨t,Set.ext fun x => ?_⟩
    change x ∈ t ↔ False
    simp [ht]
  | @insert a S _ _ ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨both M (single M a) t,Set.ext fun x => ?_⟩
    change x ∈ both _ _ _ ↔ x = a ∨ x ∈ S
    rw [mem_both,mem_single,← ht]
    rfl

/-- The model contains the graph of any function on an externally finite set
of elements. This is a finite construction even when the function originally
appears as an external parameter. -/
theorem finiteGraph {X Y : V} [Finite (El X)] (f : El X → El Y) :
    ∃ g : V, IsMap X Y g ∧ ∀ (x : El X) (y : V), Edge g x.val y ↔ y = (f x).val := by
  let pair (x : El X) := ordered M x.val (f x).val
  obtain ⟨g,rep⟩ := representsFinite M X (Set.finite_range pair)
  have mem (p : V) : p ∈ g ↔ ∃ x : El X, ordered M x.val (f x).val = p := Set.ext_iff.mp rep p
  have edge (a b : V) : Edge g a b ↔ ∃ x : El X, x.val = a ∧ (f x).val = b := by
    rw [edge_iff M,mem]
    exact exists_congr fun x => ⟨ordered_inj M,fun ⟨ha,hb⟩ => by rw [ha,hb]⟩
  refine ⟨g,⟨?_,?_,?_⟩,?_⟩
  · intro p hp
    obtain ⟨x,h⟩ := (mem p).mp hp
    exact ⟨x.val,x.property,(f x).val,(f x).property,(pair_iff M _ _ _).mpr h.symm⟩
  · intro a ha
    let x : El X := ⟨a,ha⟩
    exact ⟨(f x).val,(edge _ _).mpr ⟨x,rfl,rfl⟩⟩
  · intro a b c h k
    obtain ⟨x,hx,hb⟩ := (edge _ _).mp h
    obtain ⟨y,hy,hc⟩ := (edge _ _).mp k
    obtain rfl : x = y := Subtype.ext (hx.trans hy.symm)
    exact hb.symm.trans hc
  · intro a b
    rw [edge]
    refine ⟨fun ⟨x,h,h'⟩ => ?_,fun h => ⟨a,rfl,h.symm⟩⟩
    obtain rfl : x = a := Subtype.ext h
    exact h'.symm

/-- The internal first-order assertion that the displayed sets are in bijection. -/
def Equinumerous (X Y : V) : Prop := ∃ f : V, IsMap X Y f ∧
  (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ Edge f x y) ∧ (∀ x z y, Edge f x y → Edge f z y → x = z)

omit M in
theorem defEquinumerous {ι : Type*} {s t : (ι → V) → V} (hs : Term s) (ht : Term t) :
    Definable (fun v => Equinumerous (s v) (t v)) := by
  unfold Equinumerous
  repeat' first | apply defMap | apply defEdge | apply defAnd | apply defImp | apply defAll | apply defEx
                | apply defEq | apply defMem | zf_terms

/-- Any internal bijection induces a bijection on the external elements.
Conversely, external bijections on finite domains have internal graphs. -/
theorem equiv_of_equinumerous {X Y : V} (h : Equinumerous X Y) : Nonempty (El X ≃ El Y) := by
  classical
  obtain ⟨g,map,onto,unique⟩ := h
  choose value edge using fun x : El X => map.2.1 x.val x.property
  let f (x : El X) : El Y := ⟨value x,(edge_typed M map (edge x)).2⟩
  refine ⟨Equiv.ofBijective f ⟨?_,?_⟩⟩
  · intro a b eq
    apply Subtype.ext
    have cut : value a = value b := congrArg Subtype.val eq
    exact unique _ _ _ (edge a) (cut ▸ edge b)
  · intro y
    obtain ⟨x,hx,hy⟩ := onto y.val y.property
    exact ⟨⟨x,hx⟩,Subtype.ext (map.2.2 _ _ _ (edge _) hy)⟩

theorem equinumerous_of_finite {X Y : V} [Finite (El X)] (e : El X ≃ El Y) : Equinumerous X Y := by
  obtain ⟨g,map,edge⟩ := finiteGraph M e
  refine ⟨g,map,?_,?_⟩
  · intro y hy
    let t : El Y := ⟨y,hy⟩
    exact ⟨(e.symm t).val,(e.symm t).property,(edge _ _).mpr (congrArg Subtype.val (e.apply_symm_apply t).symm)⟩
  · intro a b y ha hb
    let x : El X := ⟨a,(edge_typed M map ha).1⟩
    let z : El X := ⟨b,(edge_typed M map hb).1⟩
    have cut : (e x).val = (e z).val := ((edge x y).mp ha).symm.trans ((edge z y).mp hb)
    exact congrArg Subtype.val (e.injective (Subtype.ext cut))

end ProjectiveZF
