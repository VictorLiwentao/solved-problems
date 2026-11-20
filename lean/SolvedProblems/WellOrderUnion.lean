module

public import SolvedProblems.WellOrderUnionModel
import SolvedProblems.WellOrderUnionBlocks
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.Order

public section
namespace WellOrderUnion

open Equiv

/-- Rigidity identifies an internal well-order with a single pointwise support for
its carrier. The converse uses an ambient well-order under that same support. -/
private theorem order_iff {A : Type u} {X : Type v} (act : Perm A →* Perm X) (S : Set X) :
    WellOrderable act S ↔ ∃ P : A → ℕ, ∀ g : Perm A, Preserves P g →
      ∀ x ∈ S, act g x = x := by
  constructor
  · rintro ⟨P,r,well,h⟩
    let : IsWellOrder S r := well
    refine ⟨P, fun g hg x hx => ?_⟩
    obtain ⟨e,he⟩ := h g hg
    let y : S := ⟨x,hx⟩
    have unique := (InitialSeg.refl r).eq_relIso e y
    exact (he y).symm.trans (congrArg Subtype.val unique)
  · rintro ⟨P,h⟩
    exact ⟨P,WellOrderingRel,inferInstance, fun g hg =>
      ⟨RelIso.refl _,fun x => (h _ hg _ x.prop).symm⟩⟩

/-- In the countable partition model, the union of an internally well-orderable family
of internally well-orderable sets admits an internal well-order. The uncountable
atom type can have arbitrary cofinality. -/
theorem unionTheorem {A : Type u} [Uncountable A] {X : Type v}
    (act : Equiv.Perm A →* Equiv.Perm X) (W : Set (Set X))
    (family : WellOrderable (setAction act) W) (members : ∀ S ∈ W, WellOrderable act S) :
    WellOrderable act (Set.sUnion W) := by
  obtain ⟨P,hP⟩ := (order_iff _ _).mp family
  obtain ⟨R,uniform⟩ := simultaneous_fixing act P
  apply (order_iff _ _).mpr
  refine ⟨R, fun g hg x hx => ?_⟩
  obtain ⟨S,hS,hs⟩ := Set.mem_sUnion.mp hx
  exact uniform S (fun f hf => hP _ hf _ hS) ((order_iff _ _).mp (members S hS)) g hg x hs

end WellOrderUnion
