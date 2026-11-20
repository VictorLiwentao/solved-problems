module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Order.WellFounded

@[expose] public section
namespace WellOrderUnion

open Equiv

/-- A coloring by natural numbers presents a partition into at most countably many blocks. -/
def Preserves {A : Type u} (P : A → ℕ) (g : Perm A) : Prop := ∀ x, P (g x) = P x

/-- Transport the action on objects to the action on sets by taking their images. -/
def setAction {A : Type u} {X : Type v} (act : Perm A →* Perm X) : Perm A →* Perm (Set X) where
  toFun g := (act g).setCongr
  map_one' := by ext S x; simp
  map_mul' g h := by
    ext S x
    simp only [map_mul, Equiv.Perm.mul_apply, setCongr_apply]
    rw [Set.image_image]
    rfl

/-- Internal well-orderability in the external permutation model. A single countable
partition supports the given well-order on S: each permutation preserving the partition
acts on S by an automorphism of the very same well-order. -/
def WellOrderable {A : Type u} {X : Type v} (act : Perm A →* Perm X) (S : Set X) : Prop :=
  ∃ (P : A → ℕ) (r : S → S → Prop), IsWellOrder S r ∧
    ∀ (g : Perm A), Preserves P g → ∃ e : r ≃r r, ∀ x : S, (e x).val = act g x.val

/-- In the countable partition model, the union of an internally well-orderable family
of internally well-orderable sets admits an internal well-order. The uncountable
atom type can have arbitrary cofinality. -/
theorem unionTheorem {A : Type u} [Uncountable A] {X : Type v}
    (act : Equiv.Perm A →* Equiv.Perm X) (W : Set (Set X))
    (family : WellOrderable (setAction act) W) (members : ∀ S ∈ W, WellOrderable act S) :
    WellOrderable act (Set.sUnion W) := by
  sorry

end WellOrderUnion
