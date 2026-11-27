module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace WeakFrucht

abbrev Reach {V : Type u} (D : V → V → Prop) := Relation.ReflTransGen D

def Extensional {V : Type u} (D : V → V → Prop) : Prop :=
  ∀ x y, (∀ z, D x z ↔ D y z) → x = y

def AccessibleFrom {V : Type u} (D : V → V → Prop) (root : V) : Prop := ∀ y, Reach D root y

/-- A decoration preserves the root, preserves edges, and maps the successor
set of each source vertex onto that of its image. -/
def Decorates {V : Type u} {W : Type v} (D : V → V → Prop) (E : W → W → Prop)
    (root : V) (point : W) (p : V → W) : Prop :=
  p root = point ∧ (∀ {x y}, D x y → E (p x) (p y)) ∧ ∀ x z, E (p x) z → ∃ y, D x y ∧ p y = z

structure Iso {V : Type u} {W : Type v} (D : V → V → Prop) (E : W → W → Prop) where
  toEquiv : V ≃ W
  edges : ∀ x y, E (toEquiv x) (toEquiv y) ↔ D x y

def Iso.symm {V W} {D : V → V → Prop} {E : W → W → Prop} (f : Iso D E) : Iso E D where
  toEquiv := f.toEquiv.symm
  edges x y := by simpa using (f.edges (f.toEquiv.symm x) (f.toEquiv.symm y)).symm

theorem reach_map {V W} {D : V → V → Prop} {E : W → W → Prop} (f : V → W)
    (h : ∀ {x y}, D x y → E (f x) (f y)) {x y} (r : Reach D x y) : Reach E (f x) (f y) := by
  induction r with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (h e)

abbrev Below {V : Type u} (D : V → V → Prop) (x : V) := {y // Reach D x y}

def rootOf {V : Type u} (D : V → V → Prop) (x : V) : Below D x := ⟨x,.refl⟩

def inner {V : Type u} {D : V → V → Prop} {x : V} (a b : Below D x) : Prop := D a.val b.val

/-- The isomorphism is between the full induced rooted descendant graphs. -/
structure RootIso {V : Type u} {W : Type v} (D : V → V → Prop) (E : W → W → Prop) (x : V) (y : W) where
  iso : Iso (@inner _ D x) (@inner _ E y)
  point : iso.toEquiv (rootOf D x) = rootOf E y

def RootIso.symm {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) : RootIso E D y x where
  iso := f.iso.symm
  point := by change f.iso.toEquiv.symm _ = _; rw [← f.point,Equiv.symm_apply_apply]

def IsoExtensional {V : Type u} (D : V → V → Prop) : Prop := ∀ x y, RootIso D D x y → x = y

abbrev Child {V : Type u} (D : V → V → Prop) (x : V) := {y // D x y}

/-- Distinct children are joined when they have a common successor. -/
def Share {V : Type u} {D : V → V → Prop} {x : V} (a b : Child D x) : Prop :=
  a ≠ b ∧ ∃ z, D a.val z ∧ D b.val z

def childBelow {V} {D : V → V → Prop} {x : V} (a : Child D x) : Below D x := ⟨a.val,.single a.property⟩

def RootIso.mapChild {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (a : Child D x) : Child E y :=
  ⟨(f.iso.toEquiv (childBelow a)).val, by
    have h := (f.iso.edges (rootOf D x) (childBelow a)).mpr a.property
    rw [f.point] at h
    exact h⟩

private theorem child_below_image {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (a : Child D x) : childBelow (f.mapChild a) = f.iso.toEquiv (childBelow a) :=
  Subtype.ext rfl

@[simp] theorem RootIso.backChild {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (a : Child D x) : f.symm.mapChild (f.mapChild a) = a := by
  apply Subtype.ext
  change (f.iso.toEquiv.symm (childBelow (f.mapChild a))).val = a.val
  rw [child_below_image,Equiv.symm_apply_apply]; rfl

@[simp] theorem RootIso.forthChild {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (b : Child E y) : f.mapChild (f.symm.mapChild b) = b := by
  apply Subtype.ext
  change (f.iso.toEquiv (childBelow (f.symm.mapChild b))).val = b.val
  rw [child_below_image]; change (f.iso.toEquiv (f.iso.toEquiv.symm _)).val = _
  rw [Equiv.apply_symm_apply]; rfl

theorem share_maps {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) {a b : Child D x} (h : Share a b) : Share (f.mapChild a) (f.mapChild b) := by
  obtain ⟨ne,z,az,bz⟩ := h
  let z' : Below D x := ⟨z,(childBelow a).property.tail az⟩
  refine ⟨fun e => ne (by simpa only [RootIso.backChild] using congrArg f.symm.mapChild e),
    (f.iso.toEquiv z').val, (f.iso.edges (childBelow a) z').mpr az, (f.iso.edges (childBelow b) z').mpr bz⟩

/-- Sharing a successor is intrinsic even when the ambient graphs have other
parents outside the two rooted descendant graphs. -/
def RootIso.onChildren {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) : Iso (@Share _ D x) (@Share _ E y) where
  toEquiv := ⟨f.mapChild,f.symm.mapChild,f.backChild,f.forthChild⟩
  edges a b := by
    change Share (f.mapChild a) (f.mapChild b) ↔ Share a b
    exact ⟨fun h => by simpa only [RootIso.backChild] using share_maps f.symm h, share_maps f⟩

end WeakFrucht
