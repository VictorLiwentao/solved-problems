module

public import SolvedProblems.ProjectiveGeometry
public import SolvedProblems.ProjectiveAvoidance
public import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Image

@[expose] public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} {cl : Set A → Set A} {G : Subgroup (Equiv.Perm A)} {D : Finset A}

theorem preserves_id : Preserves cl D (Equiv.refl _) := fun _ _ => Iff.rfl

theorem preserves_trans {p q : D ≃ D} (hp : Preserves cl D p) (hq : Preserves cl D q) :
    Preserves cl D (p.trans q) := by
  intro V a
  have h := hq (p '' V) (p a)
  simp only [Set.image_image] at h
  exact (hp V a).trans h

theorem preserves_symm {p : D ≃ D} (h : Preserves cl D p) : Preserves cl D p.symm := by
  intro V a
  have back := h (p.symm '' V) (p.symm a)
  simpa [Set.image_image] using back.symm

/-- The finite symmetry group that appears in local homogeneity. -/
def flatGroup (cl : Set A → Set A) (C D : Finset A) : Subgroup (Equiv.Perm D) where
  carrier := {p | (∀ a : D, a.val ∈ C → p a = a) ∧ Preserves cl D p}
  one_mem' := ⟨fun _ _ => rfl,preserves_id⟩
  mul_mem' := by
    intro p q hp hq
    refine ⟨fun a ha => ?_,preserves_trans hq.2 hp.2⟩
    change p (q a) = a
    rw [hq.1 a ha,hp.1 a ha]
  inv_mem' := by
    intro p hp
    refine ⟨fun a ha => ?_,preserves_symm hp.2⟩
    exact p.symm_apply_eq.mpr (hp.1 a ha).symm

/-- Points of the larger flat outside the smaller flat. -/
abbrev Outside (C D : Finset A) := {a : D // a.val ∉ C}

/-- Avoid a prescribed finite set with all the given points simultaneously,
using a closure-preserving permutation of a sufficiently large finite flat. -/
theorem displace (geom : Geometry G cl) (C D : Finset A) (inc : C ⊆ D)
    (cc : cl (C : Set A) = C) (dc : cl (D : Set A) = D) (X S : Finset A)
    (outside : ∀ x ∈ X, x ∉ C)
    (large : X.card * S.card < Nat.card (Outside C D)) :
    ∃ p : D ≃ D, (∀ a : D, a.val ∈ C → p a = a) ∧ Preserves cl D p ∧
      ∀ a : D, a.val ∈ X → (p a).val ∉ S := by
  classical
  let H := flatGroup cl C D
  let R := Outside C D
  let m (g : H) (a : R) : R := ⟨g.val a.val,by
    intro h
    have eq := g.val.injective (g.property.1 (g.val a.val) h)
    exact a.property (eq ▸ h)⟩
  let : MulAction H R := {
    smul := m
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  let : MulAction.IsPretransitive H R := ⟨fun a b => by
    obtain ⟨g,eq,fix,pres,_⟩ := geom.locally_homogeneous C D inc cc dc a.val b.val a.property b.property
    exact ⟨⟨g,fix,pres⟩,Subtype.ext eq⟩⟩
  let Xr := Finset.univ.filter fun a : R => a.val.val ∈ X
  let Sr := Finset.univ.filter fun a : R => a.val.val ∈ S
  have card (T : Finset A) : (Finset.univ.filter fun a : R => a.val.val ∈ T).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun a : R => a.val.val)
    · intro a h
      exact (Finset.mem_filter.mp h).2
    · exact (Subtype.val_injective.comp Subtype.val_injective).injOn
  have bound : Xr.card * Sr.card < Fintype.card R :=
    (Nat.mul_le_mul (card X) (card S)).trans_lt (by simpa [R,Nat.card_eq_fintype_card] using large)
  let := Fintype.ofFinite H
  obtain ⟨g,avoid⟩ := translate_avoids H R Xr Sr bound
  refine ⟨g.val,g.property.1,g.property.2,?_⟩
  intro a h ha
  let r : R := ⟨a,outside _ h⟩
  exact avoid r (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)

end ProjectiveSupports
