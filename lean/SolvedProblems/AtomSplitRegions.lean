module

public import SolvedProblems.AtomSplitModel
public import Mathlib.Basic.Denumerable
import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

namespace AtomSplit
open Set Equiv

/-- Permutations extended by the identity outside a region of atoms. -/
def Inside (B : Set ℕ) : Subgroup (Perm ℕ) where
  carrier := {p | ∀ x ∉ B, p x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' {p q} hp hq x hx := by change p (q x) = x; rw [hq x hx, hp x hx]
  inv_mem' {p} hp x hx := by change p.symm x = x; rw [Equiv.symm_apply_eq]; exact (hp _ hx).symm

theorem inside_mono {B D : Set ℕ} (h : D ⊆ B) : Inside D ≤ Inside B :=
  fun _ hp x hx => hp x (fun hx' => hx (h hx'))

theorem inside_preserves {B : Set ℕ} {g : Perm ℕ} (h : g ∈ Inside B) (x : ℕ) :
    g x ∈ B ↔ x ∈ B := by
  constructor
  · intro hx
    by_contra bad
    exact bad (h x bad ▸ hx)
  · intro hx
    by_contra bad
    have eq : g x = x := g.injective (h (g x) bad)
    exact bad (eq.symm ▸ hx)

theorem split_region {α : Type*} {S : Set α} (hS : S.Infinite) :
    ∃ U : Set α, U ⊆ S ∧ U.Infinite ∧ (S \ U).Infinite := by
  let f := Set.Infinite.natEmbedding S hS
  let even (i : ℕ) : α := (f (2*i)).val
  let odd (i : ℕ) : α := (f (2*i+1)).val
  have e_inj : Function.Injective even := fun i j h => by
    have eq := f.injective (Subtype.ext h); change 2*i=2*j at eq; omega
  have o_inj : Function.Injective odd := fun i j h => by
    have eq := f.injective (Subtype.ext h); change 2*i+1=2*j+1 at eq; omega
  refine ⟨range even, ?_, infinite_range_of_injective e_inj, (infinite_range_of_injective o_inj).mono ?_⟩
  · rintro _ ⟨i,rfl⟩; exact (f _).property
  · rintro _ ⟨i,rfl⟩
    refine ⟨(f _).property, ?_⟩
    rintro ⟨j,e⟩
    have eq := f.injective (Subtype.ext e); change 2*j=2*i+1 at eq; omega

/-- Restrict to an invariant cut and fix its complement pointwise. -/
noncomputable def cutPerm (p : Perm ℕ) (S : Set ℕ) (h : ∀ x, p x ∈ S ↔ x ∈ S) : Perm ℕ := by
  classical
  exact (p.subtypePerm h).extendDomain (Equiv.refl S)

theorem cutPerm_of_mem (p : Perm ℕ) (S : Set ℕ) (h) {x : ℕ} (hx : x ∈ S) :
    cutPerm p S h x = p x := by
  classical
  exact Perm.extendDomain_apply_image (p.subtypePerm h) (Equiv.refl S) ⟨x,hx⟩

theorem cutPerm_outside (p : Perm ℕ) (S : Set ℕ) (h) : cutPerm p S h ∈ Inside S := by
  classical
  exact fun x hx => Perm.extendDomain_apply_not_subtype _ _ hx

theorem cutPerm_same {p : Perm ℕ} {S B : Set ℕ} {h} (hp : p ∈ Inside B) :
    cutPerm p S h ∈ Inside B := by
  intro x hx
  by_cases e : x ∈ S
  · rw [cutPerm_of_mem p S h e,hp x hx]
  · exact cutPerm_outside _ _ _ x e

theorem cutPerm_factor {p : Perm ℕ} {S : Set ℕ} (h : ∀ x, p x ∈ S ↔ x ∈ S) :
    cutPerm p S h * cutPerm p Sᶜ (fun x => not_congr (h x)) = p := by
  apply Equiv.ext; intro x
  rw [Perm.mul_apply]
  by_cases hx : x ∈ S
  · rw [cutPerm_outside p Sᶜ _ x (show x ∉ Sᶜ from fun e => e hx), cutPerm_of_mem _ _ _ hx]
  · rw [cutPerm_of_mem _ _ _ (show x ∈ Sᶜ from hx), cutPerm_outside _ _ _ _ (mt (h x).mp hx)]

theorem infinite_lift {C B : Set ℕ} (hC : C.Infinite) (h : C ⊆ B) :
    Infinite {x : B // x.val ∈ C} := by
  let := hC.to_subtype
  exact Infinite.of_injective (fun x : C => (⟨⟨x.val,h x.property⟩,x.property⟩ : {x : B // x.val ∈ C}))
    (fun x y he => Subtype.ext (congrArg (fun p => p.val.val) he))

/-- On a countable block, any two infinite, co-infinite regions are conjugate. -/
theorem move_region {B C D : Set ℕ} (hc : C ⊆ B) (hd : D ⊆ B)
    (infC : C.Infinite) (infD : D.Infinite) (restC : (B \ C).Infinite) (restD : (B \ D).Infinite) :
    ∃ p : Inside B, ∀ x, p.val x ∈ D ↔ x ∈ C := by
  classical
  let := infinite_lift infC hc
  let := infinite_lift infD hd
  have complement (T : Set ℕ) (ht : (B \ T).Infinite) : Infinite {x : B // x.val ∉ T} := by
    let := ht.to_subtype
    exact Infinite.of_injective (fun x : ↑(B \ T) => (⟨⟨x.val,x.property.1⟩,x.property.2⟩ : {x : B // x.val ∉ T}))
      (fun x y he => Subtype.ext (congrArg (fun p => p.val.val) he))
  let := complement C restC
  let := complement D restD
  let e : {x : B // x.val ∈ C} ≃ {x : B // x.val ∈ D} := Classical.choice inferInstance
  let f : {x : B // x.val ∉ C} ≃ {x : B // x.val ∉ D} := Classical.choice inferInstance
  let g : Perm B := Equiv.subtypeCongr e f
  let p := g.extendDomain (Equiv.refl B)
  have hp : p ∈ Inside B := fun x hx => Perm.extendDomain_apply_not_subtype _ _ hx
  refine ⟨⟨p,hp⟩, fun x => ?_⟩
  by_cases hx : x ∈ B
  · let a : B := ⟨x,hx⟩
    have atx : p x = (g a).val := Perm.extendDomain_apply_image _ (Equiv.refl B) a
    rw [atx]
    by_cases h : a.val ∈ C
    · have eqa : g a = (e ⟨a,h⟩).val := by simp [g, Equiv.subtypeCongr,h]
      rw [eqa]; exact iff_of_true (e ⟨a,h⟩).property h
    · have eqa : g a = (f ⟨a,h⟩).val := by simp [g, Equiv.subtypeCongr,h]
      rw [eqa]; exact iff_of_false (f ⟨a,h⟩).property h
  · change p x ∈ D ↔ _
    rw [hp _ hx]; exact iff_of_false (fun h => hx (hd h)) (fun h => hx (hc h))

end AtomSplit
