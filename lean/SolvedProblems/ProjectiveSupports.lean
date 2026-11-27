module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- Fixing each point of a finite support. -/
def Fixes (σ : Equiv.Perm A) (E : Finset A) := ∀ a ∈ E, σ a = a

/-- Subsets in the finite point-support interpretation are those fixed by a
pointwise stabilizer of some finite set. -/
def Supported (S : Set A) : Prop :=
  ∃ E : Finset A, ∀ σ ∈ G, Fixes σ E → ∀ a, σ a ∈ S ↔ a ∈ S

/-- Amorphousness for the internal power set of a permutation interpretation. -/
def Amorphous : Prop := Infinite A ∧ ∀ S : Set A, Supported G S → S.Finite ∨ Sᶜ.Finite

/-- A map into a type with trivial action is constant under the stabilizer of
its finite support. -/
def Invariant {ι B : Type*} (f : (ι → A) → B) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ v, f (σ ∘ v) = f v

/-- A supported map from the atoms into any type with trivial action has
finite image. An infinite image can be split externally into two infinite
pieces whose inverse images have the same finite support. -/
theorem finite_image_one (am : Amorphous G) {B : Type*} (f : A → B) (E : Finset A)
    (hf : ∀ σ ∈ G, Fixes σ E → ∀ a, f (σ a) = f a) : (range f).Finite := by
  classical
  by_contra large
  let e := Set.Infinite.natEmbedding (range f) large
  let t (j : ℕ) := (e j).val
  have tinj : Injective t := Subtype.val_injective.comp e.injective
  choose b hb using fun j : ℕ => (e j).property
  let S := range (fun j : ℕ => t (2*j))
  have supp : Supported G (f ⁻¹' S) := ⟨E,fun σ hm fix a => by simp [hf σ hm fix a]⟩
  have binj : Injective b := fun i j h => tinj ((hb i).symm.trans ((congrArg f h).trans (hb j)))
  rcases am.2 _ supp with even | odd
  · apply (Set.infinite_range_of_injective (f := fun j : ℕ => b (2*j)) (binj.comp (by intro i j h; dsimp at h; omega)))
    apply even.subset
    rintro _ ⟨j,rfl⟩
    exact ⟨j,(hb _).symm⟩
  · apply (Set.infinite_range_of_injective (f := fun j : ℕ => b (2*j+1)) (binj.comp (by intro i j h; dsimp at h; omega)))
    apply odd.subset
    rintro _ ⟨j,rfl⟩ ⟨i,h⟩
    have bad := tinj (h.trans (hb (2*j+1)))
    omega

/-- The same finite-image conclusion for every finite Cartesian power. The
set of row images is itself an invariant function of the remaining entries. -/
theorem finite_image_tuple (am : Amorphous G) {B : Type*} (n : ℕ) (f : (Fin n → A) → B)
    (E : Finset A) (hf : Invariant G f E) : (range f).Finite := by
  classical
  induction n generalizing B with
  | zero => exact finite_range f
  | succ n ih =>
    let row (v : Fin n → A) := range (fun a : A => f (Fin.snoc v a))
    have comp (σ : Equiv.Perm A) (v : Fin n → A) (a : A) : σ ∘ Fin.snoc v a = Fin.snoc (σ ∘ v) (σ a) := by
      funext i; refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp
    have stable : Invariant G row E := by
      intro σ hg fix v
      ext b
      constructor
      · rintro ⟨a,rfl⟩
        refine ⟨σ.symm a,?_⟩
        have eq := hf σ hg fix (Fin.snoc v (σ.symm a))
        simpa [comp] using eq.symm
      · rintro ⟨a,rfl⟩
        exact ⟨σ a,by simpa only [comp] using hf σ hg fix (Fin.snoc v a)⟩
    have rows := ih row stable
    have small (v : Fin n → A) : (row v).Finite := by
      apply finite_image_one G am _ (E ∪ Finset.univ.image v)
      intro σ hg fix a
      have before : σ ∘ v = v := funext fun i => fix _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      have eq := hf σ hg (fun b hb => fix _ (Finset.mem_union_left _ hb)) (Fin.snoc v a)
      rwa [comp,before] at eq
    apply (rows.sUnion (by rintro _ ⟨v,rfl⟩; exact small v)).subset
    rintro _ ⟨v,rfl⟩
    exact ⟨row (v ∘ Fin.castSucc),⟨_,rfl⟩,v (Fin.last n),congrArg f (Fin.snoc_init_self v)⟩

/-- Finite index types can name tuple coordinates in any order. -/
theorem finite_image (am : Amorphous G) {ι : Type} [Finite ι] {B : Type*} (f : (ι → A) → B)
    (E : Finset A) (hf : Invariant G f E) : (range f).Finite := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let h (v : Fin (Fintype.card ι) → A) := f (v ∘ e)
  apply (finite_image_tuple G am _ h E (fun σ hg fix v => hf σ hg fix (v ∘ e))).subset
  rintro _ ⟨v,rfl⟩
  refine ⟨v ∘ e.symm,?_⟩
  simp [h,Function.comp_assoc]

end ProjectiveSupports
