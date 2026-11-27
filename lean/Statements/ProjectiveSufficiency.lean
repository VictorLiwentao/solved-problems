module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Logic.Equiv.Sum

/-!
# A surjection from projective type

`ProjectiveSupports.differenceSurjection` maps finite subsets to the difference
between their flat and themselves. `ProjectiveSupports.allPositivePowers`
transfers it to every positive power of the actual internal powerset.
-/

@[expose] public section

namespace ProjectiveTransfer



/-- A tuple of `k` coded finite/cofinite sets over an arbitrary structure. -/
abbrev Codes (A : Type*) (k : ℕ) := Fin k → Bool × Finset A

/-- Replace each position in a finite mask by the element at that position in the tuple. -/
noncomputable def decode {A B : Type*} {k : ℕ} (v : A → B) (p : Codes A k) : Codes B k :=
  open Classical in fun j => ((p j).1, (p j).2.image v)

end ProjectiveTransfer

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

end ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

open ProjectiveTransfer

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- An internal self-map on codes commutes with permutations fixing its support. -/
def SupportedCodeMap {k : ℕ} (f : Codes A k → Codes A k) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ x, f (decode σ x) = decode σ (f x)

end ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

open ProjectiveTransfer Set Function

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- The interpreted power set of the atoms. -/
abbrev Power := {S : Set A // Supported G S}

/-- Decode one flag and finite set as an actual subset. `true` denotes the
complement of the finite set. -/
def interpret : Bool × Finset A → Set A
  | (false,s) => s
  | (true,s) => (s : Set A)ᶜ

theorem fixed_mem (σ : Equiv.Perm A) (s : Finset A) (fix : Fixes σ s) (a : A) : σ a ∈ s ↔ a ∈ s := by
  constructor
  · intro h
    have eq := σ.injective (fix _ h)
    rwa [eq] at h
  · intro h
    rwa [fix _ h]

/-- Every finite or cofinite set has finite support. -/
theorem interpret_supported (x : Bool × Finset A) : Supported G (interpret x) := by
  rcases x with ⟨b,s⟩
  refine ⟨s,fun σ _ fix a => ?_⟩
  cases b
  · exact fixed_mem σ s fix a
  · exact not_congr (fixed_mem σ s fix a)

theorem interpret_inj [Infinite A] : Injective (interpret (A := A)) := by
  rintro ⟨b,s⟩ ⟨c,t⟩ eq
  have impossible (u v : Finset A) (h : (u : Set A) = (v : Set A)ᶜ) : False :=
    (v.finite_toSet.infinite_compl (h ▸ u.finite_toSet))
  cases b <;> cases c
  · exact congrArg (Prod.mk false) (Finset.coe_injective eq)
  · exact (impossible s t eq).elim
  · exact (impossible t s eq.symm).elim
  · exact congrArg (Prod.mk true) (Finset.coe_injective (compl_injective eq))

theorem interpret_surj (am : Amorphous G) (S : Power G) : ∃ x : Bool × Finset A, interpret x = S.val := by
  rcases am.2 S.val S.property with finite | cofin
  · exact ⟨(false,finite.toFinset),finite.coe_toFinset⟩
  · exact ⟨(true,cofin.toFinset),by simp [interpret,cofin.coe_toFinset]⟩

/-- Under internal amorphousness the code is unique. This equivalence concerns
the internal power set and commutes with permutations of the atoms. -/
noncomputable def powerEquiv (am : Amorphous G) : (Bool × Finset A) ≃ Power G := by
  let := am.1
  apply Equiv.ofBijective (fun x => ⟨interpret x,interpret_supported G x⟩)
  refine ⟨fun _ _ h => interpret_inj (congrArg Subtype.val h),?_⟩
  intro S
  obtain ⟨x,h⟩ := interpret_surj G am S
  exact ⟨x,Subtype.ext h⟩

/-- The componentwise version for finite powers. -/
noncomputable def powersEquiv (am : Amorphous G) (k : ℕ) : Codes A k ≃ (Fin k → Power G) :=
  Equiv.piCongrRight fun _ => powerEquiv G am

/-- The entire map graph is invariant when a finite support is fixed.
The image formulation uses actual subsets on both sides. -/
def SupportedPowerMap {k : ℕ} (F : (Fin k → Power G) → (Fin k → Power G)) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ x y, (∀ j, (y j).val = σ '' (x j).val) →
    ∀ j, (F y j).val = σ '' (F x j).val

end ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- The closure operator on all parameter sets commutes with every permutation
fixing one support. It therefore restricts to an internal closure operator. -/
def SupportedClosure (cl : Set A → Set A) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ S, cl (σ '' S) = σ '' cl S

/-- Preservation of the closure of arbitrary subsets of a finite closed set. -/
def Preserves (cl : Set A → Set A) (D : Finset A) (p : D ≃ D) : Prop :=
  ∀ (V : Set D) (a : D), a.val ∈ cl (Subtype.val '' V) ↔
    (p a).val ∈ cl ((fun d : D => (p d).val) '' V)

/-- The pregeometry, nondegeneracy, and the two local homogeneity conditions
in Truss's projective-type definition. Finitary closure is specified on all
subsets, and its finite support makes its restriction an internal witness. -/
structure Geometry (cl : Set A → Set A) : Prop where
  support : ∃ E, SupportedClosure G cl E
  extensive : ∀ S, S ⊆ cl S
  monotone : ∀ S T, S ⊆ T → cl S ⊆ cl T
  idempotent : ∀ S, cl (cl S) = cl S
  finite_character : ∀ S a, a ∈ cl S ↔ ∃ D : Finset A, (D : Set A) ⊆ S ∧ a ∈ cl (D : Set A)
  locally_finite : ∀ S : Set A, S.Finite → (cl S).Finite
  exchange : ∀ S a b, b ∈ cl (insert a S) → b ∉ cl S → a ∈ cl (insert b S)
  nondegenerate : ∃ D : Finset A, D.Nonempty ∧ cl (D : Set A) ≠ ⋃ x ∈ D, cl {x}
  locally_homogeneous : ∀ (S D : Finset A), S ⊆ D → cl (S : Set A) = S → cl (D : Set A) = D →
    ∀ (a b : D), a.val ∉ S → b.val ∉ S →
      ∃ p : D ≃ D, p a = b ∧ (∀ d : D, d.val ∈ S → p d = d) ∧ Preserves cl D p ∧
        ∀ (U : Finset A) (inc : D ⊆ U), cl (U : Set A) = U →
          ∃ q : U ≃ U, (∀ d : D, q ⟨d.val,inc d.property⟩ = ⟨(p d).val,inc (p d).property⟩) ∧ Preserves cl U q

/-- The closure of an internal set is internal. A support is the union of a
support of the operator with a support of the input set. -/
theorem closed_supported {cl : Set A → Set A} {E : Finset A} (supp : SupportedClosure G cl E)
    {S : Set A} (hs : Supported G S) : Supported G (cl S) := by
  classical
  obtain ⟨D,sd⟩ := hs
  refine ⟨E ∪ D,?_⟩
  intro σ hg fix a
  have move := sd σ hg (fun t h => fix _ (Finset.mem_union_right _ h))
  have eq : σ '' S = S := by
    ext z
    refine ⟨fun ⟨w,hw,h⟩ => h ▸ (move w).mpr hw,fun hz => ?_⟩
    exact ⟨σ.symm z,(move _).mp (by simpa using hz),σ.apply_symm_apply z⟩
  have ce := supp σ hg (fun t ht => fix _ (Finset.mem_union_left _ ht)) S
  rw [eq] at ce
  conv_lhs => rw [ce]
  exact σ.injective.mem_set_image

end ProjectiveSupports

public section

namespace ProjectiveSupports

open Function

/-- In a finite transitive action, some translate of `X` misses `S` whenever
`|X| |S|` is smaller than the underlying set. Count the equal-size fibres of
the evaluation map; a group consisting entirely of bad translates would
inject into the fibres indexed by pairs in `X × S`. -/
theorem translate_avoids (H R : Type*) [Group H] [MulAction H R] [MulAction.IsPretransitive H R]
    [Fintype H] [Fintype R] (X S : Finset R) (bound : X.card * S.card < Fintype.card R) :
    ∃ h : H, ∀ x ∈ X, h • x ∉ S := by
  classical
  have pos : 0 < Fintype.card R := (Nat.zero_le _).trans_lt bound
  let := Fintype.card_pos_iff.mp pos
  let base : R := Classical.choice (inferInstance : Nonempty R)
  let fiber (x y : R) := {h : H // h • x = y}
  let m := Fintype.card (fiber base base)
  have eqCard (x y z : R) : Fintype.card (fiber x y) = Fintype.card (fiber x z) := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H y z
    apply Fintype.card_congr
    exact {
      toFun := fun h => ⟨g * h.val,by rw [mul_smul,h.property,hg]⟩
      invFun := fun h => ⟨g⁻¹ * h.val,by rw [mul_smul,h.property,← hg,inv_smul_smul]⟩
      left_inv := fun h => Subtype.ext (inv_mul_cancel_left _ _)
      right_inv := fun h => Subtype.ext (mul_inv_cancel_left _ _) }
  have total (x : R) : Fintype.card H = Fintype.card R * Fintype.card (fiber x base) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv fun g : H => g • x), Fintype.card_sigma]
    change ∑ y : R, Fintype.card (fiber x y) = _
    simp [fun y => eqCard x y base]
  have fiberSize (x y : R) : Fintype.card (fiber x y) = m :=
    (eqCard x y base).trans (Nat.eq_of_mul_eq_mul_left pos ((total x).symm.trans (total base)))
  by_contra! bad
  choose hit hx meets using bad
  let hitPair (g : H) : X × S := (⟨hit g,hx g⟩,⟨g • hit g,meets g⟩)
  let cert (g : H) : Σ p : X × S, fiber p.1.val p.2.val := ⟨hitPair g,⟨g,rfl⟩⟩
  have inj : Injective cert := fun a b h => congrArg (fun z : Σ p : X × S, fiber p.1.val p.2.val => z.2.val) h
  have card := Fintype.card_le_of_injective cert inj
  rw [Fintype.card_sigma] at card
  have count : Fintype.card H ≤ (X.card * S.card) * m := by simpa [fiberSize] using card
  have nonzero : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨1,one_smul _ _⟩⟩
  exact (Nat.mul_lt_mul_of_pos_right bound nonzero).not_ge ((total base) ▸ count)

end ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} {G : Subgroup (Equiv.Perm A)} {cl : Set A → Set A}

/-- The finite closed flat generated by a finite set. -/
noncomputable def finiteFlat (geom : Geometry G cl) (S : Finset A) : Finset A :=
  (geom.locally_finite (S : Set A) S.finite_toSet).toFinset

@[simp] theorem coe_finiteFlat (geom : Geometry G cl) (S : Finset A) : (finiteFlat geom S : Set A) = cl (S : Set A) :=
  Set.Finite.coe_toFinset _

theorem finiteFlat_closed (geom : Geometry G cl) (S : Finset A) :
    cl (finiteFlat geom S : Set A) = finiteFlat geom S := by simp [geom.idempotent]

theorem intoFlat (geom : Geometry G cl) (S : Finset A) : S ⊆ finiteFlat geom S := by
  intro a ha
  exact (coe_finiteFlat geom S).superset (geom.extensive (S : Set A) ha)

/-- The points of a finite set as elements of an ambient finite flat. -/
noncomputable def inside (D X : Finset A) : Finset D :=
  open Classical in Finset.univ.filter fun a : D => a.val ∈ X

@[simp] theorem mem_inside (D X : Finset A) (a : D) : a ∈ inside D X ↔ a.val ∈ X := by
  classical
  simp [inside]

theorem coe_inside {D X : Finset A} (h : X ⊆ D) : Subtype.val '' (inside D X : Set D) = (X : Set A) := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (mem_inside _ _ _).mp hx
  · intro ha
    exact ⟨⟨a,h ha⟩,(mem_inside _ _ _).mpr ha,rfl⟩

/-- Apply a permutation of the ambient finite flat to the indicated subset. -/
noncomputable def moveSet {D : Finset A} (p : D ≃ D) (X : Finset A) : Finset A :=
  open Classical in (inside D X).image fun d => (p d).val

theorem moves_closure {D X : Finset A} (sub : X ⊆ D) {p : D ≃ D} (hp : Preserves cl D p) (a : D) :
    a.val ∈ cl (X : Set A) ↔ (p a).val ∈ cl (moveSet p X : Set A) := by
  classical
  have eq := hp (inside D X : Set D) a
  rwa [coe_inside sub,← Finset.coe_image] at eq

/-- The points of a finite spanning set are all outside closure of the
single distinguished point. This property is inherited under a symmetry of
a finite flat containing the entire configuration. -/
def SpansOff (cl : Set A → Set A) (z : A) (X : Finset A) : Prop :=
  z ∈ cl (X : Set A) ∧ ∀ x ∈ X, x ∉ cl {z}

theorem move_spanning_set {D X : Finset A} (xd : X ⊆ D) {p : D ≃ D} (hp : Preserves cl D p) {z : D}
    (h : SpansOff cl z.val X) : SpansOff cl (p z).val (moveSet p X) := by
  classical
  refine ⟨(moves_closure xd hp z).mp h.1,?_⟩
  intro y hy
  obtain ⟨x,mem,rfl⟩ := Finset.mem_image.mp hy
  have ht := hp ({z} : Set D) x
  simp only [Set.image_singleton] at ht
  exact fun hm => h.2 x.val ((mem_inside _ _ _).mp mem) (ht.mpr hm)

/-- Nondegeneracy provides one point spanned by a finite set of points all
outside its singleton closure. Exchange removes algebraic core points. -/
theorem exists_spanning_set (geom : Geometry G cl) : ∃ z X, z ∉ cl ∅ ∧ SpansOff cl z X := by
  classical
  obtain ⟨D,ne,neq⟩ := geom.nondegenerate
  have sub : (⋃ x ∈ D, cl {x}) ⊆ cl (D : Set A) := by
    intro a ha
    obtain ⟨x,hx,h⟩ := Set.mem_iUnion₂.mp ha
    exact geom.monotone _ _ (Set.singleton_subset_iff.mpr hx) h
  obtain ⟨z,hz,miss⟩ := Set.not_subset.mp (show ¬ cl (D : Set A) ⊆ ⋃ x ∈ D, cl {x} from fun h => neq (Set.Subset.antisymm h sub))
  have single (x) (hx : x ∈ D) : z ∉ cl {x} := fun h => miss (Set.mem_iUnion₂.mpr ⟨x,hx,h⟩)
  let X := D.filter fun x => x ∉ cl ∅
  have inside : (D : Set A) ⊆ cl (X : Set A) := by
    intro x hx
    by_cases h : x ∈ cl ∅
    · exact geom.monotone _ _ (Set.empty_subset _) h
    · exact geom.extensive _ (Finset.mem_filter.mpr ⟨hx,h⟩)
  obtain ⟨u,hu⟩ := ne
  refine ⟨z,X,fun h => single u hu (geom.monotone _ _ (Set.empty_subset _) h),?_,?_⟩
  · exact (geom.idempotent _).subset (geom.monotone _ _ inside hz)
  · intro x hx h
    obtain ⟨xd,fresh⟩ := Finset.mem_filter.mp hx
    apply single x xd
    simpa using geom.exchange ∅ z x (by simpa using h) fresh

end ProjectiveSupports

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

public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} {G : Subgroup (Equiv.Perm A)} {cl : Set A → Set A}

/-- Any generic point has a finite spanning configuration outside its own
singleton closure, by transitivity over the finite algebraic core. -/
theorem spans_each_generic (geom : Geometry G cl) {b : A} (fresh : b ∉ cl ∅) : ∃ X, SpansOff cl b X := by
  classical
  obtain ⟨z,X,zo,hX⟩ := exists_spanning_set geom
  let C := finiteFlat geom ∅
  let T := insert b (insert z X)
  let D := finiteFlat geom T
  have core : (C : Set A) = cl ∅ := by simp [C]
  have cd : C ⊆ D := by
    intro x hx
    apply (coe_finiteFlat geom T).superset
    exact geom.monotone _ _ (Set.empty_subset _) (core.subset hx)
  let a : D := ⟨z,intoFlat geom T (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
  let t : D := ⟨b,intoFlat geom T (Finset.mem_insert_self _ _)⟩
  have xd : X ⊆ D := fun _ h => intoFlat geom T (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  obtain ⟨p,eq,_,symm,_⟩ := geom.locally_homogeneous C D cd (finiteFlat_closed _ _) (finiteFlat_closed _ _)
    a t (fun h => zo (core.subset h)) (fun h => fresh (core.subset h))
  have tr := move_spanning_set xd symm (z := a) hX
  exact ⟨_,eq ▸ tr⟩

/-- A given point has a finite spanning set disjoint from any prescribed finite
set. All other members of the initial configuration lie in the same orbit of
a finite-flat stabilizer, so a sufficiently large finite flat allows a
translate avoiding every forbidden point. -/
theorem spans_point_away [Infinite A] (geom : Geometry G cl) (b : A) (S : Finset A) :
    ∃ W : Finset A, Disjoint W S ∧ b ∈ cl (W : Set A) := by
  classical
  by_cases root : b ∈ cl ∅
  · exact ⟨∅,Finset.disjoint_empty_left _,by simpa using root⟩
  obtain ⟨X,hX⟩ := spans_each_generic geom root
  let C := finiteFlat geom {b}
  have ce : (C : Set A) = cl {b} := by simp [C]
  obtain ⟨T,away,num⟩ := C.finite_toSet.infinite_compl.exists_subset_card_eq (X.card*S.card+1)
  let B := C ∪ X ∪ T
  let D := finiteFlat geom B
  have cd : C ⊆ D := fun _ h => intoFlat geom B (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have xd : X ⊆ D := fun _ h => intoFlat geom B (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have td : T ⊆ D := fun _ h => intoFlat geom B (Finset.mem_union_right _ h)
  let embed (t : T) : Outside C D := ⟨⟨t.val,td t.property⟩,away t.property⟩
  have bound : T.card ≤ Nat.card (Outside C D) := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective embed
      (fun a b h => Subtype.ext (congrArg (fun u : Outside C D => u.val.val) h))
  rw [num] at bound
  have enough : X.card*S.card < Nat.card (Outside C D) := bound
  obtain ⟨p,fix,pres,miss⟩ := displace geom C D cd (finiteFlat_closed _ _) (finiteFlat_closed _ _)
    X S (fun a h hc => hX.2 a h (ce.subset hc)) enough
  have bc : b ∈ C := intoFlat geom {b} (Finset.mem_singleton_self _)
  let a : D := ⟨b,cd bc⟩
  have spanning := moves_closure xd pres a |>.mp hX.1
  rw [fix a bc] at spanning
  refine ⟨moveSet p X,Finset.disjoint_left.mpr ?_,spanning⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact miss x ((mem_inside D X x).mp hx)

open Classical in
/-- Each finite set lies in a finite closed flat spanned by the complement of
that set inside the flat. -/
theorem flat_spanned_by_difference [Infinite A] (geom : Geometry G cl) (S : Finset A) :
    ∃ D : Finset A, S ⊆ D ∧ finiteFlat geom (D \ S) = D := by
  classical
  choose w apart span using fun a => spans_point_away geom a S
  let W := S.biUnion w
  let D := finiteFlat geom W
  have sub : S ⊆ D := by
    intro a ha
    apply (coe_finiteFlat geom W).superset
    apply geom.monotone _ _ _ (span a)
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨a,ha,hx⟩
  have wd : W ⊆ D \ S := by
    intro x hx
    obtain ⟨u,hu,xm⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_sdiff.mpr ⟨intoFlat geom W hx,Finset.disjoint_left.mp (apart u) xm⟩
  refine ⟨D,sub,Finset.coe_injective ?_⟩
  rw [coe_finiteFlat]
  exact Set.Subset.antisymm ((geom.monotone _ _ (by exact Finset.sdiff_subset : (↑(D \ S) : Set A) ⊆ D)).trans (finiteFlat_closed geom W).subset)
    ((coe_finiteFlat geom W).subset.trans (geom.monotone _ _ wd))

end ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

open Set Function

variable {A : Type*} {G : Subgroup (Equiv.Perm A)} {cl : Set A → Set A}

/-- Send a finite subset to the points in its generated flat that it omits. -/
noncomputable def flatDifference (geom : Geometry G cl) (S : Finset A) : Finset A :=
  open Classical in finiteFlat geom S \ S

/-- This specific map is supported and surjective but fails to be injective.
All closed finite flats map to the empty set. -/
theorem differenceSurjection [Infinite A] (geom : Geometry G cl) :
    (∃ E : Finset A, ∀ σ ∈ G, Fixes σ E → ∀ S : Finset A,
      flatDifference geom (S.map σ.toEmbedding) = (flatDifference geom S).map σ.toEmbedding) ∧
    Surjective (flatDifference geom) ∧ ¬ Injective (flatDifference geom) := by
  classical
  obtain ⟨E,supp⟩ := geom.support
  refine ⟨⟨E,?_⟩,?_,?_⟩
  · intro σ hm fix S
    apply Finset.coe_injective
    simp only [flatDifference,Finset.coe_sdiff,coe_finiteFlat,Finset.coe_map,Equiv.coe_toEmbedding]
    rw [supp σ hm fix,Set.image_sdiff σ.injective]
  · intro S
    obtain ⟨D,sub,flat⟩ := flat_spanned_by_difference geom S
    exact ⟨D \ S,by rw [flatDifference,flat,Finset.sdiff_sdiff_eq_self sub]⟩
  · intro hinj
    let C := finiteFlat geom ∅
    obtain ⟨a,fresh⟩ := C.finite_toSet.exists_notMem
    let D := finiteFlat geom {a}
    have empty (T : Finset A) : flatDifference geom (finiteFlat geom T) = ∅ := by
      have fixed : finiteFlat geom (finiteFlat geom T) = finiteFlat geom T := Finset.coe_injective ((coe_finiteFlat geom (finiteFlat geom T)).trans (finiteFlat_closed geom T))
      simp [flatDifference,fixed]
    have eq : C = D := hinj ((empty ∅).trans (empty {a}).symm)
    apply fresh
    change a ∈ C
    rw [eq]
    exact intoFlat geom {a} (Finset.mem_singleton_self a)

end ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

open Function ProjectiveTransfer

variable {A : Type*} {G : Subgroup (Equiv.Perm A)}

/-- Internal dual Dedekind infinity of the finite power, expressed by the
existence of a supported surjective noninjective self-map. -/
def DuallyInfinitePower (G : Subgroup (Equiv.Perm A)) (k : ℕ) : Prop :=
  ∃ F : (Fin k → Power G) → (Fin k → Power G), (∃ E, SupportedPowerMap G F E) ∧ Surjective F ∧ ¬ Injective F

private theorem of_code (am : Amorphous G) {k : ℕ} (f : Codes A k → Codes A k) (E : Finset A)
    (support : SupportedCodeMap G f E) (onto : Surjective f) (collision : ¬ Injective f) : DuallyInfinitePower G k := by
  let e := powersEquiv G am k
  let F (x : Fin k → Power G) := e (f (e.symm x))
  refine ⟨F,⟨E,?_⟩,e.surjective.comp (onto.comp e.symm.surjective),?_⟩
  · intro σ hg fix x y eq j
    have perm (u : Codes A k) (i : Fin k) : (e (decode σ u) i).val = σ '' (e u i).val := by
      classical
      change interpret (decode σ u i) = σ '' interpret (u i)
      obtain ⟨b,s,cut⟩ : ∃ b s, u i = (b,s) := ⟨_,_,rfl⟩
      cases b <;> simp [decode,cut,interpret,Finset.coe_image,Set.image_compl_eq σ.bijective]
    have move : e.symm y = decode σ (e.symm x) := by
      apply e.injective
      rw [e.apply_symm_apply]
      funext i
      apply Subtype.ext
      rw [perm,e.apply_symm_apply,eq]
    change (e (f (e.symm y)) j).val = σ '' (e (f (e.symm x)) j).val
    rw [move,support _ hg fix,perm]
  · intro inj
    apply collision
    intro a b eq
    apply e.injective
    apply inj
    simp [F,eq]

/-- A single supported map on finite subsets acts on the finite part of the
chosen coordinate and keeps its flag and the remaining coordinates. -/
private def updatePart {k : ℕ} (j : Fin k) (g : Finset A → Finset A) (x : Codes A k) : Codes A k :=
  Function.update x j ((x j).1,g (x j).2)

/-- Projective type implies dual Dedekind infinity of every positive finite
power of the internal powerset. The explicit map replaces one finite part
`S` by `cl(S) \\ S`, preserving that coordinate's finite/cofinite flag. -/
theorem allPositivePowers (am : Amorphous G) {cl : Set A → Set A} (geom : Geometry G cl)
    (k : ℕ) (pos : 0 < k) : DuallyInfinitePower G k := by
  classical
  let := am.1
  let j : Fin k := ⟨0,pos⟩
  let g := flatDifference geom
  obtain ⟨⟨E,hs⟩,onto,collision⟩ := differenceSurjection geom
  apply of_code am (updatePart j g) E
  · intro σ hm fix x
    funext i
    by_cases eq : i = j
    · subst i
      apply Prod.ext
      · simp [updatePart,decode]
      · simpa [updatePart,decode,g,Finset.map_eq_image] using hs σ hm fix (x j).2
    · simp [updatePart,decode,eq]
  · intro y
    obtain ⟨s,hs⟩ := onto (y j).2
    refine ⟨Function.update y j ((y j).1,s),?_⟩
    funext i
    by_cases eq : i = j
    · subst i
      simp [updatePart,g,hs]
    · simp [updatePart,eq]
  · intro inj
    apply collision
    intro s t h
    let x (u : Finset A) : Codes A k := Function.update (fun _ => (false,∅)) j (false,u)
    have eq : updatePart j g (x s) = updatePart j g (x t) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [updatePart,x,g,h]
      · simp [updatePart,x,hi]
    have read := congrArg (fun v : Codes A k => (v j).2) (inj eq)
    simpa [x] using read

end ProjectiveSupports
