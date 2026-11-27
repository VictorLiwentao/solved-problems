module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Union

/-!
# Finite spectra and minimality from internal amorphousness

The protected targets `ProjectiveSupports.finite_image` and
`ProjectiveSupports.powerStructureProperties` concern the actual power set of
supported subsets. They use finite point supports in a group of permutations.
-/

@[expose] public section

namespace ProjectiveTypes

open FirstOrder FirstOrder.Language Set

variable (L : Language) {ι κ M N : Type*} [L.Structure M] [L.Structure N]

/-- The full first-order type of a tuple over the empty set. -/
def tupleType (x : ι → M) : Set (L.Formula ι) := {φ | φ.Realize x}

/-- Types of the given arity actually realized in a structure. -/
def typesIn (M : Type*) [L.Structure M] (ι : Type*) : Set (Set (L.Formula ι)) :=
  Set.range (tupleType L : (ι → M) → Set (L.Formula ι))

end ProjectiveTypes

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes

/-- A tuple of `k` coded finite/cofinite sets over an arbitrary structure. -/
abbrev Codes (A : Type*) (k : ℕ) := Fin k → Bool × Finset A

/-- Replace each position in a finite mask by the element at that position in the tuple. -/
noncomputable def decode {A B : Type*} {k : ℕ} (v : A → B) (p : Codes A k) : Codes B k :=
  open Classical in fun j => ((p j).1, (p j).2.image v)

/-- A relation symbol on `n` entries specifies two finite/cofinite codes on these
positions. Repeated positions between coordinates and empty masks are allowed. -/
def graphLanguage (k : ℕ) : Language where
  Functions _ := Empty
  Relations n := Codes (Fin n) k × Codes (Fin n) k

/-- Use every such relation to record the graph of a single self-map. -/
@[instance_reducible] noncomputable def graphStructure {A : Type*} {k : ℕ} (f : Codes A k → Codes A k) :
    (graphLanguage k).Structure A where
  funMap := fun {_} e => nomatch e
  RelMap := fun {_} r v => f (decode v r.1) = decode v r.2

/-- Finitely many full first-order types at each finite arity. -/
def FiniteTypes (L : Language) (A : Type*) [L.Structure A] : Prop :=
  ∀ (ι : Type) [Finite ι], (typesIn L A ι).Finite

end ProjectiveTransfer

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ}

@[simp] theorem decode_comp {U V W : Type*} (f : U → V) (g : V → W) (p : Codes U k) :
    decode g (decode f p) = decode (g ∘ f) p := by
  classical
  funext j
  simp [decode, Finset.image_image, Function.comp_def]

end ProjectiveTransfer

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes

variable (L : Language) {M ι : Type*} [L.Structure M]

/-- Append one distinguished element to a parameter tuple. -/
def point (x : ι → M) (a : M) : ι ⊕ Unit → M := Sum.elim x fun _ => a

/-- A unary definable set, with its displayed finite parameter tuple. -/
def locus (x : ι → M) (φ : L.Formula (ι ⊕ Unit)) : Set M :=
  {a | φ.Realize (point x a)}

/-- Every unary set definable with finitely many parameters is finite or cofinite. -/
def Minimal (M : Type*) [L.Structure M] : Prop :=
  ∀ (ι : Type) [Finite ι] (x : ι → M) (φ : L.Formula (ι ⊕ Unit)),
    (locus L x φ).Finite ∨ (locus L x φ)ᶜ.Finite

end ProjectiveAlgebraic

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

@[expose] public section

namespace ProjectiveSupports

open FirstOrder FirstOrder.Language ProjectiveAlgebraic ProjectiveTransfer ProjectiveTypes Set Function

variable {A : Type*} (G : Subgroup (_root_.Equiv.Perm A)) {L : Language} [L.Structure A]

/-- Every permutation fixing these finitely many points induces a genuine
first-order automorphism of the displayed structure. -/
def SupportedStructure (L : Language) [L.Structure A] (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∃ e : A ≃[L] A, e.toEquiv = σ

/-- Amorphousness in the support interpretation implies both model-theoretic
properties used in the argument, without postulating a well-order of the
internal atom set or its internal powerset. -/
theorem structure_properties (am : Amorphous G) (E : Finset A) (h : SupportedStructure G L E) :
    FiniteTypes L A ∧ Minimal L A := by
  classical
  refine ⟨?_,?_⟩
  · intro ι _
    apply finite_image G am _ E
    intro σ hg fix v
    obtain ⟨e,rfl⟩ := h _ hg fix
    ext φ
    exact StrongHomClass.realize_formula e φ
  · intro ι _ v φ
    let := Fintype.ofFinite ι
    apply am.2
    refine ⟨E ∪ Finset.univ.image v,?_⟩
    intro σ hg fix a
    obtain ⟨e,rfl⟩ := h _ hg (fun t ht => fix t (Finset.mem_union_left _ ht))
    have cut : e ∘ point v a = point v (e a) := by
      funext j
      rcases j with j|j
      · exact fix _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      · rfl
    change φ.Realize (point v (e a)) ↔ φ.Realize (point v a)
    rw [← cut]
    exact StrongHomClass.realize_formula e φ

/-- An internal self-map on codes commutes with permutations fixing its support. -/
def SupportedCodeMap {k : ℕ} (f : Codes A k → Codes A k) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ x, f (decode σ x) = decode σ (f x)

private theorem decode_injective {k : ℕ} (σ : _root_.Equiv.Perm A) : Injective (decode (k := k) σ) := by
  have inv (x : Codes A k) : decode σ.symm (decode σ x) = x := by
    rw [decode_comp]
    funext j
    simp [decode,Function.comp_def]
  exact Function.LeftInverse.injective inv

/-- The graph language recording every finite mask of the map has the very
same finite support as the map. -/
theorem graph_supported {k : ℕ} (f : Codes A k → Codes A k) (E : Finset A) (h : SupportedCodeMap G f E) :
    letI := graphStructure f
    SupportedStructure G (graphLanguage k) E := by
  let := graphStructure f
  intro σ hg fix
  refine ⟨{toEquiv := σ
           map_fun' := fun r => nomatch r
           map_rel' := ?_},rfl⟩
  intro n r v
  change f (decode (σ ∘ v) r.1) = decode (σ ∘ v) r.2 ↔ f (decode v r.1) = decode v r.2
  rw [← decode_comp v σ,← decode_comp v σ,h _ hg fix]
  exact (decode_injective σ).eq_iff

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

private theorem natural {k : ℕ} (σ : Equiv.Perm A) (x : Codes A k) (j : Fin k) :
    interpret (decode σ x j) = σ '' interpret (x j) := by
  classical
  obtain ⟨b,s,eq⟩ : ∃ b s, x j = (b,s) := ⟨_,_,rfl⟩
  cases b
  · simp [decode,eq,interpret,Finset.coe_image]
  · simp [decode,eq,interpret,Finset.coe_image,Set.image_compl_eq σ.bijective]

/-- Transfer a supported map on the actual internal power set to a supported
map on finite/cofinite codes. -/
theorem supports_conjugate (am : Amorphous G) {k : ℕ} (F : (Fin k → Power G) → (Fin k → Power G))
    (E : Finset A) (supp : SupportedPowerMap G F E) :
    let e := powersEquiv G am k
    SupportedCodeMap G (fun x => e.symm (F (e x))) E := by
  let e := powersEquiv G am k
  change SupportedCodeMap G (fun x => e.symm (F (e x))) E
  intro σ hg fix x
  have perm (u : Codes A k) (j : Fin k) : (e (decode σ u) j).val = σ '' (e u j).val := natural σ u j
  have rel := supp σ hg fix (e x) (e (decode σ x)) (perm x)
  apply e.injective
  rw [e.apply_symm_apply]
  funext j
  apply Subtype.ext
  rw [perm,e.apply_symm_apply]
  exact rel j

end ProjectiveSupports

public section

namespace ProjectiveSupports

open ProjectiveTransfer ProjectiveAlgebraic

/-- A supported self-map on the actual internal power set of amorphous atoms
has a coded first-order graph with finite spectra in every finite arity and
finite/cofinite unary definable sets over all finite parameter tuples. -/
theorem powerStructureProperties {A : Type*} (G : Subgroup (Equiv.Perm A)) (am : Amorphous G) {k : ℕ}
    (F : (Fin k → Power G) → (Fin k → Power G)) (E : Finset A) (h : SupportedPowerMap G F E) :
    let e := powersEquiv G am k
    letI := graphStructure (fun x => e.symm (F (e x)))
    FiniteTypes (graphLanguage k) A ∧ Minimal (graphLanguage k) A := by
  let e := powersEquiv G am k
  let f (x : Codes A k) := e.symm (F (e x))
  let := graphStructure f
  exact structure_properties G am E (graph_supported G f E (supports_conjugate G am F E h))

end ProjectiveSupports
