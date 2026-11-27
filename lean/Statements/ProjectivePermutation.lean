module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Function.Iterate
public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Range
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The projective-type equivalence in the finite point-support interpretation

`ProjectiveSupports.projectivePowers` compares the actual supported power set,
its positive finite powers, and the full set of projective pregeometry conditions.
All lemmas needed for both directions have checked proof bodies in this file.
The small separate Challenges protect individual components of this argument.
-/

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

namespace ProjectiveTypes

open FirstOrder FirstOrder.Language Set

variable (L : Language) {ι κ M N : Type*} [L.Structure M] [L.Structure N]

/-- The full first-order type of a tuple over the empty set. -/
def tupleType (x : ι → M) : Set (L.Formula ι) := {φ | φ.Realize x}

/-- Types of the given arity actually realized in a structure. -/
def typesIn (M : Type*) [L.Structure M] (ι : Type*) : Set (Set (L.Formula ι)) :=
  Set.range (tupleType L : (ι → M) → Set (L.Formula ι))

private theorem distinguish (x : ι → M) (y : ι → N) (h : tupleType L x ≠ tupleType L y) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ¬φ.Realize y := by
  by_contra! no
  apply h
  ext φ
  change φ.Realize x ↔ φ.Realize y
  refine ⟨no φ, fun hy => ?_⟩
  by_contra hx
  exact (Formula.realize_not.mp (no φ.not (Formula.realize_not.mpr hx))) hy

/-- A single formula separates a tuple from any finite collection of other realized types. -/
private theorem separate (x : ι → M) (S : Set (Set (L.Formula ι))) (hs : S.Finite)
    (realized : S ⊆ typesIn L N ι) (avoids : tupleType L x ∉ S) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ∀ y : ι → N, tupleType L y ∈ S → ¬φ.Realize y := by
  induction S, hs using Set.Finite.induction_on with
  | empty => exact ⟨⊤, Formula.realize_top.mpr trivial, by simp⟩
  | @insert q S hq hs ih =>
    have nq : tupleType L x ≠ q := fun h => avoids (h ▸ Set.mem_insert q S)
    obtain ⟨y,hy⟩ := realized (Set.mem_insert q S)
    obtain ⟨φ,hφ,hφy⟩ := distinguish L x y (hy ▸ nq)
    obtain ⟨θ,hθ,hθy⟩ := ih ((Set.subset_insert q S).trans realized)
      (fun h => avoids (Set.mem_insert_of_mem q h))
    refine ⟨φ ⊓ θ, Formula.realize_inf.mpr ⟨hφ,hθ⟩, ?_⟩
    intro z hz h
    obtain ⟨hp,ht⟩ := Formula.realize_inf.mp h
    rcases Set.mem_insert_iff.mp hz with eq | hz
    · exact hφy ((show φ ∈ tupleType L y from (eq.trans hy.symm) ▸ hp))
    · exact hθy z hz ht

private theorem exists_transfer [Finite ι] (h : M ≅[L] N) (φ : L.Formula ι) :
    (∃ x : ι → M, φ.Realize x) ↔ (∃ y : ι → N, φ.Realize y) := by
  let ψ : L.Sentence := (φ.relabel (Sum.inr : ι → Empty ⊕ ι)).iExs ι
  have transfer := elementarilyEquivalent_iff.mp h ψ
  simpa only [ψ, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
    Sum.elim_comp_inr] using transfer

private theorem types_subset [Finite ι] (h : M ≅[L] N) (hN : (typesIn L N ι).Finite) :
    typesIn L M ι ⊆ typesIn L N ι := by
  rintro _ ⟨x,rfl⟩
  by_contra missing
  obtain ⟨φ,hx,hn⟩ := separate L x _ hN Set.Subset.rfl missing
  obtain ⟨y,hy⟩ := (exists_transfer L h φ).mp ⟨x,hx⟩
  exact hn y ⟨y,rfl⟩ hy

/-- Each finite-arity type is realized in both elementarily equivalent structures
when one of them realizes only finitely many types of that arity. -/
theorem realizedTypes_eq [Finite ι] (h : M ≅[L] N) (hM : (typesIn L M ι).Finite) :
    typesIn L M ι = typesIn L N ι := by
  have sub := types_subset L (M := N) (N := M) (ι := ι) (Eq.symm h) hM
  exact Set.Subset.antisymm (types_subset L h (hM.subset sub)) sub

/-- Tuples of a fixed type in the two models can be extended on the second
side to match arbitrarily many additional prescribed elements on the first.
The isolation formula is obtained from finitely many realized joint types. -/
theorem extendTuple [Finite κ] [Finite ι] (h : M ≅[L] N)
    (finite : (typesIn L M (ι ⊕ κ)).Finite) {x : ι → M} {y : ι → N}
    (same : tupleType L x = tupleType L y) (z : κ → M) :
    ∃ w : κ → N, tupleType L (Sum.elim x z) = tupleType L (Sum.elim y w) := by
  let p := tupleType L (Sum.elim x z)
  let S := typesIn L N (ι ⊕ κ) \ {p}
  have eq := realizedTypes_eq L h finite
  have hs : S.Finite := (eq ▸ finite : (typesIn L N (ι ⊕ κ)).Finite).subset Set.sdiff_subset
  have avoids : p ∉ S := fun h => h.2 rfl
  obtain ⟨φ,hp,other⟩ := separate L (Sum.elim x z) S hs Set.sdiff_subset avoids
  have hx : φ.iExs κ ∈ tupleType L x := Formula.realize_iExs.mpr ⟨z,hp⟩
  have hy : φ.iExs κ ∈ tupleType L y := same ▸ hx
  obtain ⟨w,hw⟩ := Formula.realize_iExs.mp hy
  refine ⟨w, ?_⟩
  by_contra diff
  exact other _ ⟨⟨_,rfl⟩, fun eq => diff eq.symm⟩ hw

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

/-- The relation on codes interpreted in the second model. The number of entries
and the two masks range freely; no bound on unknown output lengths is imposed. -/
def recorded {A : Type*} {k : ℕ} [(graphLanguage k).Structure A] (x y : Codes A k) : Prop :=
  ∃ (n : ℕ) (p q : Codes (Fin n) k) (v : Fin n → A),
    decode v p = x ∧ decode v q = y ∧ Structure.RelMap (L := graphLanguage k) (p,q) v

/-- Finitely many full first-order types at each finite arity. -/
def FiniteTypes (L : Language) (A : Type*) [L.Structure A] : Prop :=
  ∀ (ι : Type) [Finite ι], (typesIn L A ι).Finite

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

/-- The algebraic closure of a tuple consists of the elements of finite
unary sets defined over precisely those parameters. -/
def tupleClosure (x : ι → M) : Set M :=
  {a | ∃ φ : L.Formula (ι ⊕ Unit), a ∈ locus L x φ ∧ (locus L x φ).Finite}

/-- Every unary set definable with finitely many parameters is finite or cofinite. -/
def Minimal (M : Type*) [L.Structure M] : Prop :=
  ∀ (ι : Type) [Finite ι] (x : ι → M) (φ : L.Formula (ι ⊕ Unit)),
    (locus L x φ).Finite ∨ (locus L x φ)ᶜ.Finite

/-- Algebraic closure on arbitrary parameter sets has finite character by definition. -/
def acl (S : Set M) : Set M :=
  {a | ∃ (n : ℕ) (x : Fin n → M), Set.range x ⊆ S ∧ a ∈ tupleClosure L x}

end ProjectiveAlgebraic

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set

variable {L : Language} {M : Type*} [L.Structure M]

/-- In a finite spectrum of realized types, a single formula defines each complete type. -/
theorem isolate {ι : Type*} (fin : (typesIn L M ι).Finite) (x : ι → M) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ∀ y : ι → M, φ.Realize y ↔ tupleType L y = tupleType L x := by
  have distinguish {y : ι → M} (diff : tupleType L y ≠ tupleType L x) :
      ∃ φ : L.Formula ι, φ.Realize x ∧ ¬φ.Realize y := by
    by_contra! no
    apply diff
    ext φ
    change φ.Realize y ↔ φ.Realize x
    refine ⟨fun hy => ?_, no φ⟩
    by_contra hx
    exact (Formula.realize_not.mp (no φ.not (Formula.realize_not.mpr hx))) hy
  have aux (S : Set (Set (L.Formula ι))) (hs : S.Finite) (sub : S ⊆ typesIn L M ι) :
      ∃ φ : L.Formula ι, φ.Realize x ∧ ∀ y : ι → M, tupleType L y ∈ S →
        φ.Realize y → tupleType L y = tupleType L x := by
    induction S, hs using Set.Finite.induction_on with
    | empty => exact ⟨⊤,Formula.realize_top.mpr trivial,by simp⟩
    | @insert q S _ hs ih =>
      obtain ⟨ψ,hψ,indu⟩ := ih ((Set.subset_insert q S).trans sub)
      obtain ⟨y,hy⟩ := sub (Set.mem_insert q S)
      by_cases he : tupleType L y = tupleType L x
      · refine ⟨ψ,hψ,?_⟩
        intro z hz h
        rcases Set.mem_insert_iff.mp hz with eq | mem
        · exact (eq.trans hy.symm).trans he
        · exact indu z mem h
      · obtain ⟨θ,hθ,hθy⟩ := distinguish he
        refine ⟨ψ ⊓ θ, Formula.realize_inf.mpr ⟨hψ,hθ⟩, ?_⟩
        intro z hz h
        obtain ⟨hp,ht⟩ := Formula.realize_inf.mp h
        rcases Set.mem_insert_iff.mp hz with eq | mem
        · exact False.elim <| hθy ((show θ ∈ tupleType L y from (eq.trans hy.symm) ▸ ht))
        · exact indu z mem hp
  obtain ⟨φ,hφ,spec⟩ := aux _ fin Set.Subset.rfl
  exact ⟨φ,hφ, fun y => ⟨spec y ⟨y,rfl⟩,fun h => (show φ ∈ tupleType L y from h ▸ hφ)⟩⟩

variable {ι : Type} [Finite ι]

private def fiberType (x : ι → M) (p : Set (L.Formula (ι ⊕ Unit))) : Set M :=
  {a | tupleType L (point x a) = p}

/-- An element is algebraic over a finite tuple precisely when its complete
one-type over the tuple has only finitely many realizations. -/
theorem algebraic_iff_finite_type (fin : FiniteTypes L M) (x : ι → M) (a : M) :
    a ∈ tupleClosure L x ↔ {b | tupleType L (point x b) = tupleType L (point x a)}.Finite := by
  constructor
  · rintro ⟨φ,ha,small⟩
    exact small.subset fun b h => (show φ ∈ tupleType L (point x b) from h ▸ ha)
  · intro small
    obtain ⟨φ,ha,hφ⟩ := isolate (fin (ι ⊕ Unit)) (point x a)
    have eq : locus L x φ = {b | tupleType L (point x b) = tupleType L (point x a)} := by
      ext b; exact hφ (point x b)
    exact ⟨φ,ha,eq.symm ▸ small⟩

/-- Local finiteness of algebraic closure follows from finite finite-arity type spectra. -/
theorem finite_tupleClosure (fin : FiniteTypes L M) (x : ι → M) : (tupleClosure L x).Finite := by
  let S := {p ∈ typesIn L M (ι ⊕ Unit) | (fiberType x p).Finite}
  have hs : S.Finite := (fin (ι ⊕ Unit)).subset fun _ h => h.1
  apply (hs.biUnion (fun p hp => hp.2)).subset
  intro a ha
  have hf := (algebraic_iff_finite_type fin x a).mp ha
  exact Set.mem_iUnion₂.mpr ⟨_,⟨⟨_,rfl⟩,hf⟩,rfl⟩

/-- Nonalgebraic elements all realize the same complete unary type over any given finite tuple. -/
theorem generic_type (min : Minimal L M) {x : ι → M} {a b : M}
    (ha : a ∉ tupleClosure L x) (hb : b ∉ tupleClosure L x) :
    tupleType L (point x a) = tupleType L (point x b) := by
  have go {z w : M} (hz : z ∉ tupleClosure L x) (hw : w ∉ tupleClosure L x)
      (φ : L.Formula (ι ⊕ Unit)) (hφ : φ.Realize (point x z)) : φ.Realize (point x w) := by
    rcases min ι x φ with h | h
    · exact (hz ⟨φ,hφ,h⟩).elim
    · by_contra bad
      apply hw
      have setEq : locus L x φ.not = (locus L x φ)ᶜ := by
        ext v; exact Formula.realize_not
      exact ⟨φ.not,Formula.realize_not.mpr bad,setEq.symm ▸ h⟩
  exact Set.ext fun φ => ⟨go ha hb φ,go hb ha φ⟩

end ProjectiveAlgebraic

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ}

@[simp] theorem decode_comp {U V W : Type*} (f : U → V) (g : V → W) (p : Codes U k) :
    decode g (decode f p) = decode (g ∘ f) p := by
  classical
  funext j
  simp [decode, Finset.image_image, Function.comp_def]

/-- All finitely many finite parts fit on one finite tuple. -/
theorem present {A : Type*} (x : Codes A k) :
    ∃ (n : ℕ) (p : Codes (Fin n) k) (v : Fin n → A), decode v p = x := by
  classical
  let s := Finset.univ.biUnion fun j => (x j).2
  let u : Codes s k := fun j => ((x j).1, Finset.univ.filter fun a => a.val ∈ (x j).2)
  let e := s.equivFin
  refine ⟨s.card,decode e u, (fun i => (e.symm i).val), ?_⟩
  rw [decode_comp]
  funext j
  refine Prod.ext ?_ ?_
  · rfl
  apply Finset.ext
  intro a
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    simpa [e] using (Finset.mem_filter.mp hz).2
  · intro h
    have ha : a ∈ s := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _, h⟩
    exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,by simp⟩

variable {L : Language} {A B ι κ : Type*} [L.Structure A] [L.Structure B]

/-- Restriction/reordering retains equality of complete types. -/
theorem match_subtuple {a : ι → A} {b : ι → B}
    (m : tupleType L a = tupleType L b) (f : κ → ι) : tupleType L (a ∘ f) = tupleType L (b ∘ f) := by
  ext φ
  have h := Set.ext_iff.mp m (φ.relabel f)
  simpa only [tupleType,Set.mem_ofPred_eq,Formula.realize_relabel] using h

private theorem match_eq {a : ι → A} {b : ι → B} (m : tupleType L a = tupleType L b) (i j : ι) :
    a i = a j ↔ b i = b j := by
  have h := Set.ext_iff.mp m ((Term.var i).equal (Term.var j))
  simpa [tupleType] using h

private theorem image_eq_of_match {a : ι → A} {b : ι → B}
    (m : tupleType L a = tupleType L b) (p q : Finset ι) :
    letI := Classical.decEq A
    letI := Classical.decEq B
    p.image a = q.image a → p.image b = q.image b := by
  classical
  intro h
  apply Finset.Subset.antisymm
  · rintro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have mem : a i ∈ q.image a := h ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j,hj,(match_eq m j i).mp he⟩
  · rintro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have mem : a i ∈ p.image a := h.symm ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j,hj,(match_eq m j i).mp he⟩

private theorem match_codes_one {x : ι → A} {y : ι → B}
    (same : tupleType L x = tupleType L y) (p q : Codes ι k)
    (h : decode x p = decode x q) : decode y p = decode y q := by
  funext j
  have flag := congrArg (fun a : Bool × Finset A => a.1) (congrFun h j)
  exact Prod.ext flag (image_eq_of_match same _ _ (congrArg Prod.snd (congrFun h j)))

/-- Equality of two decoded tuples of finite parts depends only on equality of entries. -/
theorem match_codes {a : ι → A} {b : ι → B} (m : tupleType L a = tupleType L b)
    (p q : Codes ι k) : decode a p = decode a q ↔ decode b p = decode b q :=
  ⟨match_codes_one m p q,match_codes_one m.symm p q⟩

/-- Different masks may be given on the two different parts of a joint tuple. -/
theorem match_cross {a : ι → A} {b : ι → B} {u : κ → A} {v : κ → B}
    (m : tupleType L (Sum.elim a u) = tupleType L (Sum.elim b v))
    (p : Codes ι k) (q : Codes κ k) : decode a p = decode u q ↔ decode b p = decode v q := by
  have h := match_codes m (decode Sum.inl p) (decode Sum.inr q)
  simpa only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] using h

/-- Atomic graph predicates in matched tuples have identical truth values. -/
theorem match_relation {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]
    {n : ℕ} {a : Fin n → A} {b : Fin n → B} (m : tupleType (graphLanguage k) a = tupleType _ b)
    (p q : Codes (Fin n) k) :
    Structure.RelMap (L := graphLanguage k) (p,q) a ↔ Structure.RelMap (L := graphLanguage k) (p,q) b := by
  let r : (graphLanguage k).Relations n := (p,q)
  have h := Set.ext_iff.mp m (r.formula fun i => Term.var i)
  change (r.formula fun i => Term.var i).Realize a ↔ (r.formula fun i => Term.var i).Realize b at h
  simpa only [Formula.realize_rel,Term.realize] using h

end ProjectiveTransfer

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {ι : Type}

/-- Restrictions of matching tuples to a parameter list and one of the new entries. -/
theorem match_entry {κ : Type*} {x y : ι → M} {a b : κ → M}
    (same : tupleType L (Sum.elim x a) = tupleType L (Sum.elim y b)) (i : κ) :
    tupleType L (point x (a i)) = tupleType L (point y (b i)) := by
  have h := match_subtuple same (Sum.elim Sum.inl fun _ : Unit => Sum.inr i)
  have cut (u : ι → M) (v : κ → M) :
      Sum.elim u v ∘ Sum.elim Sum.inl (fun _ : Unit => Sum.inr i) = point u (v i) := by
    funext j; cases j <;> rfl
  rwa [cut,cut] at h

private theorem inj_transfer {κ : Type*} {a b : κ → M} (same : tupleType L a = tupleType L b)
    (ha : Injective a) : Injective b := by
  intro i j eq
  apply ha
  have h := Set.ext_iff.mp same ((Term.var i).equal (Term.var j))
  change ((Term.var i).equal (Term.var j)).Realize a ↔ ((Term.var i).equal (Term.var j)).Realize b at h
  exact (Formula.realize_equal.mp (h.mpr (Formula.realize_equal.mpr eq)))

variable [Finite ι]

private theorem copy_card_le (fin : FiniteTypes L M) {x y : ι → M} {S T : Set M}
    (m : tupleType L x = tupleType L y)
    (comp : ∀ a b, tupleType L (point x a) = tupleType L (point y b) → (a ∈ S ↔ b ∈ T)) :
    S.encard ≤ T.encard := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  obtain ⟨a,inside,inj⟩ := (S.le_encard_iff_exists_fin_injective n).mp hn
  obtain ⟨b,joint⟩ := extendTuple L (Eq.refl _) (fin (ι ⊕ Fin n)) m a
  have ab : tupleType L a = tupleType L b := match_subtuple joint Sum.inr
  exact (T.le_encard_iff_exists_fin_injective n).mpr
    ⟨b, fun i => (comp _ _ (match_entry joint i)).mp (inside i), inj_transfer ab inj⟩

/-- Any two sets of points that agree under matching all one-point extensions
have the same finite cardinal, or are both infinite. -/
theorem copy_card (fin : FiniteTypes L M) {x y : ι → M} {S T : Set M}
    (m : tupleType L x = tupleType L y)
    (comp : ∀ a b, tupleType L (point x a) = tupleType L (point y b) → (a ∈ S ↔ b ∈ T)) :
    S.encard = T.encard :=
  le_antisymm (copy_card_le fin m comp) (copy_card_le fin m.symm fun a b h => (comp b a h.symm).symm)

/-- The extended finite cardinality of a definable unary set depends only on the
complete type of its parameters. -/
theorem locus_card (fin : FiniteTypes L M) {x y : ι → M} (m : tupleType L x = tupleType L y)
    (φ : L.Formula (ι ⊕ Unit)) : (locus L x φ).encard = (locus L y φ).encard :=
  copy_card fin m fun _ _ h => Set.ext_iff.mp h φ

/-- Algebraicity is preserved under matching the full pointed tuples. -/
theorem algebraic_match (fin : FiniteTypes L M) {x y : ι → M} {a b : M}
    (m : tupleType L (point x a) = tupleType L (point y b)) : a ∈ tupleClosure L x ↔ b ∈ tupleClosure L y := by
  have base : tupleType L x = tupleType L y := match_subtuple m Sum.inl
  have go {u v : ι → M} {s t : M} (h : tupleType L (point u s) = tupleType L (point v t))
      (bse : tupleType L u = tupleType L v) (hs : s ∈ tupleClosure L u) : t ∈ tupleClosure L v := by
    obtain ⟨φ,has,small⟩ := hs
    exact ⟨φ,(Set.ext_iff.mp h φ).mp has,small.finite_of_encard_le (locus_card fin bse φ).ge⟩
  exact ⟨go m base,go m.symm base.symm⟩

/-- The finite sizes of the closures agree for elementarily matching parameter tuples. -/
theorem closure_card (fin : FiniteTypes L M) {x y : ι → M} (m : tupleType L x = tupleType L y) :
    (tupleClosure L x).encard = (tupleClosure L y).encard :=
  copy_card fin m fun _ _ h => algebraic_match fin h

end ProjectiveAlgebraic

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

private theorem acl_map (fin : FiniteTypes L A) (e : A ≃[L] A) {S : Set A} {a : A} (h : a ∈ acl L S) :
    e a ∈ acl L (e '' S) := by
  obtain ⟨n,v,inc,mem⟩ := h
  have t : tupleType L (point (e ∘ v) (e a)) = tupleType L (point v a) := by
    have cut : e ∘ point v a = point (e ∘ v) (e a) := by funext j; cases j <;> rfl
    rw [← cut]
    ext φ
    exact StrongHomClass.realize_formula e φ
  refine ⟨n,e ∘ v,?_,(algebraic_match fin t).mpr mem⟩
  rintro _ ⟨i,rfl⟩
  exact ⟨v i,inc (Set.mem_range_self i),rfl⟩

/-- Algebraic closure commutes with every automorphism, also on infinite and
externally given parameter sets. -/
theorem acl_image (fin : FiniteTypes L A) (e : A ≃[L] A) (S : Set A) :
    acl L (e '' S) = e '' acl L S := by
  ext y
  refine ⟨?_,fun ⟨x,hx,eq⟩ => eq ▸ acl_map fin e hx⟩
  intro hy
  have back := acl_map fin e.symm hy
  have eq : e.symm '' (e '' S) = S := by
    ext x
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      simpa using hz
    · intro h
      exact ⟨e x,⟨x,h,rfl⟩,e.symm_apply_apply x⟩
  exact ⟨e.symm y,eq ▸ back,e.apply_symm_apply y⟩

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

@[expose] public section

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

@[expose] public section

namespace ProjectiveBlocks

/-- A finite core and countably many blocks, each with `d` labelled positions. -/
abbrev Point (c d : ℕ) := Fin c ⊕ (ℕ × Fin d)

/-- Each of the `k` coordinates stores its finite/cofinite flag and its finite part. -/
abbrev Code (c d k : ℕ) := Fin k → Bool × Finset (Point c d)

/-- A block permutation fixes the core and preserves the position inside each block. -/
def relabel {c d : ℕ} (σ : Equiv.Perm ℕ) : Equiv.Perm (Point c d) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr σ (Equiv.refl _))

/-- Transport the actual finite subsets by the positionwise action. -/
def rename {c d k : ℕ} (σ : Equiv.Perm ℕ) (x : Code c d k) : Code c d k :=
  fun j => ((x j).1, (x j).2.map (relabel σ).toEmbedding)

/-- The self-map commutes with every block permutation. -/
def Equivariant {c d k : ℕ} (g : Code c d k → Code c d k) : Prop :=
  ∀ σ x, g (rename σ x) = rename σ (g x)

/-- The core and flags have `2^(k(1+c))` states, and there are `q` possible
patterns of a block, giving `q^q` output tables on input patterns. -/
def orbitBound (c d k : ℕ) : ℕ :=
  let q := 2 ^ (d * k)
  2 ^ (k * (1 + c)) * q ^ q

end ProjectiveBlocks

@[expose] public section

namespace ProjectiveBlocks

open Function Set

private abbrev Pattern (d k : ℕ) := Fin d × Fin k → Bool
private abbrev Table (c d k : ℕ) :=
  (Fin k → Bool) × (Fin c × Fin k → Bool) × (Pattern d k → Pattern d k)

private def pattern {c d k} (x : Code c d k) (i : ℕ) : Pattern d k :=
  fun p => decide (Sum.inr (i, p.1) ∈ (x p.2).2)

private def core {c d k} (x : Code c d k) : Fin c × Fin k → Bool :=
  fun p => decide (Sum.inl p.1 ∈ (x p.2).2)

private theorem ext_code {c d k} {x y : Code c d k}
    (hflag : ∀ j, (x j).1 = (y j).1) (hcore : core x = core y)
    (hblocks : ∀ i, pattern x i = pattern y i) : x = y := by
  funext j
  apply Prod.ext (hflag j)
  apply Finset.ext
  intro a
  obtain a | ⟨i,t⟩ := a
  · simpa [core] using congrFun hcore (a,j)
  · simpa [pattern] using congrFun (hblocks i) (t,j)

private theorem pattern_rename {c d k} (σ : Equiv.Perm ℕ) (x : Code c d k) (i : ℕ) :
    pattern (rename σ x) i = pattern x (σ.symm i) := by
  funext j
  simp only [pattern, rename, Finset.mem_map_equiv]
  rfl

private theorem core_rename {c d k} (σ : Equiv.Perm ℕ) (x : Code c d k) :
    core (rename σ x) = core x := by
  funext j
  simp only [core, rename, Finset.mem_map_equiv]
  rfl

private theorem iter_const {c d k} {g : Code c d k → Code c d k} (hg : Equivariant g)
    (s : Code c d k) {a b : ℕ} (hab : pattern s a = pattern s b) (n : ℕ) :
    pattern (g^[n] s) a = pattern (g^[n] s) b := by
  let σ := Equiv.swap a b
  have fixed : rename σ s = s := by
    apply ext_code (x := rename σ s) (y := s) (fun _ => rfl) (core_rename σ s)
    intro i
    rw [pattern_rename]
    change pattern s (Equiv.swap a b i) = pattern s i
    by_cases ha : i = a
    · simpa [ha] using hab.symm
    by_cases hb : i = b
    · simpa [hb] using hab
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  have stabilizes : rename σ (g^[n] s) = g^[n] s := by
    induction n with
    | zero => exact fixed
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← hg σ, ih]
  have hb := congrArg (fun x => pattern x b) stabilizes
  simpa only [pattern_rename, σ, Equiv.symm_swap, Equiv.swap_apply_right] using hb

private noncomputable def representative {c d k} (s : Code c d k) (p : Pattern d k) : ℕ :=
  open Classical in if h : ∃ i, pattern s i = p then Nat.find h else 0

private theorem rep_pattern {c d k} (s : Code c d k) (i : ℕ) :
    pattern s (representative s (pattern s i)) = pattern s i := by
  classical
  have h : ∃ j, pattern s j = pattern s i := ⟨i,rfl⟩
  simpa only [representative, dite_eq_left h] using Nat.find_spec h

private noncomputable def encode {c d k} (s x : Code c d k) : Table c d k :=
  (fun j => (x j).1, core x, fun p => pattern x (representative s p))

private theorem encode_inj {c d k} {g : Code c d k → Code c d k} (hg : Equivariant g)
    (s : Code c d k) : Set.InjOn (encode s) (Set.range (fun n => g^[n] s)) := by
  rintro _ ⟨n,rfl⟩ _ ⟨m,rfl⟩ h
  apply ext_code (congrFun (congrArg Prod.fst h)) (congrArg (fun t => t.2.1) h)
  intro i
  have hi := rep_pattern s i
  exact (iter_const hg s hi n).symm.trans <|
    (congrFun (congrArg (fun t => t.2.2) h) (pattern s i)).trans (iter_const hg s hi m)

private theorem table_card (c d k : ℕ) : Fintype.card (Table c d k) = orbitBound c d k := by
  simp only [Table, Pattern, orbitBound, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  rw [← Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  ring

/-- The explicit uniform bound in the manuscript counts all forward iterates of
any finite/cofinite code, including the finite parts on the fixed core. -/
theorem blockOrbitBound {c d k : ℕ} (g : Code c d k → Code c d k) (hg : Equivariant g)
    (s : Code c d k) :
    (Set.range fun n : ℕ => g^[n] s).Finite ∧
    (Set.range fun n : ℕ => g^[n] s).ncard ≤ orbitBound c d k := by
  classical
  let O := Set.range fun n : ℕ => g^[n] s
  have inj := encode_inj hg s
  have finite : O.Finite := Set.Finite.of_injOn (f := encode s) (t := Set.univ)
    (fun _ _ => trivial) inj (Set.finite_univ)
  refine ⟨finite, ?_⟩
  have le := O.ncard_le_ncard_of_injOn (encode s) (t := Set.univ) (fun _ _ => trivial) inj
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, table_card] using le

private theorem eventual_period {X : Type*} (f : X → X) (x : X) (B : ℕ)
    {a b : Fin (B+1)} (hab : a < b) (heq : f^[a.val] x = f^[b.val] x) :
    Function.IsPeriodicPt f B.factorial (f^[B] x) := by
  have hper : Function.IsPeriodicPt f (b.val - a.val) (f^[a.val] x) := by
    change f^[b.val-a.val] (f^[a.val] x) = f^[a.val] x
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le, heq]
  have ale : a.val ≤ B := by omega
  have pos : 0 < b.val-a.val := by omega
  have le : b.val-a.val ≤ B := by omega
  have period := (hper.trans_dvd (Nat.dvd_factorial pos le)).apply_iterate (B-a.val)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel ale] at period

/-- A surjective equivariant map has a single finite exponent working on all
codes. In particular it cannot be the noninjective surjection transferred to
this countable block model in the degenerate case of the paper. -/
theorem equivariantSurjection {c d k : ℕ} (g : Code c d k → Code c d k)
    (hg : Equivariant g) (hs : Function.Surjective g) :
    g^[(orbitBound c d k).factorial] = id ∧ Function.Injective g := by
  let B := orbitBound c d k
  have all (s : Code c d k) : Function.IsPeriodicPt g B.factorial s := by
    obtain ⟨x,rfl⟩ := hs.iterate B s
    let tags (n : Fin (B+1)) := encode x (g^[n.val] x)
    have count : Fintype.card (Table c d k) < Fintype.card (Fin (B+1)) := by
      rw [table_card, Fintype.card_fin]
      exact Nat.lt_succ_self B
    obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt tags count
    have same := encode_inj hg x ⟨i.val,rfl⟩ ⟨j.val,rfl⟩ he
    rcases lt_or_gt_of_ne hne with h | h
    · exact eventual_period g x B h same
    · exact eventual_period g x B h same.symm
  exact ⟨funext (fun s => (all s).eq),
    fun {_ _} h => (all _).eq_of_apply_eq_same (all _) (Nat.factorial_pos B) h⟩

end ProjectiveBlocks

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ} {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]

/-- The source structure's predicates record exactly the given map, even when the
coordinate masks overlap. This property holds by definition in `graphStructure f`. -/
def Records (f : Codes A k → Codes A k) : Prop :=
  ∀ {n : ℕ} (p q : Codes (Fin n) k) (v : Fin n → A),
    Structure.RelMap (L := graphLanguage k) (p,q) v ↔ f (decode v p) = decode v q

private theorem record_of_match {ι : Type} [Finite ι] {f : Codes A k → Codes A k}
    (hf : Records f) {a : ι → A} {b : ι → B}
    (m : tupleType (graphLanguage k) a = tupleType _ b) (p q : Codes ι k)
    (h : f (decode a p) = decode a q) : recorded (decode b p) (decode b q) := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have ma := match_subtuple m e.symm
  refine ⟨_, decode e p, decode e q, b ∘ e.symm, ?_, ?_, ?_⟩
  · simp [Function.comp_assoc]
  · simp [Function.comp_assoc]
  apply (match_relation ma _ _).mp
  apply (hf _ _ _).mpr
  simpa [Function.comp_assoc] using h

/-- Moving the enumeration of the finite parts, or its shape, preserves the
value of the recorded graph. Matching a larger tuple on the first side verifies
all potential other presentations without assuming a fixed output size. -/
theorem compareGraph {ι : Type} [Finite ι] {f : Codes A k → Codes A k}
    (hf : Records f) (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    {a : ι → A} {b : ι → B} (m : tupleType (graphLanguage k) a = tupleType _ b) (p q : Codes ι k) :
    f (decode a p) = decode a q ↔ recorded (decode b p) (decode b q) := by
  refine ⟨record_of_match hf m p q, ?_⟩
  rintro ⟨n,u,v,b',hu,hv,r⟩
  have sameTypes := realizedTypes_eq (graphLanguage k) eq (fin (ι ⊕ Fin n))
  obtain ⟨a',joint⟩ := extendTuple (graphLanguage k) (Eq.symm eq) (sameTypes ▸ fin _) m.symm b'
  have sub := match_subtuple joint (Sum.inr : Fin n → ι ⊕ Fin n)
  simp only [Sum.elim_comp_inr] at sub
  have rel := (hf u v a').mp ((match_relation sub u v).mp r)
  have h₁ := (match_cross joint p u).mp hu.symm
  have h₂ := (match_cross joint q v).mp hv.symm
  rwa [h₁,h₂]

/-- Interpret a pair whose masks use disjoint lists of entries. -/
theorem comparePair {ι κ : Type} [Finite ι] [Finite κ] {f : Codes A k → Codes A k}
    (hf : Records f) (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    {a : ι → A} {b : ι → B} {u : κ → A} {v : κ → B}
    (m : tupleType (graphLanguage k) (Sum.elim a u) = tupleType _ (Sum.elim b v))
    (p : Codes ι k) (q : Codes κ k) : f (decode a p) = decode u q ↔ recorded (decode b p) (decode v q) := by
  have h := compareGraph hf eq fin m (decode Sum.inl p) (decode Sum.inr q)
  simpa only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] using h

/-- Every tuple on the second side can first be matched on the first. -/
theorem match_from_right {ι : Type} [Finite ι] (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) (b : ι → B) :
    ∃ a : ι → A, tupleType (graphLanguage k) a = tupleType _ b := by
  have hs := realizedTypes_eq (graphLanguage k) eq (fin ι)
  change tupleType (graphLanguage k) b ∈ typesIn (graphLanguage k) A ι
  rw [hs]
  exact ⟨b,rfl⟩

/-- The graph interpreted on the second side is total. -/
theorem graph_total {f : Codes A k → Codes A k} (hf : Records f) (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) (x : Codes B k) : ∃ y, recorded x y := by
  obtain ⟨n,p,b,rfl⟩ := present x
  obtain ⟨a,m⟩ := match_from_right eq fin b
  obtain ⟨l,q,z,hz⟩ := present (f (decode a p))
  obtain ⟨w,joint⟩ := extendTuple (graphLanguage k) eq (fin (Fin n ⊕ Fin l)) m z
  exact ⟨_,(comparePair hf eq fin joint p q).mp hz.symm⟩

/-- The graph interpreted on the second side is single-valued. -/
theorem graph_functional {f : Codes A k → Codes A k} (hf : Records f) (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) {x y z : Codes B k} (hy : recorded x y)
    (hz : recorded x z) : y = z := by
  obtain ⟨n,p,q,b,rfl,rfl,r⟩ := hy
  obtain ⟨l,u,v,w,hu,rfl,t⟩ := hz
  obtain ⟨ab,m⟩ := match_from_right eq fin (Sum.elim b w)
  let a := ab ∘ Sum.inl
  let z := ab ∘ Sum.inr
  have joint : tupleType (graphLanguage k) (Sum.elim a z) = tupleType _ (Sum.elim b w) := by
    simpa [a,z] using m
  have m₁ := match_subtuple m (Sum.inl : Fin n → Fin n ⊕ Fin l)
  have m₂ := match_subtuple m (Sum.inr : Fin l → Fin n ⊕ Fin l)
  simp only [Sum.elim_comp_inl,Sum.elim_comp_inr] at m₁ m₂
  have h₁ := (hf p q a).mp ((match_relation m₁ p q).mpr r)
  have h₂ := (hf u v z).mp ((match_relation m₂ u v).mpr t)
  have h : decode a p = decode z u := (match_cross joint p u).mpr hu.symm
  exact (match_cross joint q v).mp (h₁.symm.trans ((congrArg f h).trans h₂))

end ProjectiveTransfer

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ} {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]

private def MatchesMaps (f : Codes A k → Codes A k) (g : Codes B k → Codes B k) : Prop :=
  ∀ {ι : Type} [Finite ι] {a : ι → A} {b : ι → B},
    tupleType (graphLanguage k) a = tupleType _ b → ∀ p q : Codes ι k,
      f (decode a p) = decode a q ↔ g (decode b p) = decode b q

private theorem lift_surjective {f : Codes A k → Codes A k} {g : Codes B k → Codes B k}
    (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    (graphs : MatchesMaps f g) (surj : Surjective f) : Surjective g := by
  intro x
  obtain ⟨n,p,b,rfl⟩ := present x
  obtain ⟨a,m⟩ := match_from_right eq fin b
  obtain ⟨pre,hpre⟩ := surj (decode a p)
  obtain ⟨l,q,z,rfl⟩ := present pre
  obtain ⟨w,joint⟩ := extendTuple (graphLanguage k) eq (fin (Fin n ⊕ Fin l)) m z
  have t := graphs joint (decode Sum.inr q) (decode Sum.inl p)
  simp only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] at t
  exact ⟨_,t.mp hpre⟩

private theorem lift_injective {f : Codes A k → Codes A k} {g : Codes B k → Codes B k}
    (eq : A ≅[graphLanguage k] B) (finB : FiniteTypes (graphLanguage k) B)
    (graphs : MatchesMaps f g) (inj : Injective g) : Injective f := by
  intro x y h
  obtain ⟨n,p,a,rfl⟩ := present x
  obtain ⟨m,q,b,rfl⟩ := present y
  obtain ⟨l,r,z,hz⟩ := present (f (decode a p))
  let v := Sum.elim a (Sum.elim b z)
  let X := decode (Sum.inl : Fin n → Fin n ⊕ (Fin m ⊕ Fin l)) p
  let Y := decode (fun j : Fin m => Sum.inr (Sum.inl j) : Fin m → Fin n ⊕ (Fin m ⊕ Fin l)) q
  let Z := decode (fun j : Fin l => Sum.inr (Sum.inr j) : Fin l → Fin n ⊕ (Fin m ⊕ Fin l)) r
  have ex : decode v X = decode a p := by simp only [X,decode_comp]; rfl
  have ey : decode v Y = decode b q := by simp only [Y,decode_comp]; rfl
  have ez : decode v Z = decode z r := by simp only [Z,decode_comp]; rfl
  obtain ⟨w,mw⟩ := match_from_right (Eq.symm eq) finB v
  have hx := (graphs mw.symm X Z).mp (by rw [ex,ez,hz])
  have hy := (graphs mw.symm Y Z).mp (by rw [ey,ez,hz,h])
  exact ex.symm.trans (((match_codes mw X Y).mp (inj (hx.trans hy.symm))).trans ey)

/-- In any elementarily equivalent structure, the graph predicates of a map on
coded finite/cofinite sets define a unique self-map. Surjectivity and injectivity
are both preserved and reflected. Finite type spectra are only required of the
source structure, and there is no uniform bound assumption on output lengths. -/
theorem transferGraph (k : ℕ) {M N : Type*} (f : Codes M k → Codes M k)
    [(graphLanguage k).Structure N] :
    letI := graphStructure f
    M ≅[graphLanguage k] N → FiniteTypes (graphLanguage k) M →
      ∃ g : Codes N k → Codes N k,
        (∀ x y, g x = y ↔ recorded x y) ∧
        (Surjective f ↔ Surjective g) ∧ (Injective f ↔ Injective g) := by
  let := graphStructure f
  intro eq fin
  have src : Records f := by intro n p q t; rfl
  have fin' : FiniteTypes (graphLanguage k) N := fun ι _ =>
    (realizedTypes_eq _ eq (fin ι)) ▸ fin ι
  let g (x : Codes N k) := Classical.choose (graph_total src eq fin x)
  have prop (x y : Codes N k) : g x = y ↔ recorded x y := by
    have chosen := Classical.choose_spec (graph_total src eq fin x)
    exact ⟨fun h => h ▸ chosen, graph_functional src eq fin chosen⟩
  have graphs : MatchesMaps f g := fun {_ _ _ _} h p q =>
    (compareGraph src eq fin h p q).trans (prop _ _).symm
  have reverse : MatchesMaps g f := fun {_ _ _ _} h p q => (graphs h.symm p q).symm
  exact ⟨g,prop,⟨lift_surjective eq fin graphs, lift_surjective (Eq.symm eq) fin' reverse⟩,
    ⟨lift_injective (Eq.symm eq) fin reverse, lift_injective eq fin' graphs⟩⟩

end ProjectiveTransfer

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveBlocks Function

/-- Permuting the blocks positionwise in the second structure preserves every
named first-order graph predicate. The core is pointwise fixed. -/
def BlockModel (c d k : ℕ) [(graphLanguage k).Structure (Point c d)] : Prop :=
  ∀ (σ : _root_.Equiv.Perm ℕ) {n : ℕ} (r : (graphLanguage k).Relations n) (v : Fin n → Point c d),
    Structure.RelMap r (relabel σ ∘ v) ↔ Structure.RelMap r v

private def blockAut {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k)
    (σ : _root_.Equiv.Perm ℕ) : Point c d ≃[graphLanguage k] Point c d where
  toEquiv := relabel σ
  map_fun' := fun f => nomatch f
  map_rel' := s σ

private def small {c d n : ℕ} : Fin c ⊕ (Fin n × Fin d) → Point c d :=
  Sum.map id fun a => (a.1.val, a.2)

/-- Every finite tuple lies in the permutation orbit of one using only as many
block indices as the length of the tuple. -/
private theorem normalize {c d : ℕ} {ι : Type} [Fintype ι] (v : ι → Point c d) :
    ∃ (σ : _root_.Equiv.Perm ℕ) (w : ι → Fin c ⊕ (Fin (Fintype.card ι) × Fin d)),
      relabel σ ∘ v = small ∘ w := by
  classical
  let tag (x : Point c d) : ℕ := Sum.elim (fun _ => 0) Prod.fst x
  let U := Finset.univ.image (tag ∘ v)
  have card : U.card ≤ Fintype.card ι := by simpa [U] using (Finset.card_image_le (f := tag ∘ v) (s := Finset.univ))
  let e := U.equivFin
  obtain ⟨σ,hσ⟩ := _root_.Equiv.Perm.exists_extending_pair (fun a : U => a.val)
    (fun a : U => (e a).val) Subtype.val_injective (Fin.val_injective.comp e.injective)
  have bound (i : ι) : σ (tag (v i)) < Fintype.card ι := by
    let a : U := ⟨_,Finset.mem_image_of_mem (tag ∘ v) (Finset.mem_univ i)⟩
    exact (hσ a).symm ▸ Nat.lt_of_lt_of_le (e a).isLt card
  have position (i : ι) : ∃ w, relabel σ (v i) = small (n := Fintype.card ι) w := by
    cases hx : v i with
    | inl t => exact ⟨.inl t,rfl⟩
    | inr t =>
      have h := bound i
      rw [hx] at h
      exact ⟨.inr (⟨σ t.1,h⟩,t.2),rfl⟩
  exact ⟨σ,fun i => (position i).choose, funext fun i => (position i).choose_spec⟩

private theorem blockTypes {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k) :
    FiniteTypes (graphLanguage k) (Point c d) := by
  intro ι _
  classical
  let := Fintype.ofFinite ι
  let T := Fin c ⊕ (Fin (Fintype.card ι) × Fin d)
  let ts (w : ι → T) := tupleType (graphLanguage k) (small ∘ w)
  apply (Set.finite_range ts).subset
  rintro _ ⟨v,rfl⟩
  obtain ⟨σ,w,hσ⟩ := normalize v
  refine ⟨w,?_⟩
  change tupleType _ (small ∘ w) = tupleType _ v
  rw [← hσ]
  ext φ
  exact StrongHomClass.realize_formula (blockAut s σ) φ

private theorem rename_decode {c d k : ℕ} (σ : _root_.Equiv.Perm ℕ) (x : Code c d k) :
    rename σ x = decode (relabel σ) x := by
  funext j
  apply Prod.ext
  · rfl
  · ext a
    simp only [rename,decode,Finset.mem_map,Finset.mem_image]
    rfl

private theorem rel_invariant {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k)
    (σ : _root_.Equiv.Perm ℕ) {x y : Code c d k} (h : recorded x y) : recorded (rename σ x) (rename σ y) := by
  obtain ⟨n,p,q,v,rfl,rfl,r⟩ := h
  exact ⟨n,p,q,relabel σ ∘ v, (rename_decode σ _ ▸ decode_comp _ _ _).symm,
    (rename_decode σ _ ▸ decode_comp _ _ _).symm, (s σ _ _).mpr r⟩

/-- The obstruction after passing to a countable symmetric block model. If a
surjection's graph structure is elementarily equivalent to such a model, the
original map is injective. No check on the number of tuple types or on the
lengths of the finite parts is assumed. -/
theorem obstructionOfBlockModel {M : Type*} (c d k : ℕ) (f : Codes M k → Codes M k)
    [(graphLanguage k).Structure (Point c d)] (model : BlockModel c d k) :
    letI := graphStructure f
    M ≅[graphLanguage k] (Point c d) → Surjective f → Injective f := by
  let := graphStructure f
  intro eq surj
  have finB := blockTypes model
  have fin : FiniteTypes (graphLanguage k) M := fun ι _ =>
    (realizedTypes_eq _ (Eq.symm eq) (finB ι)) ▸ finB ι
  obtain ⟨g,isGraph,sg,ig⟩ := transferGraph k f eq fin
  have equiv : Equivariant g := by
    intro σ x
    exact (isGraph _ _).mpr (rel_invariant model σ ((isGraph x _).mp rfl))
  exact ig.mpr <| (equivariantSurjection g equiv (sg.mp surj)).2

end ProjectiveTransfer

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic

variable {d : ℕ} {M : Type*} {κ ι : Type} (L : Language) [L.Structure M]

/-- One tuple lists the finite core followed by all positions in the designated blocks. -/
def marked (core : κ → M) (B : ℚ → Fin d → M) (m : ι → ℚ) : κ ⊕ (ι × Fin d) → M :=
  Sum.elim core fun ij => B (m ij.1) ij.2

/-- The full first-order type of an extra enumerated block over the marked ones. -/
def overMarks (core : κ → M) (B : ℚ → Fin d → M) (m : ι → ℚ) (t : ℚ) :=
  tupleType L (Sum.elim (marked core B m) (B t))

/-- Ordered indiscernibility over the named core, stated using increasing embeddings
of the rationals. Parameters can list their blocks in any order. -/
def OrderIndiscernible (core : κ → M) (B : ℚ → Fin d → M) : Prop :=
  ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (f : ℚ → ℚ), StrictMono f →
    tupleType L (marked core B m) = tupleType L (marked core B (f ∘ m))

/-- The distinguished point of an unmarked block is generic over the core and
all positions of the finitely many marked blocks. -/
def IndependentBlocks (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) : Prop :=
  ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (t : ℚ), t ∉ Set.range m →
    B t i₀ ∉ tupleClosure L (marked core B m)

/-- Every position in a block is algebraic over its distinguished point. -/
def AlgebraicBlocks (B : ℚ → Fin d → M) (i₀ : Fin d) : Prop :=
  ∀ t j, B t j ∈ tupleClosure L (fun _ : Unit => B t i₀)

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open Set Function

/-- Infinite Ramsey for a fixed tuple length and a finite palette. Restricting
to increasing tuples gives a single colour on an infinite subset of any
prescribed infinite set of natural numbers. -/
theorem ramseyTuples {C : Type*} [Finite C] (n : ℕ) (color : (Fin n → ℕ) → C)
    (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ c : C, ∀ t : Fin n → ℕ, StrictMono t → (∀ i, t i ∈ T) → color t = c := by
  classical
  induction n generalizing S with
  | zero =>
    exact ⟨S,Set.Subset.rfl,hS,color Fin.elim0,fun t _ _ => congrArg color (funext fun j => j.elim0)⟩
  | succ n ih =>
    let Host := {s : Set ℕ // s.Infinite}
    let p (s : Host) := s.property.nonempty.choose
    have mem (s : Host) : p s ∈ s.val := s.property.nonempty.choose_spec
    have step (s : Host) : ∃ t : Host, (t.val ⊆ s.val ∧ ∀ z ∈ t.val, p s < z) ∧
        ∃ c : C, ∀ v : Fin n → ℕ, StrictMono v → (∀ i, v i ∈ t.val) → color (Fin.cons (p s) v) = c := by
      have tail := s.property.sdiff (Set.finite_Iic (p s))
      obtain ⟨T,ht,large,c,hc⟩ := ih (fun v => color (Fin.cons (p s) v)) _ tail
      exact ⟨⟨_,large⟩,⟨ht.trans Set.sdiff_subset,fun z hz => lt_of_not_ge (ht hz).2⟩,c,hc⟩
    choose next spec using step
    let set : ℕ → Host := Nat.rec ⟨S,hS⟩ (fun _ s => next s)
    let v (i : ℕ) := p (set i)
    have decrease : Antitone fun i => (set i).val := antitone_nat_of_succ_le fun i => (spec (set i)).1.1
    have strict : StrictMono v := strictMono_nat_of_lt_succ fun i => (spec (set i)).1.2 _ (mem (set (i+1)))
    let col (i : ℕ) := (spec (set i)).2.choose
    obtain ⟨c,large⟩ := Finite.exists_infinite_fiber col
    let idx := {i | col i = c}
    have inf : idx.Infinite := Set.infinite_coe_iff.mp large
    refine ⟨v '' idx, ?_, inf.image strict.injective.injOn,c,?_⟩
    · rintro _ ⟨j,_,rfl⟩
      exact decrease (Nat.zero_le j) (mem (set j))
    · intro t mono inside
      choose pos hpos ep using inside
      let j := pos 0
      have eq (i : Fin n) : t i.succ ∈ (set (j+1)).val := by
        have lt : j < pos i.succ := strict.lt_iff_lt.mp (by rw [show v j = t 0 from ep 0, ep]; exact mono (Fin.succ_pos i))
        rw [← ep i.succ]
        exact decrease (Nat.succ_le_of_lt lt) (mem (set _))
      have hom := (spec (set j)).2.choose_spec (Fin.tail t) (mono.comp (fun _ _ h => Nat.succ_lt_succ h)) eq
      have reassemble : Fin.cons (p (set j)) (Fin.tail t) = t := by rw [show p (set j) = t 0 from ep 0,Fin.cons_self_tail]
      exact ((congrArg color reassemble).symm.trans hom).trans (hpos 0)

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ ι J : Type}

/-- A block tuple, with the named finite core. The entries may have any finite index type. -/
def layout (core : κ → M) (v : ι → Fin d → M) := Sum.elim core fun ij : ι × Fin d => v ij.1 ij.2

/-- Equality of the complete joint block types, keeping the core fixed. -/
def Matched (L : Language) {M : Type*} [L.Structure M] (core : κ → M) (v w : ι → Fin d → M) :=
  tupleType L (layout core v) = tupleType L (layout core w)

theorem restrict_match {c : κ → M} {a b : ι → Fin d → M} (h : Matched L c a b) (f : J → ι) :
    Matched L c (a ∘ f) (b ∘ f) := by
  have m := match_subtuple h (Sum.map id (Prod.map f id))
  have cut (v : ι → Fin d → M) : layout c v ∘ Sum.map id (Prod.map f id) = layout c (v ∘ f) := by
    funext i; cases i <;> rfl
  rwa [cut,cut] at m

/-- The labels have identical order relations. -/
def SameOrder {A B : Type*} [LT A] [LT B] {ι : Type*} (p : ι → A) (q : ι → B) : Prop :=
  ∀ i j, p i < p j ↔ q i < q j

/-- Realize any prescribed ordering of a finite tuple inside an infinite subset of ℕ. -/
theorem ordered_labels {A : Type*} [LinearOrder A] {n : ℕ} (p : Fin n → A) (inj : Injective p)
    {S : Set ℕ} (inf : S.Infinite) : ∃ t : Fin n → ℕ, (∀ i, t i ∈ S) ∧ SameOrder p t := by
  classical
  let perm := Tuple.sort p
  have strict : StrictMono (p ∘ perm) := (Tuple.monotone_sort p).strictMono_of_injective (inj.comp perm.injective)
  let t (i : Fin n) := Nat.nth (· ∈ S) (perm.symm i).val
  refine ⟨t,fun i => Nat.nth_mem_of_infinite inf _,?_⟩
  intro i j
  have h := strict.lt_iff_lt (a := perm.symm i) (b := perm.symm j)
  simp only [Function.comp_apply,_root_.Equiv.apply_symm_apply] at h
  exact h.trans (Nat.nth_strictMono inf).lt_iff_lt.symm

private theorem matching_palette [Finite κ] (fin : FiniteTypes L M) (core : κ → M)
    (R : ℕ → Fin d → M) (n : ℕ) (S : Set ℕ) (inf : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∀ t u : Fin n → ℕ, Injective t → SameOrder t u →
      (∀ i, t i ∈ T) → (∀ i, u i ∈ T) → Matched L core (R ∘ t) (R ∘ u) := by
  classical
  let palette := typesIn L M (κ ⊕ (Fin n × Fin d))
  let := (fin _).to_subtype (s := palette)
  let col (t : Fin n → ℕ) : palette := ⟨tupleType L (layout core (R ∘ t)),⟨_,rfl⟩⟩
  obtain ⟨T,sub,large,c,h⟩ := ramseyTuples n col S inf
  refine ⟨T,sub,large,?_⟩
  intro t u inj order ti ui
  let perm := Tuple.sort t
  have st : StrictMono (t ∘ perm) := (Tuple.monotone_sort t).strictMono_of_injective (inj.comp perm.injective)
  have su : StrictMono (u ∘ perm) := fun i j ij => (order (perm i) (perm j)).mp (st ij)
  have eq := (h _ st (fun i => ti _)).trans (h _ su (fun i => ui _)).symm
  have m : Matched L core (R ∘ t ∘ perm) (R ∘ u ∘ perm) := congrArg Subtype.val eq
  have undo := restrict_match m perm.symm
  have cancel (v : Fin n → ℕ) : (R ∘ v ∘ perm) ∘ perm.symm = R ∘ v := by funext i; simp
  rwa [cancel,cancel] at undo

/-- A descending sequence of infinite sets, with the complete type of each
finite length determined by the order on its corresponding set. -/
theorem homogeneous_levels [Finite κ] (fin : FiniteTypes L M) (core : κ → M) (R : ℕ → Fin d → M) :
    ∃ H : ℕ → Set ℕ, Antitone H ∧ (∀ n, (H n).Infinite) ∧
      ∀ n (t u : Fin n → ℕ), Injective t → SameOrder t u → (∀ i, t i ∈ H n) → (∀ i, u i ∈ H n) →
        Matched L core (R ∘ t) (R ∘ u) := by
  classical
  let Host := {S : Set ℕ // S.Infinite}
  have step (n : ℕ) (S : Host) : ∃ T : Host, T.val ⊆ S.val ∧
      ∀ t u : Fin n → ℕ, Injective t → SameOrder t u → (∀ i, t i ∈ T.val) → (∀ i, u i ∈ T.val) →
        Matched L core (R ∘ t) (R ∘ u) := by
    obtain ⟨T,sub,large,h⟩ := matching_palette fin core R n S.val S.property
    exact ⟨⟨T,large⟩,sub,h⟩
  choose next sub same using step
  let seq : ℕ → Host := Nat.rec ⟨Set.univ,Set.infinite_univ⟩ (fun n s => next (n+1) s)
  refine ⟨fun n => (seq n).val,antitone_nat_of_succ_le fun n => sub _ _,fun n => (seq n).property,?_⟩
  intro n
  cases n with
  | zero => intro t u _ _ _ _; exact (Subsingleton.elim t u) ▸ rfl
  | succ n => exact same _ (seq n)

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ : Type}

/-- Complete type of the first `n` enumerated positions, modeled by labels on the `n`th level. -/
def Stage (L : Language) {M : Type*} [L.Structure M] (c : κ → M)
    (R : ℕ → Fin d → M) (H : ℕ → Set ℕ) (name : ℕ ≃ ℚ) (n : ℕ) (v : Fin n → Fin d → M) : Prop :=
  ∃ t : Fin n → ℕ, (∀ i, t i ∈ H n) ∧ SameOrder (fun i : Fin n => name i.val) t ∧ Matched L c v (R ∘ t)

theorem order_inj {A B ι : Type*} [LinearOrder A] [LinearOrder B] {p : ι → A} {t : ι → B}
    (inj : Injective p) (eq : SameOrder p t) : Injective t := by
  intro i j h
  apply inj
  rcases lt_trichotomy (p i) (p j) with lt|eq'|gt
  · exact (h.not_lt ((eq i j).mp lt)).elim
  · exact eq'
  · exact (h.symm.not_lt ((eq j i).mp gt)).elim

/-- Replace the last position in an encoded block tuple by a new tuple of point matches. -/
private theorem put_last {n : ℕ} (c : κ → M) {s t : Fin (n+1) → Fin d → M}
    (m : tupleType L (Sum.elim (layout c (s ∘ Fin.castSucc)) (s (Fin.last n))) =
      tupleType L (Sum.elim (layout c (t ∘ Fin.castSucc)) (t (Fin.last n)))) : Matched L c s t := by
  let keep : κ ⊕ (Fin (n+1) × Fin d) → (κ ⊕ (Fin n × Fin d)) ⊕ Fin d :=
    Sum.elim (fun x => .inl (.inl x)) fun ij =>
      Fin.lastCases (.inr ij.2) (fun i => .inl (.inr (i,ij.2))) ij.1
  have cut (v : Fin (n+1) → Fin d → M) :
      Sum.elim (layout c (v ∘ Fin.castSucc)) (v (Fin.last n)) ∘ keep = layout c v := by
    funext i
    rcases i with j|⟨j,t⟩
    · rfl
    · refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp [keep,layout]
  have h := match_subtuple m keep
  rwa [cut,cut] at h

private theorem step_stage [Finite κ] (fin : FiniteTypes L M) (c : κ → M) (R : ℕ → Fin d → M)
    (H : ℕ → Set ℕ) (down : Antitone H) (inf : ∀ n, (H n).Infinite)
    (hom : ∀ n (t u : Fin n → ℕ), Injective t → SameOrder t u → (∀ i, t i ∈ H n) →
      (∀ i, u i ∈ H n) → Matched L c (R ∘ t) (R ∘ u))
    (name : ℕ ≃ ℚ) (n : ℕ) (v : Fin n → Fin d → M) (stage : Stage L c R H name n v) :
    ∃ w : Fin (n+1) → Fin d → M, Stage L c R H name (n+1) w ∧ ∀ i, w i.castSucc = v i := by
  classical
  obtain ⟨t,ti,ord,mat⟩ := stage
  obtain ⟨u,ui,ordU⟩ := ordered_labels (fun i : Fin (n+1) => name i.val)
    (name.injective.comp Fin.val_injective) (inf (n+1))
  let old := u ∘ Fin.castSucc
  have oo : SameOrder t old := fun i j => (ord i j).symm.trans (ordU i.castSucc j.castSucc)
  have eq := hom n t old (order_inj (name.injective.comp Fin.val_injective) ord) oo ti
    (fun i => down (Nat.le_succ n) (ui i.castSucc))
  have base : Matched L c (R ∘ old) v := Eq.symm (mat.trans eq)
  obtain ⟨z,all⟩ := extendTuple L (Eq.refl _) (fin ((κ ⊕ (Fin n × Fin d)) ⊕ Fin d)) base (R (u (Fin.last n)))
  let w : Fin (n+1) → Fin d → M := Fin.snoc v z
  have pre : w ∘ Fin.castSucc = v := by funext i; simp [w]
  have end' : w (Fin.last n) = z := by simp [w]
  refine ⟨w,⟨u,ui,ordU,?_⟩,fun i => congrFun pre i⟩
  apply Eq.symm
  apply put_last
  rw [pre,end']
  exact all

/-- Assemble coherent stages in the original homogeneous structure. Every
finite prefix agrees with a tuple from the corresponding homogeneous level. -/
theorem assemble_stages [Finite κ] (fin : FiniteTypes L M) (c : κ → M) (R : ℕ → Fin d → M)
    (H : ℕ → Set ℕ) (down : Antitone H) (inf : ∀ n, (H n).Infinite)
    (hom : ∀ n (t u : Fin n → ℕ), Injective t → SameOrder t u → (∀ i, t i ∈ H n) →
      (∀ i, u i ∈ H n) → Matched L c (R ∘ t) (R ∘ u)) (name : ℕ ≃ ℚ) :
    ∃ B : ℚ → Fin d → M, ∀ n, Stage L c R H name n (fun i : Fin n => B (name i.val)) := by
  classical
  let Good (n : ℕ) := {v : Fin n → Fin d → M // Stage L c R H name n v}
  have start : Stage L c R H name 0 Fin.elim0 := by
    refine ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,?_⟩
    exact congrArg (fun g => tupleType L (layout c g)) (Subsingleton.elim _ _)
  have succ (n : ℕ) (v : Good n) : ∃ w : Good (n+1), ∀ i, w.val i.castSucc = v.val i := by
    obtain ⟨w,good,pre⟩ := step_stage fin c R H down inf hom name n v.val v.property
    exact ⟨⟨w,good⟩,pre⟩
  choose next extends' using succ
  let stages : (n : ℕ) → Good n := Nat.rec ⟨Fin.elim0,start⟩ next
  have prev (n : ℕ) (i : Fin n) : (stages (n+1)).val i.castSucc = (stages n).val i := extends' _ _ _
  let B (q : ℚ) := (stages (name.symm q+1)).val (Fin.last _)
  have atIndex (n : ℕ) (i : Fin n) : B (name i.val) = (stages n).val i := by
    induction n with
    | zero => exact i.elim0
    | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact congrArg (fun r => (stages (r+1)).val (Fin.last r)) (name.symm_apply_apply n)
      · exact (ih j).trans (prev n j).symm
  exact ⟨B,fun n => (funext (atIndex n)) ▸ (stages n).property⟩

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ : Type}

/-- Every finite tuple of distinct enumerated blocks in the new sequence has
the complete joint type of a tuple of distinct original enumerated blocks. -/
def BasedOn (L : Language) {M : Type*} [L.Structure M] (c : κ → M)
    (R : ℕ → Fin d → M) (B : ℚ → Fin d → M) : Prop :=
  ∀ {n : ℕ} (p : Fin n → ℚ), Injective p → ∃ t : Fin n → ℕ, Injective t ∧ Matched L c (B ∘ p) (R ∘ t)

private theorem from_prefix (c : κ → M) (R : ℕ → Fin d → M) (H : ℕ → Set ℕ) (down : Antitone H)
    (name : ℕ ≃ ℚ) (B : ℚ → Fin d → M) (st : ∀ n, Stage L c R H name n (fun i : Fin n => B (name i.val)))
    {n : ℕ} (p : Fin n → ℚ) : ∃ t : Fin n → ℕ, (∀ i, t i ∈ H n) ∧ SameOrder p t ∧ Matched L c (B ∘ p) (R ∘ t) := by
  classical
  let idx (i : Fin n) := name.symm (p i)
  let N := max n (Finset.univ.sup idx + 1)
  have bound (i : Fin n) : idx i < N := (Nat.lt_succ_of_le (Finset.le_sup (s := Finset.univ) (Finset.mem_univ i))).trans_le (le_max_right _ _)
  let pos (i : Fin n) : Fin N := ⟨idx i,bound i⟩
  obtain ⟨t,ins,ord,match'⟩ := st N
  have matchProof := restrict_match match' pos
  have shape : (fun i : Fin N => B (name i.val)) ∘ pos = B ∘ p := by funext i; simp [pos,idx]
  rw [shape] at matchProof
  refine ⟨t ∘ pos,fun i => down (le_max_left _ _) (ins (pos i)),?_,matchProof⟩
  intro i j
  simpa [pos,idx] using ord (pos i) (pos j)

/-- Construct rationally indexed order indiscernibles over the finite core.
Finite Ramsey thinning determines compatible joint types. Finite-type
extension then realizes the enumeration one new block at a time in the
source structure. -/
theorem extractOrderSequence [Finite κ] (fin : FiniteTypes L M) (core : κ → M) (R : ℕ → Fin d → M) :
    ∃ B : ℚ → Fin d → M, OrderIndiscernible L core B ∧ BasedOn L core R B := by
  classical
  let name := (Denumerable.eqv ℚ).symm
  obtain ⟨H,down,inf,hom⟩ := homogeneous_levels fin core R
  obtain ⟨B,st⟩ := assemble_stages fin core R H down inf hom name
  have realize {n : ℕ} (p : Fin n → ℚ) := from_prefix core R H down name B st p
  refine ⟨B,?_,?_⟩
  · intro ι hι m f hf
    let := Fintype.ofFinite ι
    let D := Finset.univ.image m
    let p (i : Fin D.card) : ℚ := (D.equivFin.symm i).val
    let r (i : ι) := D.equivFin ⟨m i,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    have cut : p ∘ r = m := by funext i; simp [p,r]
    obtain ⟨t,ti,ord,mb⟩ := realize p
    obtain ⟨u,ui,ord',mb'⟩ := realize (f ∘ p)
    have pinj : Injective p := Subtype.val_injective.comp D.equivFin.symm.injective
    have oo : SameOrder t u := fun i j => (ord i j).symm.trans (hf.lt_iff_lt.symm.trans (ord' i j))
    have mm : Matched L core (B ∘ p) (B ∘ (f ∘ p)) := mb.trans ((hom _ t u (order_inj pinj ord) oo ti ui).trans mb'.symm)
    have small := restrict_match mm r
    change Matched L core (B ∘ m) (B ∘ f ∘ m)
    simpa only [Function.comp_assoc,cut] using small
  · intro n p hp
    obtain ⟨t,_,ord,mat⟩ := realize p
    exact ⟨t,order_inj hp ord,mat⟩

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set

variable {L : Language} {M : Type*} [L.Structure M] {ι : Type}

/-- Swap the final two variables while retaining the base parameters. -/
private def swapLast : (ι ⊕ Unit) ⊕ Unit → (ι ⊕ Unit) ⊕ Unit
  | .inl (.inl i) => .inl (.inl i)
  | .inl (.inr _) => .inr ()
  | .inr _ => .inl (.inr ())

private theorem flip (x : ι → M) (a b : M) (φ : L.Formula ((ι ⊕ Unit) ⊕ Unit)) :
    b ∈ locus L (point x a) φ ↔ a ∈ locus L (point x b) (φ.relabel swapLast) := by
  change φ.Realize _ ↔ (φ.relabel swapLast).Realize _
  rw [Formula.realize_relabel]
  have e : point (point x a) b = point (point x b) a ∘ swapLast := by
    funext i
    rcases i with (i|i)|i <;> rfl
  rw [e]

/-- Algebraic closure satisfies exchange. The row containing `b` is finite.
If the inverse fibre through `a` were cofinite, more than the row size many
conjugates of `b` would have cofinite inverse fibres, with a common point. -/
theorem tuple_exchange [Finite ι] (fin : FiniteTypes L M) (min : Minimal L M) (x : ι → M) {a b : M}
    (ab : b ∈ tupleClosure L (point x a)) (bs : b ∉ tupleClosure L x) : a ∈ tupleClosure L (point x b) := by
  classical
  by_contra notAlg
  let joint := point (point x a) b
  obtain ⟨φ,hφ,iso⟩ := isolate (fin ((ι ⊕ Unit) ⊕ Unit)) joint
  let row (u : M) := locus L (point x u) φ
  let col (v : M) := locus L (point x v) (φ.relabel swapLast)
  have rfin : (row a).Finite := ((algebraic_iff_finite_type fin _ _).mp ab).subset
    (fun v hv => (iso (point (point x a) v)).mp hv)
  have ac : a ∈ col b := (flip x a b φ).mp hφ
  have cfin : (col b)ᶜ.Finite := (min _ (point x b) (φ.relabel swapLast)).resolve_left (fun h => notAlg ⟨_,ac,h⟩)
  let O := {v | tupleType L (point x v) = tupleType L (point x b)}
  have large : O.Infinite := fun small => bs ((algebraic_iff_finite_type fin x b).mpr small)
  obtain ⟨n,hn⟩ := rfin.exists_encard_eq_coe
  have enough : ((n+1 : ℕ) : ℕ∞) ≤ O.encard := large.encard_eq ▸ le_top
  obtain ⟨t,ht,inj⟩ := (O.le_encard_iff_exists_fin_injective (n+1)).mp enough
  have good (i : Fin (n+1)) : (col (t i))ᶜ.Finite := by
    have cmp := locus_card fin (ht i : tupleType L (point x (t i)) = tupleType L (point x b))
      (φ.relabel swapLast).not
    have cm (v : M) : locus L (point x v) (φ.relabel swapLast).not = (col v)ᶜ := by
      ext u; exact Formula.realize_not
    rw [cm,cm] at cmp
    exact cfin.finite_of_encard_le cmp.le
  have small : (⋃ i, (col (t i))ᶜ).Finite := Set.finite_iUnion good
  obtain ⟨u,_,outside⟩ := large.exists_notMem_finite small
  have mem (i : Fin (n+1)) : t i ∈ row u := by
    apply (flip x u (t i) φ).mpr
    by_contra h
    exact outside (Set.mem_iUnion.mpr ⟨i,h⟩)
  have ju := (iso (point (point x u) (t 0))).mp (mem 0)
  have ua : tupleType L (point x u) = tupleType L (point x a) := match_subtuple ju Sum.inl
  have rowEq := locus_card fin ua φ
  have tooMany := ((row u).le_encard_iff_exists_fin_injective (n+1)).mpr ⟨t,mem,inj⟩
  change (row u).encard = (row a).encard at rowEq
  rw [rowEq,hn] at tooMany
  exact Nat.not_succ_le_self n (ENat.natCast_le_natCast.mp tooMany)

end ProjectiveAlgebraic

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M]

/-- Extra tuple parameters preserve algebraicity, including when tuples have repetitions. -/
theorem tuple_mono {ι κ : Type*} (x : ι → M) (y : κ → M) (inc : Set.range x ⊆ Set.range y) :
    tupleClosure L x ⊆ tupleClosure L y := by
  classical
  choose t ht using fun i => inc (Set.mem_range_self i)
  rintro a ⟨φ,ha,small⟩
  let ψ := φ.relabel (Sum.map t id)
  have eq : locus L y ψ = locus L x φ := by
    ext b
    change (φ.relabel _).Realize _ ↔ _
    rw [Formula.realize_relabel]
    have m : point y b ∘ Sum.map t id = point x b := by
      funext i
      cases i with
      | inl i => exact ht i
      | inr u => rfl
    rw [m]
    rfl
  exact ⟨ψ,eq ▸ ha,eq ▸ small⟩

/-- Every displayed parameter itself belongs to the tuple closure. -/
theorem mem_of_param {ι : Type*} (x : ι → M) (i : ι) : x i ∈ tupleClosure L x := by
  let φ : L.Formula (ι ⊕ Unit) := (Term.var (Sum.inr ())).equal (Term.var (Sum.inl i))
  have eq : locus L x φ = {x i} := by
    ext b
    exact Formula.realize_equal
  exact ⟨φ,eq ▸ Set.mem_singleton _,eq ▸ Set.finite_singleton _⟩

/-- Algebraic closure is transitive over finite tuples: the finitely many
potential conjugates of the algebraic parameter tuple supply only finitely
many possible values. -/
theorem tuple_trans {ι κ : Type} [Finite ι] [Finite κ] (fin : FiniteTypes L M)
    (x : ι → M) (z : κ → M) (hz : ∀ j, z j ∈ tupleClosure L x) :
    tupleClosure L z ⊆ tupleClosure L x := by
  classical
  intro a ha
  let D := tupleClosure L x
  let := (finite_tupleClosure fin x).to_subtype
  let tuples : Set (κ → M) := Set.range (fun v : κ → D => (fun j => (v j).val))
  have small : (⋃ v ∈ tuples, tupleClosure L v).Finite :=
    (Set.finite_range _).biUnion (fun v _ => finite_tupleClosure fin v)
  apply (algebraic_iff_finite_type fin x a).mpr
  apply small.subset
  intro b hb
  have base : tupleType L (point x a) = tupleType L (point x b) := Eq.symm hb
  obtain ⟨w,joint⟩ := extendTuple L (Eq.refl _) (fin ((ι ⊕ Unit) ⊕ κ)) base z
  have mem (i : κ) : w i ∈ D := by
    have eqs := match_subtuple joint
      (Sum.elim (fun j : ι => Sum.inl (Sum.inl j)) fun _ : Unit => Sum.inr i)
    have cut (p : M) (v : κ → M) :
        Sum.elim (point x p) v ∘ Sum.elim (fun j : ι => Sum.inl (Sum.inl j)) (fun _ : Unit => Sum.inr i)
        = point x (v i) := by funext t; cases t <;> rfl
    rw [cut,cut] at eqs
    exact (algebraic_match fin eqs).mp (hz i)
  have eqs := match_subtuple joint (Sum.elim Sum.inr fun _ : Unit => Sum.inl (Sum.inr ()))
  have cut (p : M) (v : κ → M) :
      Sum.elim (point x p) v ∘ Sum.elim Sum.inr (fun _ : Unit => Sum.inl (Sum.inr ())) =
        point v p := by funext t; cases t <;> rfl
  rw [cut,cut] at eqs
  exact Set.mem_iUnion₂.mpr ⟨w,⟨fun i => ⟨_,mem i⟩,rfl⟩,(algebraic_match fin eqs).mp ha⟩

/-- The algebraic closure of the range of a finite tuple is its tuple closure. -/
theorem acl_range {ι : Type} [Finite ι] (x : ι → M) : acl L (Set.range x) = tupleClosure L x := by
  classical
  ext a
  constructor
  · rintro ⟨n,z,h,ha⟩; exact tuple_mono z x h ha
  · intro ha
    let := Fintype.ofFinite ι
    let e := Fintype.equivFin ι
    have eq : Set.range (x ∘ e.symm) = Set.range x := (e.symm.surjective.range_comp x)
    exact ⟨_,x ∘ e.symm,eq.subset,tuple_mono x _ eq.superset ha⟩

/-- Monotonicity of algebraic closure. -/
theorem acl_mono {S T : Set M} (h : S ⊆ T) : acl L S ⊆ acl L T := by
  rintro a ⟨n,x,hx,ha⟩
  exact ⟨n,x,hx.trans h,ha⟩

/-- Every parameter is algebraic over a set containing it. -/
theorem acl_extensive (S : Set M) : S ⊆ acl L S := by
  intro a ha
  let x : Fin 1 → M := fun _ => a
  exact ⟨1,x,fun _ ⟨_,h⟩ => h ▸ ha,mem_of_param x 0⟩

/-- For a finite set, enumerate its elements without repetitions. -/
noncomputable def enumerate (D : Finset M) (i : Fin D.card) : M := (D.equivFin.symm i).val

theorem range_enumerate (D : Finset M) : Set.range (enumerate D) = (D : Set M) := by
  ext a
  exact ⟨fun ⟨i,e⟩ => e ▸ (D.equivFin.symm i).property,
    fun h => ⟨D.equivFin ⟨a,h⟩,by simp [enumerate]⟩⟩

/-- Local finiteness for the closure operator on sets. -/
theorem finite_acl (fin : FiniteTypes L M) {S : Set M} (hs : S.Finite) : (acl L S).Finite := by
  classical
  obtain ⟨D,rfl⟩ := hs.exists_finset_coe
  rw [← range_enumerate D,acl_range]
  exact finite_tupleClosure fin _

/-- Transitivity for the closure operator on arbitrary parameter sets follows
by collecting the finitely many finite lists of parameters witnessing algebraicity. -/
theorem acl_idempotent (fin : FiniteTypes L M) (S : Set M) : acl L (acl L S) = acl L S := by
  classical
  refine Set.Subset.antisymm ?_ (acl_extensive _)
  rintro a ⟨n,z,hz,ha⟩
  choose ar x inside mem using fun i => hz (Set.mem_range_self i)
  let T := ⋃ i : Fin n, Set.range (x i)
  have small : T.Finite := Set.finite_iUnion fun i => Set.finite_range (x i)
  obtain ⟨D,hD⟩ := small.exists_finset_coe
  let y := enumerate D
  have range : Set.range y = T := (range_enumerate D).trans hD
  have sub : T ⊆ S := Set.iUnion_subset inside
  have inc (i : Fin n) : Set.range (x i) ⊆ Set.range y := range ▸ Set.subset_iUnion (fun j => Set.range (x j)) i
  exact ⟨_,y,range.subset.trans sub,tuple_trans fin y z (fun i => tuple_mono _ y (inc i) (mem i)) ha⟩

end ProjectiveAlgebraic

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set

variable {L : Language} {M : Type*} [L.Structure M]

/-- Exchange for arbitrary parameter sets. Only the finite tuple witnessing the
algebraicity of `b` over `S ∪ {a}` enters the proof. -/
theorem acl_exchange (fin : FiniteTypes L M) (min : Minimal L M) (S : Set M) {a b : M}
    (ha : b ∈ acl L (insert a S)) (hb : b ∉ acl L S) : a ∈ acl L (insert b S) := by
  classical
  obtain ⟨n,z,inside,alg⟩ := ha
  let D := (Finset.univ.image z).erase a
  let x := enumerate D
  have dom : Set.range x = (D : Set M) := range_enumerate D
  have ds : (D : Set M) ⊆ S := by
    rintro u hu
    obtain ⟨ne,h⟩ := Finset.mem_erase.mp hu
    obtain ⟨i,_,hh⟩ := Finset.mem_image.mp h
    exact (Set.mem_insert_iff.mp (inside ⟨i,hh⟩)).resolve_left ne
  have inc : Set.range z ⊆ Set.range (point x a) := by
    rintro _ ⟨i,rfl⟩
    by_cases h : z i = a
    · exact ⟨.inr (),h.symm⟩
    · have hd : z i ∈ D := Finset.mem_erase.mpr ⟨h,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
      obtain ⟨j,hj⟩ := (dom ▸ hd : z i ∈ Set.range x)
      exact ⟨.inl j,hj⟩
  have gen : b ∉ tupleClosure L x := fun hx => hb ⟨_,x,dom.subset.trans ds,hx⟩
  have ex := tuple_exchange fin min x (tuple_mono z _ inc alg) gen
  have sub : Set.range (point x b) ⊆ insert b S := by
    rintro _ ⟨j,rfl⟩
    cases j with
    | inl j => exact Set.mem_insert_of_mem b (ds (dom ▸ Set.mem_range_self j))
    | inr j => exact Set.mem_insert b S
  have out := acl_mono (L := L) sub ((acl_range (L := L) (point x b)).symm ▸ ex)
  exact out

/-- Closure is finitary even on an arbitrary parameter set. -/
theorem acl_finite_character (S : Set M) (a : M) :
    a ∈ acl L S ↔ ∃ D : Finset M, (D : Set M) ⊆ S ∧ a ∈ acl L (D : Set M) := by
  classical
  refine ⟨?_,fun ⟨D,h,ha⟩ => acl_mono h ha⟩
  rintro ⟨n,x,inc,hx⟩
  let D := Finset.univ.image x
  have eq : (D : Set M) = Set.range x := by simp [D]
  exact ⟨D,eq.subset.trans inc,eq ▸ (acl_range (L := L) x).symm ▸ hx⟩

/-- In a minimal structure with finitely many types of each finite arity,
algebraic closure is a locally finite pregeometry. -/
theorem pregeometry (fin : FiniteTypes L M) (min : Minimal L M) :
    (∀ S : Set M, S ⊆ acl L S) ∧
    (∀ S T : Set M, S ⊆ T → acl L S ⊆ acl L T) ∧
    (∀ S : Set M, acl L (acl L S) = acl L S) ∧
    (∀ S : Set M, ∀ a, a ∈ acl L S ↔ ∃ D : Finset M, (D : Set M) ⊆ S ∧ a ∈ acl L (D : Set M)) ∧
    (∀ S : Set M, S.Finite → (acl L S).Finite) ∧
    (∀ (S : Set M) (a b : M), b ∈ acl L (insert a S) → b ∉ acl L S → a ∈ acl L (insert b S)) :=
  ⟨acl_extensive,fun _ _ => acl_mono,acl_idempotent fin,acl_finite_character,
    fun _ => finite_acl fin,fun S _ _ => acl_exchange fin min S⟩

end ProjectiveAlgebraic

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ I : Type}

/-- Degeneracy means that the closure of each nonempty finite set is the union
of its singleton closures, as in the manuscript and Truss's definition. -/
def Degenerate (L : Language) (M : Type*) [L.Structure M] : Prop :=
  ∀ D : Finset M, D.Nonempty → acl L (D : Set M) = ⋃ x ∈ D, acl L {x}

/-- The displayed core enumerates algebraic closure of the empty set. The other
coordinates are disjoint blocks and enumerate each singleton closure off the core. -/
structure BlockChart (L : Language) {M : Type*} [L.Structure M] (core : κ → M)
    (B : I → Fin d → M) : Prop where
  core_exact : Set.range core = acl L ∅
  disjoint : Injective (layout core B)
  singleton_exact : ∀ t j, acl L {B t j} = Set.range core ∪ Set.range (B t)

/-- A set containing the core and stable under singleton closure is closed
under all algebraic closure in the degenerate case. -/
theorem closed_of_singletons (deg : Degenerate L M) (S : Set M) (core : acl L ∅ ⊆ S)
    (stable : ∀ a ∈ S, acl L {a} ⊆ S) : acl L S = S := by
  classical
  refine Set.Subset.antisymm ?_ (acl_extensive _)
  intro x hx
  obtain ⟨D,ds,mem⟩ := (acl_finite_character S x).mp hx
  rcases D.eq_empty_or_nonempty with rfl | h
  · exact core (by simpa using mem)
  · rw [deg D h] at mem
    obtain ⟨a,ad,hx⟩ := Set.mem_iUnion₂.mp mem
    exact stable _ (ds ad) hx

private theorem cl_of_mem (fin : FiniteTypes L M) (a : M) {S : Set M} (h : a ∈ acl L S) :
    acl L {a} ⊆ acl L S := (acl_mono (Set.singleton_subset_iff.mpr h)).trans (acl_idempotent fin S).subset

private theorem equal_cl (fin : FiniteTypes L M) (min : Minimal L M) {a x : M}
    (h : x ∈ acl L {a}) (outside : x ∉ acl L ∅) : acl L {x} = acl L {a} := by
  have back : a ∈ acl L {x} := by simpa using acl_exchange fin min ∅ (a := a) (b := x) (by simpa using h) outside
  exact Set.Subset.antisymm (cl_of_mem fin _ h) (cl_of_mem fin _ back)

theorem separated_points [Infinite M] (fin : FiniteTypes L M) :
    ∃ z : ℕ → M, (∀ i, z i ∉ acl L ∅) ∧ ∀ i j, i < j → z j ∉ acl L {z i} := by
  classical
  choose pick fresh using fun s : Finset M => (finite_acl fin s.finite_toSet).exists_notMem
  let seen : ℕ → Finset M := Nat.rec ∅ fun _ s => insert (pick s) s
  let z (i : ℕ) := pick (seen i)
  have inc : Monotone seen := monotone_nat_of_le_succ fun i => Finset.subset_insert _ _
  refine ⟨z,fun i h => fresh (seen i) (acl_mono (Set.empty_subset _) h),?_⟩
  intro i j lt h
  have member : z i ∈ seen j := inc (Nat.succ_le_of_lt lt) (Finset.mem_insert_self _ _)
  exact fresh (seen j) (acl_mono (Set.singleton_subset_iff.mpr member) h)

/-- Every infinite structure satisfying the finite-type and minimality hypotheses
has a finite algebraic core and countably many disjoint, equally sized,
enumerated singleton-closure blocks outside it. This concerns the external
first-order structure, including its actual finite definable sets. -/
theorem rawBlockChart [Infinite M] (fin : FiniteTypes L M) (min : Minimal L M) :
    ∃ (c d : ℕ) (_ : Fin d) (core : Fin c → M) (R : ℕ → Fin d → M), BlockChart L core R := by
  classical
  obtain ⟨z,out,apart⟩ := separated_points fin
  let C := acl L (∅ : Set M)
  have cf : C.Finite := finite_acl fin Set.finite_empty
  let Cset := cf.toFinset
  let core := enumerate Cset
  have ce : Set.range core = C := (range_enumerate Cset).trans cf.coe_toFinset
  have one (i : ℕ) : tupleClosure L (fun _ : Unit => z i) = acl L {z i} := by rw [← acl_range]; simp
  let S (i : ℕ) := acl L {z i} \ C
  have sf (i : ℕ) : (S i).Finite := (finite_acl fin (Set.finite_singleton _)).subset Set.sdiff_subset
  have si (i : ℕ) : z i ∈ S i := ⟨acl_extensive _ (Set.mem_singleton _),out i⟩
  have gen (i : ℕ) : tupleType L (fun _ : Unit => z i) = tupleType L (fun _ : Unit => z 0) := by
    let x : Empty → M := Empty.elim
    have base : tupleClosure L x = C := by rw [← acl_range,Set.range_eq_empty x]
    have m := generic_type min (x := x) (a := z i) (b := z 0)
      (fun h => out i (base.subset h)) (fun h => out 0 (base.subset h))
    exact match_subtuple m Sum.inr
  have sc (i : ℕ) : (S i).ncard = (S 0).ncard := by
    have eq := closure_card fin (gen i)
    rw [one,one] at eq
    have ci (j : ℕ) : C ⊆ acl L {z j} := acl_mono (Set.empty_subset _)
    rw [Set.ncard_def,Set.ncard_def]
    simp only [S,Set.encard_sdiff (ci _) cf,eq]
  let D (i : ℕ) := (sf i).toFinset
  let width := (D 0).card
  have wc (i : ℕ) : (D i).card = width := by
    simpa only [D,width,← Set.ncard_eq_toFinset_card] using sc i
  let e (i : ℕ) := (D i).equivFinOfCardEq (wc i)
  let R (i : ℕ) (j : Fin width) := ((e i).symm j).val
  have re (i : ℕ) : Set.range (R i) = S i := by
    ext a
    constructor
    · rintro ⟨j,rfl⟩
      exact (sf i).mem_toFinset.mp ((e i).symm j).property
    · intro h
      let w : D i := ⟨a,(sf i).mem_toFinset.mpr h⟩
      exact ⟨e i w,by simp [R,w]⟩
  have distinct {i j : ℕ} {x : M} (hx : x ∈ S i) (hy : x ∈ S j) : i = j := by
    have eq := (equal_cl fin min hx.1 hx.2).symm.trans (equal_cl fin min hy.1 hy.2)
    rcases lt_trichotomy i j with lt|rfl|gt
    · exact (apart i j lt (eq.symm.subset (si j).1)).elim
    · rfl
    · exact (apart j i gt (eq.subset (si i).1)).elim
  have rin (i) (j) : R i j ∈ S i := (re i).subset (Set.mem_range_self j)
  have wp : 0 < width := Finset.card_pos.mpr ⟨z 0,(sf 0).mem_toFinset.mpr (si 0)⟩
  refine ⟨Cset.card,width,⟨0,wp⟩,core,R,ce,?_,?_⟩
  · rintro (a|⟨i,t⟩) (b|⟨j,u⟩) eq
    · exact congrArg Sum.inl (Cset.equivFin.symm.injective (Subtype.ext eq))
    · change core a = R j u at eq
      exact ((rin j u).2 (eq ▸ ce.subset (Set.mem_range_self a))).elim
    · change R i t = core b at eq
      exact ((rin i t).2 (eq.symm ▸ ce.subset (Set.mem_range_self b))).elim
    · change R i t = R j u at eq
      have ij := distinct (rin i t) (eq.symm ▸ rin j u)
      subst j
      exact congrArg (fun p => Sum.inr (i,p)) ((e i).symm.injective (Subtype.ext eq))
  · intro i j
    rw [ce,re,equal_cl fin min (rin i j).1 (rin i j).2]
    exact (Set.union_sdiff_cancel (acl_mono (L := L) (Set.empty_subset _))).symm

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ I : Type}

private theorem coord_eq {J : Type*} {x y : J → M} (m : tupleType L x = tupleType L y) (i j : J) :
    x i = x j ↔ y i = y j := by
  have h := Set.ext_iff.mp m ((Term.var i).equal (Term.var j))
  exact Formula.realize_equal.symm.trans (h.trans Formula.realize_equal)

private theorem based_many {core : κ → M} {R : ℕ → Fin d → M} {B : ℚ → Fin d → M}
    (base : BasedOn L core R B) {J : Type} [Finite J] (p : J → ℚ) (hp : Injective p) :
    ∃ t : J → ℕ, Injective t ∧ Matched L core (B ∘ p) (R ∘ t) := by
  classical
  let := Fintype.ofFinite J
  let e := Fintype.equivFin J
  obtain ⟨u,inj,mu⟩ := base (p ∘ e.symm) (hp.comp e.symm.injective)
  refine ⟨u ∘ e,inj.comp e.injective,?_⟩
  have eq := restrict_match mu e
  simpa only [Function.comp_assoc,_root_.Equiv.symm_comp_self,Function.comp_id] using eq

private theorem local_inj {core : κ → M} {R : ℕ → Fin d → M} {B : ℚ → Fin d → M}
    (chart : BlockChart L core R) (base : BasedOn L core R B) {J : Type} [Finite J] (p : J → ℚ) (hp : Injective p) :
    Injective (layout core (B ∘ p)) := by
  obtain ⟨u,inj,h⟩ := based_many base p hp
  intro i j eq
  have r := (coord_eq h i j).mp eq
  let incl : κ ⊕ (J × Fin d) → κ ⊕ (ℕ × Fin d) := Sum.map id (Prod.map u id)
  have cut (i) : layout core (R ∘ u) i = layout core R (incl i) := by cases i <;> rfl
  rw [cut,cut] at r
  have same := chart.disjoint r
  rcases i with i|⟨i,a⟩ <;> rcases j with j|⟨j,b⟩ <;> simp_all [incl,inj.eq_iff]

private theorem full_inj {core : κ → M} {R : ℕ → Fin d → M} {B : ℚ → Fin d → M}
    (chart : BlockChart L core R) (base : BasedOn L core R B) : Injective (layout core B) := by
  classical
  intro i j eq
  let tag : κ ⊕ (ℚ × Fin d) → ℚ := Sum.elim (fun _ => 0) Prod.fst
  let S : Finset ℚ := {tag i,tag j}
  let pack (p : κ ⊕ (ℚ × Fin d)) (hp : tag p ∈ S) : κ ⊕ (S × Fin d) := match p with
    | .inl a => .inl a
    | .inr (t,b) => .inr (⟨t,hp⟩,b)
  let incl : κ ⊕ (S × Fin d) → κ ⊕ (ℚ × Fin d) := Sum.map id (Prod.map Subtype.val id)
  have back (p hp) : incl (pack p hp) = p := by cases p <;> rfl
  have val (p hp) : layout core (B ∘ (Subtype.val : S → ℚ)) (pack p hp) = layout core B p := by cases p <;> rfl
  have mi : tag i ∈ S := by simp [S]
  have mj : tag j ∈ S := by simp [S]
  have h := local_inj chart base (Subtype.val : S → ℚ) Subtype.val_injective ((val i mi).trans (eq.trans (val j mj).symm))
  exact (back i mi).symm.trans ((congrArg incl h).trans (back j mj))

/-- Pointwise type matching transfers the fact that the displayed block
exhausts the singleton closure off the core, including all possible additional
ambient elements outside the displayed points. -/
theorem inherit_chart [Finite κ] (fin : FiniteTypes L M) {core : κ → M} {R : ℕ → Fin d → M}
    {B : ℚ → Fin d → M} (chart : BlockChart L core R) (base : BasedOn L core R B) : BlockChart L core B := by
  refine ⟨chart.core_exact,full_inj chart base,?_⟩
  intro t j
  let p (_ : Unit) := t
  obtain ⟨u,_,mat⟩ := based_many base p (fun i l _ => Subsingleton.elim i l)
  let X := layout core (B ∘ p)
  let Y := layout core (R ∘ u)
  ext x
  obtain ⟨v,joint⟩ := extendTuple L (Eq.refl _) (fin ((κ ⊕ (Unit × Fin d)) ⊕ Unit)) mat (fun _ : Unit => x)
  have m : tupleType L (point X x) = tupleType L (point Y (v ())) := by
    have eq : (fun _ : Unit => v ()) = v := funext fun z => by cases z; rfl
    simpa [point,eq,X,Y] using joint
  let idx := Sum.inr ((),j) (α := κ)
  let keep : Unit ⊕ Unit → (κ ⊕ (Unit × Fin d)) ⊕ Unit := Sum.map (fun _ => idx) id
  have cut (y : κ ⊕ (Unit × Fin d) → M) (z : M) : point y z ∘ keep = point (fun _ : Unit => y idx) z := by
    funext i; cases i <;> rfl
  have sub := match_subtuple m keep
  rw [cut,cut] at sub
  have alg := algebraic_match fin sub
  have one (a : M) : tupleClosure L (fun _ : Unit => a) = acl L {a} := by rw [← acl_range]; simp
  rw [one,one] at alg
  change x ∈ acl L {B t j} ↔ v () ∈ acl L {R (u ()) j} at alg
  rw [chart.singleton_exact _ _] at alg
  have coord (i : κ ⊕ (Unit × Fin d)) : X i = x ↔ Y i = v () := coord_eq m (.inl i) (.inr ())
  refine alg.trans ⟨?_,?_⟩
  · rintro (⟨a,h⟩ | ⟨l,h⟩)
    · exact Or.inl ⟨a,(coord (.inl a)).mpr h⟩
    · exact Or.inr ⟨l,(coord (.inr ((),l))).mpr h⟩
  · rintro (⟨a,h⟩ | ⟨l,h⟩)
    · exact Or.inl ⟨a,(coord (.inl a)).mp h⟩
    · exact Or.inr ⟨l,(coord (.inr ((),l))).mp h⟩

/-- The core together with any collection of whole blocks is algebraically
closed when the pregeometry is degenerate. -/
theorem chart_closed (fin : FiniteTypes L M) (deg : Degenerate L M) {core : κ → M}
    {B : I → Fin d → M} (chart : BlockChart L core B) {J : Type} (p : J → I) :
    acl L (Set.range (layout core (B ∘ p))) = Set.range (layout core (B ∘ p)) := by
  have cores : Set.range core ⊆ Set.range (layout core (B ∘ p)) := by
    rintro _ ⟨c,rfl⟩; exact ⟨.inl c,rfl⟩
  apply closed_of_singletons deg _ (chart.core_exact ▸ cores)
  rintro _ ⟨i,rfl⟩
  rcases i with c|⟨i,j⟩
  · have h : core c ∈ acl L (∅ : Set M) := chart.core_exact.subset (Set.mem_range_self c)
    have sub := (acl_mono (L := L) (Set.singleton_subset_iff.mpr h)).trans (acl_idempotent fin ∅).subset
    exact sub.trans (chart.core_exact ▸ cores)
  · change acl L {B (p i) j} ⊆ _
    rw [chart.singleton_exact]
    refine Set.union_subset cores ?_
    rintro _ ⟨k,rfl⟩; exact ⟨.inr (i,k),rfl⟩

/-- A new block's point is generic over any finitely many other blocks. -/
theorem chart_independent [Finite κ] (fin : FiniteTypes L M) (deg : Degenerate L M) {core : κ → M}
    {B : ℚ → Fin d → M} (chart : BlockChart L core B) (i₀ : Fin d) : IndependentBlocks L core B i₀ := by
  intro ι _ m t fresh member
  have inside : B t i₀ ∈ Set.range (layout core (B ∘ m)) :=
    (chart_closed fin deg chart m).subset ((acl_range (L := L) (marked core B m)).superset member)
  obtain ⟨j,h⟩ := inside
  rcases j with c|⟨i,l⟩
  · have same := chart.disjoint (a₁ := Sum.inl c) (a₂ := Sum.inr (t,i₀)) h
    cases same
  · have same := chart.disjoint (a₁ := Sum.inr (m i,l)) (a₂ := Sum.inr (t,i₀)) h
    exact fresh ⟨i,congrArg Prod.fst (Sum.inr.inj same)⟩

theorem chart_algebraic {core : κ → M} {B : ℚ → Fin d → M} (chart : BlockChart L core B)
    (i₀ : Fin d) : AlgebraicBlocks L B i₀ := by
  intro t j
  have one : tupleClosure L (fun _ : Unit => B t i₀) = acl L {B t i₀} := by rw [← acl_range]; simp
  rw [one,chart.singleton_exact]
  exact Or.inr (Set.mem_range_self j)

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {d : ℕ} {M : Type*} [L.Structure M] {κ ι : Type} [Finite κ] [Finite ι]

/-- Once a marked tuple is held fixed, all generic new distinguished points
can be matched to the same point. Their full enumerations then have only
finitely many possible images, bounded independently of the markers. -/
theorem markedTypeBound (fin : FiniteTypes L M) (min : Minimal L M)
    (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) (indep : IndependentBlocks L core B i₀)
    (alg : AlgebraicBlocks L B i₀) (m : ι → ℚ) (s : ℚ) (fresh : s ∉ Set.range m)
    {n : ℕ} (t : Fin n → ℚ) (free : ∀ i, t i ∉ Set.range m)
    (diff : Injective fun i => overMarks L core B m (t i)) :
    n ≤ (tupleClosure L (fun _ : Unit => B s i₀)).ncard ^ d := by
  classical
  let p := marked core B m
  let A := tupleClosure L (fun _ : Unit => B s i₀)
  have move (i : Fin n) : ∃ v : Fin d → M, (∀ j, v j ∈ A) ∧
      overMarks L core B m (t i) = tupleType L (Sum.elim p v) := by
    have same := generic_type min (indep m _ (free i)) (indep m _ fresh)
    obtain ⟨v,joint⟩ := extendTuple L (Eq.refl _) (fin (((κ ⊕ (ι × Fin d)) ⊕ Unit) ⊕ Fin d)) same (B (t i))
    refine ⟨v,?_,?_⟩
    · intro j
      let keep : Unit ⊕ Unit → ((κ ⊕ (ι × Fin d)) ⊕ Unit) ⊕ Fin d :=
        Sum.elim (fun _ => Sum.inl (Sum.inr ())) (fun _ => Sum.inr j)
      have h := match_subtuple joint keep
      have cut (u : M) (v : Fin d → M) : Sum.elim (point p u) v ∘ keep = point (fun _ : Unit => u) (v j) := by
        funext q; cases q <;> rfl
      rw [cut,cut] at h
      exact (algebraic_match fin h).mp (alg _ j)
    · let keep : (κ ⊕ (ι × Fin d)) ⊕ Fin d → ((κ ⊕ (ι × Fin d)) ⊕ Unit) ⊕ Fin d :=
        Sum.map Sum.inl id
      have h := match_subtuple joint keep
      have cut (u : M) (v : Fin d → M) : Sum.elim (point p u) v ∘ keep = Sum.elim p v := by
        funext q; cases q <;> rfl
      rwa [cut,cut] at h
  choose v inside hv using move
  let tag (i : Fin n) (j : Fin d) : A := ⟨v i j,inside i j⟩
  have inj : Injective tag := by
    intro i j h
    have eq : v i = v j := funext fun l => congrArg Subtype.val (congrFun h l)
    apply diff
    change overMarks L core B m (t i) = overMarks L core B m (t j)
    rw [hv i,hv j,eq]
  let := (finite_tupleClosure fin (fun _ : Unit => B s i₀)).fintype
  have le := Fintype.card_le_of_injective tag inj
  simpa only [Fintype.card_fin,Fintype.card_fun,Set.fintypeCard_eq_ncard,A] using le

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

/-- Integer-spaced marker positions used to replicate a finite order configuration. -/
def center (i : ℕ) : ℚ := 5*(i : ℚ)

noncomputable def offset (x : ℚ) : ℚ :=
  ((orderIsoIooNegOneOne ℚ) x).val - ((orderIsoIooNegOneOne ℚ) 0).val

private theorem offset_strict : StrictMono offset := by
  intro x y h
  have less : ((orderIsoIooNegOneOne ℚ) x).val < ((orderIsoIooNegOneOne ℚ) y).val :=
    (orderIsoIooNegOneOne ℚ).strictMono h
  unfold offset
  linarith

private theorem offset_zero : offset 0 = 0 := by simp [offset]

private theorem offset_bounds (x : ℚ) : -2 < offset x ∧ offset x < 2 := by
  obtain ⟨lo,hi⟩ := ((orderIsoIooNegOneOne ℚ) x).property
  obtain ⟨lo',hi'⟩ := ((orderIsoIooNegOneOne ℚ) 0).property
  unfold offset
  constructor <;> linarith

/-- Map prescribed `u < v` to `center i`, `center j`. Every other position
misses every marker, even when the other markers outnumber the original tuple. -/
noncomputable def movePair (u v : ℚ) (i j : ℕ) (x : ℚ) : ℚ :=
  if x < v then center i + offset (x-u) else center j + offset (x-v)

theorem movePair_strict {u v : ℚ} {i j : ℕ} (ij : i < j) : StrictMono (movePair u v i j) := by
  intro x y xy
  by_cases yv : y < v
  · simp only [movePair,ite_eq_left yv,ite_eq_left (xy.trans yv),add_lt_add_iff_left]
    exact offset_strict (sub_lt_sub_right xy _)
  by_cases xv : x < v
  · simp only [movePair,ite_eq_left xv,ite_eq_right yv,center]
    have le : (i:ℚ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt ij
    linarith [(offset_bounds (x-u)).2,(offset_bounds (y-v)).1]
  · simp only [movePair,ite_eq_right xv,ite_eq_right yv,add_lt_add_iff_left]
    exact offset_strict (sub_lt_sub_right xy _)

theorem movePair_left {u v : ℚ} (uv : u < v) (i j : ℕ) : movePair u v i j u = center i := by
  simp [movePair,uv,offset_zero]

theorem movePair_right (u v : ℚ) (i j : ℕ) : movePair u v i j v = center j := by
  simp [movePair,offset_zero]

private theorem offset_ne_center {i l : ℕ} {x : ℚ} (hx : x ≠ 0) : center i + offset x ≠ center l := by
  intro eq
  unfold center at eq
  rcases lt_trichotomy i l with h|rfl|h
  · have le : (i:ℚ)+1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [(offset_bounds x).2]
  · exact hx (offset_strict.injective (by rw [offset_zero]; linarith))
  · have le : (l:ℚ)+1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [(offset_bounds x).1]

theorem movePair_avoids {u v x : ℚ} {i j l : ℕ} (hu : x ≠ u) (hv : x ≠ v) :
    movePair u v i j x ≠ center l := by
  by_cases h : x < v
  · simpa only [movePair,ite_eq_left h] using (offset_ne_center (i := i) (l := l) (sub_ne_zero.mpr hu))
  · simpa only [movePair,ite_eq_right h] using (offset_ne_center (i := j) (l := l) (sub_ne_zero.mpr hv))

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {d : ℕ} {M : Type*} [L.Structure M] {κ ι : Type} [Finite κ] [Finite ι]

omit [Finite κ] in
private theorem over_moves {core : κ → M} {B : ℚ → Fin d → M} (oi : OrderIndiscernible L core B)
    (m : ι → ℚ) (s : ℚ) (f : ℚ → ℚ) (hf : StrictMono f) :
    overMarks L core B m s = overMarks L core B (f ∘ m) (f s) := by
  let aug (v : ι → ℚ) (u : ℚ) : Option ι → ℚ := fun | .none => u | .some j => v j
  let keep : (κ ⊕ (ι × Fin d)) ⊕ Fin d → κ ⊕ (Option ι × Fin d) :=
    Sum.elim (Sum.map id fun e => (some e.1,e.2)) fun j => Sum.inr (none,j)
  have cut (v : ι → ℚ) (u : ℚ) : marked core B (aug v u) ∘ keep = Sum.elim (marked core B v) (B u) := by
    funext p
    rcases p with (c|p)|j <;> rfl
  have cmap : f ∘ aug m s = aug (f ∘ m) (f s) := by funext p; cases p <;> rfl
  have h := match_subtuple (oi (aug m s) f hf) keep
  rwa [cmap,cut,cut] at h

omit [Finite κ] [Finite ι] in
private theorem over_restrict {β : Type} {core : κ → M} {B : ℚ → Fin d → M} (m : β → ℚ)
    {s t : ℚ} (eq : overMarks L core B m s = overMarks L core B m t) (subset : ι → β) :
    overMarks L core B (m ∘ subset) s = overMarks L core B (m ∘ subset) t := by
  let keep : (κ ⊕ (ι × Fin d)) ⊕ Fin d → (κ ⊕ (β × Fin d)) ⊕ Fin d :=
    Sum.map (Sum.map id (Prod.map subset id)) id
  have cut (u : ℚ) : Sum.elim (marked core B m) (B u) ∘ keep = Sum.elim (marked core B (m ∘ subset)) (B u) := by
    funext p; rcases p with (c|p)|j <;> rfl
  have h := match_subtuple eq keep
  rwa [cut,cut] at h

private theorem no_gaps_lt (fin : FiniteTypes L M) (min : Minimal L M)
    (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) (oi : OrderIndiscernible L core B)
    (indep : IndependentBlocks L core B i₀) (alg : AlgebraicBlocks L B i₀)
    (m : ι → ℚ) {u v : ℚ} (uv : u < v) (fu : u ∉ Set.range m) (fv : v ∉ Set.range m) :
    overMarks L core B m u = overMarks L core B m v := by
  classical
  by_contra different
  let bound := (tupleClosure L (fun _ : Unit => B (center 0) i₀)).ncard ^ d
  let I := Fin (bound+1)
  let allMarks (p : I × I × ι) := movePair u v p.1.val p.2.1.val (m p.2.2)
  have fresh (l : ℕ) : center l ∉ Set.range allMarks := by
    rintro ⟨p,eq⟩
    exact movePair_avoids (i := p.1.val) (j := p.2.1.val)
      (fun e => fu ⟨p.2.2,e⟩) (fun e => fv ⟨p.2.2,e⟩) eq
  have distinct {i j : I} (ij : i < j) :
      overMarks L core B allMarks (center i.val) ≠ overMarks L core B allMarks (center j.val) := by
    intro eq
    let f := movePair u v i.val j.val
    have rest := over_restrict allMarks eq (fun l : ι => (i,j,l))
    change overMarks L core B (f ∘ m) (center i.val) = overMarks L core B (f ∘ m) (center j.val) at rest
    have m₁ := over_moves oi m u f (movePair_strict ij)
    have m₂ := over_moves oi m v f (movePair_strict ij)
    rw [show f u = center i.val from movePair_left uv _ _] at m₁
    rw [show f v = center j.val from movePair_right _ _ _ _] at m₂
    exact different (m₁.trans (rest.trans m₂.symm))
  have inj : Injective (fun i : I => overMarks L core B allMarks (center i.val)) := by
    intro i j h
    rcases lt_trichotomy i j with lt | eq | gt
    · exact (distinct lt h).elim
    · exact eq
    · exact (distinct gt h.symm).elim
  have contradiction := markedTypeBound fin min core B i₀ indep alg allMarks (center 0) (fresh 0)
    (fun i : I => center i.val) (fun i => fresh i.val) inj
  exact Nat.not_succ_le_self bound contradiction

/-- With a finite core and algebraic enumerations of blocks, order-indiscernible
blocks in independent positions have the same type over any finite set of
other marked blocks, regardless of which gaps in the order they occupy. -/
theorem sameOverMarks (fin : FiniteTypes L M) (min : Minimal L M) (core : κ → M) (B : ℚ → Fin d → M)
    (i₀ : Fin d) (oi : OrderIndiscernible L core B) (indep : IndependentBlocks L core B i₀)
    (alg : AlgebraicBlocks L B i₀) (m : ι → ℚ) {u v : ℚ} (hu : u ∉ Set.range m) (hv : v ∉ Set.range m) :
    overMarks L core B m u = overMarks L core B m v := by
  rcases lt_trichotomy u v with lt | rfl | gt
  · exact no_gaps_lt fin min core B i₀ oi indep alg m lt hu hv
  · rfl
  · exact (no_gaps_lt fin min core B i₀ oi indep alg m gt hv hu).symm

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {d : ℕ} {M : Type*} [L.Structure M] {κ ι : Type} [Finite κ] [Finite ι]

private def substMark (m : ι → ℚ) (a b : ℚ) (i : ι) : ℚ := if m i = a then b else m i

omit [Finite κ] in
private theorem change_one (core : κ → M) (B : ℚ → Fin d → M)
    (gaps : ∀ {J : Type} [Finite J] (m : J → ℚ) {u v : ℚ}, u ∉ Set.range m → v ∉ Set.range m →
      overMarks L core B m u = overMarks L core B m v)
    (m : ι → ℚ) (a b : ℚ) (fresh : b ∉ Set.range m) :
    tupleType L (marked core B m) = tupleType L (marked core B (substMark m a b)) := by
  classical
  let T := {i : ι // m i ≠ a}
  let rest (i : T) := m i.val
  have fa : a ∉ Set.range rest := by rintro ⟨i,hi⟩; exact i.property hi
  have fb : b ∉ Set.range rest := by rintro ⟨i,hi⟩; exact fresh ⟨i.val,hi⟩
  have h := gaps rest fa fb
  let keep : κ ⊕ (ι × Fin d) → (κ ⊕ (T × Fin d)) ⊕ Fin d :=
    Sum.elim (fun c => Sum.inl (Sum.inl c)) fun p =>
      if h : m p.1 = a then Sum.inr p.2 else Sum.inl (Sum.inr (⟨p.1,h⟩,p.2))
  have cut (t : ℚ) : Sum.elim (marked core B rest) (B t) ∘ keep = marked core B (substMark m a t) := by
    funext p
    rcases p with v|⟨j,i⟩
    · rfl
    · by_cases h : m j = a <;> simp [keep,substMark,marked,rest,Function.comp_apply,h]
  have mm := match_subtuple h keep
  rw [cut,cut] at mm
  have id' : substMark m a a = m := by funext i; by_cases h : m i = a <;> simp [substMark,h]
  rwa [id'] at mm

omit [Finite κ] in
private theorem swap_types (core : κ → M) (B : ℚ → Fin d → M)
    (gaps : ∀ {J : Type} [Finite J] (m : J → ℚ) {u v : ℚ}, u ∉ Set.range m → v ∉ Set.range m →
      overMarks L core B m u = overMarks L core B m v)
    (m : ι → ℚ) (a b : ℚ) :
    tupleType L (marked core B m) = tupleType L (marked core B (_root_.Equiv.swap a b ∘ m)) := by
  classical
  by_cases eq : a = b
  · subst b; simp
  have small : (Set.range m ∪ {a,b}).Finite := (Set.finite_range m).union (by simp)
  obtain ⟨w,hw⟩ := small.exists_notMem
  have fw : w ∉ Set.range m := fun h => hw (Or.inl h)
  have wa : w ≠ a := fun h => hw (Or.inr (Or.inl h))
  have wb : w ≠ b := fun h => hw (Or.inr (Or.inr h))
  let u := substMark m a w
  let v := substMark u b a
  have h₁ := change_one core B gaps m a w fw
  have fa : a ∉ Set.range u := by
    rintro ⟨i,hi⟩
    by_cases e : m i = a <;> simp [u,substMark,e,wa] at hi
  have fb : b ∉ Set.range v := by
    rintro ⟨i,hi⟩
    by_cases e : u i = b <;> simp [v,substMark,e,eq] at hi
  have h₂ := change_one core B gaps u b a fa
  have h₃ := change_one core B gaps v w b fb
  have id' : substMark v w b = _root_.Equiv.swap a b ∘ m := by
    funext j
    have nw : m j ≠ w := fun h => fw ⟨j,h⟩
    by_cases ha : m j = a
    · simp [v,u,substMark,ha,wb]
    · by_cases hb : m j = b
      · simp [v,u,substMark,hb,Ne.symm eq,Ne.symm wa]
      · simp [v,u,substMark,ha,hb,nw,_root_.Equiv.swap_apply_def]
  rw [id'] at h₃
  exact h₁.trans (h₂.trans h₃)

/-- In this block geometry, every permutation of the rational index set
preserves the types of finite tuples of enumerated blocks, fixing the core.
The proof needs only finite type isolation and the explicit finite bound on
possible enumerations. -/
theorem totalIndiscernibility (fin : FiniteTypes L M) (min : Minimal L M)
    (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) (oi : OrderIndiscernible L core B)
    (indep : IndependentBlocks L core B i₀) (alg : AlgebraicBlocks L B i₀)
    (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ) :
    tupleType L (marked core B m) = tupleType L (marked core B (π ∘ m)) := by
  classical
  have gaps {J : Type} [Finite J] (m : J → ℚ) {u v : ℚ} := sameOverMarks fin min core B i₀ oi indep alg m (u := u) (v := v)
  let Good (e : _root_.Equiv.Perm ℚ) := ∀ z : ι → ℚ,
    tupleType L (marked core B z) = tupleType L (marked core B (e ∘ z))
  have approx (s : Finset ℚ) : ∃ e : _root_.Equiv.Perm ℚ, Good e ∧ ∀ i ∈ s, e i = π i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨_root_.Equiv.refl _,fun _ => rfl,by simp⟩
    | @insert a s fresh ih =>
      obtain ⟨e,good,agree⟩ := ih
      let f := _root_.Equiv.swap (e a) (π a)
      refine ⟨e.trans f,fun z => (good z).trans (swap_types core B gaps (e ∘ z) _ _),?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | mem
      · exact _root_.Equiv.swap_apply_left _ _
      · have ne : i ≠ a := fun h => fresh (h ▸ mem)
        have p : e i ≠ π a := (agree i mem) ▸ fun h => ne (π.injective h)
        exact (_root_.Equiv.swap_apply_of_ne_of_ne (fun h => ne (e.injective h)) p).trans (agree i mem)
  let := Fintype.ofFinite ι
  let s := Finset.univ.image m
  obtain ⟨e,good,agree⟩ := approx s
  have h : e ∘ m = π ∘ m := funext fun i => agree _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa only [h] using good m

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer ProjectiveBlocks Set Function

variable {k : ℕ} {M : Type*} [(graphLanguage k).Structure M]

@[instance_reducible] private def pull {P : Type*} (e : P → M) : (graphLanguage k).Structure P where
  funMap := fun {_} f => nomatch f
  RelMap := fun {_} r v => Structure.RelMap (L := graphLanguage k) r (e ∘ v)

/-- Tarski--Vaught for an infinite algebraically closed subset of this minimal
relational structure. A finite definable fibre is in algebraic closure of the
parameters, and a cofinite fibre meets the infinite subset. -/
private theorem elementary_pull {P : Type*} (e : P → M) (inj : Injective e) (large : (Set.range e).Infinite)
    (closed : acl (graphLanguage k) (Set.range e) = Set.range e) (min : Minimal (graphLanguage k) M) :
    letI := pull (k := k) e
    P ≅[graphLanguage k] M := by
  let := pull (k := k) e
  let embed : P ↪[graphLanguage k] M := {
    toEmbedding := ⟨e,inj⟩
    map_fun' := fun f => nomatch f
    map_rel' := fun _ _ => Iff.rfl }
  apply ElementaryEmbedding.elementarilyEquivalent
  apply embed.toElementaryEmbedding
  intro n φ v a ha
  let ix : Empty ⊕ Fin (n+1) → Fin n ⊕ Unit := Sum.elim Empty.elim (Fin.lastCases (.inr ()) Sum.inl)
  let ψ := φ.toFormula.relabel ix
  let p := e ∘ v
  have truth (z : M) : z ∈ locus (graphLanguage k) p ψ ↔ φ.Realize default (Fin.snoc p z) := by
    change (φ.toFormula.relabel ix).Realize _ ↔ _
    rw [Formula.realize_relabel,BoundedFormula.realize_toFormula]
    have cut : (point p z ∘ ix) ∘ Sum.inr = Fin.snoc p z := by
      funext j; refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp [ix,point]
    rw [cut,Unique.eq_default ((point p z ∘ ix) ∘ Sum.inl)]
  rcases min _ p ψ with small | cofin
  · have alg : a ∈ tupleClosure (graphLanguage k) p := ⟨ψ,(truth a).mpr ha,small⟩
    have mem : a ∈ Set.range e := closed.subset ⟨n,p,Set.range_comp_subset_range v e,alg⟩
    obtain ⟨x,rfl⟩ := mem
    exact ⟨x,ha⟩
  · obtain ⟨_,⟨x,rfl⟩,inside⟩ := large.exists_notMem_finite cofin
    exact ⟨x,(truth _).mp (Classical.not_not.mp inside)⟩

/-- The full positionwise symmetry of the induced countable structure follows
from total indiscernibility on finite blocks, including tuples containing core
points and repeated positions. -/
private theorem sequence_symmetry {c d : ℕ} (core : Fin c → M) (B : ℚ → Fin d → M) (name : ℕ ≃ ℚ)
    (full : ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ),
      tupleType (graphLanguage k) (marked core B m) = tupleType _ (marked core B (π ∘ m))) :
    letI := pull (k := k) (layout core (B ∘ name))
    BlockModel c d k := by
  let := pull (k := k) (layout core (B ∘ name))
  intro σ n r v
  let π := (name.symm.trans σ).trans name
  let idx (i : Fin n) : ℚ := match v i with | .inl _ => 0 | .inr (j,_) => name j
  let keep (i : Fin n) : Fin c ⊕ (Fin n × Fin d) := match v i with
    | .inl a => .inl a
    | .inr (_,j) => .inr (i,j)
  let e := layout core (B ∘ name)
  have raw : marked core B idx ∘ keep = e ∘ v := by
    funext i; cases h : v i <;> simp [idx,keep,e,marked,layout,h]
  have moved : marked core B (π ∘ idx) ∘ keep = e ∘ (relabel σ ∘ v) := by
    funext i; cases h : v i <;> simp [idx,keep,e,marked,layout,relabel,h,π]
  have m := match_subtuple (full idx π) keep
  rw [raw,moved] at m
  exact (match_relation m r.1 r.2).symm

/-- A closed union of rationally indexed, totally indiscernible enumerated
blocks and a finite core yields an elementary model with full block symmetry.
The proof applies the Tarski--Vaught test to the actual induced structure. -/
theorem elementaryOfSequence (min : Minimal (graphLanguage k) M) {c d : ℕ} (i₀ : Fin d)
    (core : Fin c → M) (B : ℚ → Fin d → M) (name : ℕ ≃ ℚ)
    (inj : Injective (layout core (B ∘ name)))
    (closed : acl (graphLanguage k) (Set.range (layout core (B ∘ name))) = Set.range (layout core (B ∘ name)))
    (full : ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ),
      tupleType (graphLanguage k) (marked core B m) = tupleType _ (marked core B (π ∘ m))) :
    ∃ s : (graphLanguage k).Structure (Point c d), letI := s
      (M ≅[graphLanguage k] Point c d) ∧ BlockModel c d k := by
  let e := layout core (B ∘ name)
  let : Nonempty (Fin d) := ⟨i₀⟩
  have large : (Set.range e).Infinite := Set.infinite_range_of_injective inj
  let := pull (k := k) e
  exact ⟨pull (k := k) e,(elementary_pull e inj large closed min).symm,sequence_symmetry core B name full⟩

/-- In the degenerate case the graph theory has an elementarily equivalent
countable model with a finite named core and uniform finite blocks, invariant
under the entire symmetric group of the blocks. -/
theorem symmetricBlockModel [Infinite M] (fin : FiniteTypes (graphLanguage k) M) (min : Minimal (graphLanguage k) M)
    (deg : Degenerate (graphLanguage k) M) :
    ∃ (c d : ℕ) (_ : Fin d) (s : (graphLanguage k).Structure (Point c d)),
      letI := s
      (M ≅[graphLanguage k] Point c d) ∧ BlockModel c d k := by
  classical
  obtain ⟨c,d,i₀,core,R,raw⟩ := rawBlockChart fin min
  obtain ⟨B,oi,base⟩ := extractOrderSequence fin core R
  have chart := inherit_chart fin raw base
  have full {ι : Type} [Finite ι] (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ) :=
    totalIndiscernibility fin min core B i₀ oi (chart_independent fin deg chart i₀) (chart_algebraic chart i₀) m π
  let name := (Denumerable.eqv ℚ).symm
  let e := layout core (B ∘ name)
  have cut : e = layout core B ∘ Sum.map id (Prod.map name id) := by funext i; cases i <;> rfl
  have inj : Injective e := by
    rw [cut]
    apply chart.disjoint.comp
    rintro (a|⟨i,j⟩) (b|⟨t,u⟩) h <;> simp_all
  obtain ⟨s,eq,inv⟩ := elementaryOfSequence min i₀ core B name inj (chart_closed fin deg chart name) full
  exact ⟨c,d,i₀,s,eq,inv⟩

end ProjectiveIndiscernibles

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M]

private theorem closure_inside {ι : Type} [Finite ι] {D : Finset M} (closed : acl L (D : Set M) = D)
    {x : ι → M} (hx : ∀ i, x i ∈ D) : tupleClosure L x ⊆ (D : Set M) := by
  rw [← acl_range x,← closed]
  exact acl_mono fun _ ⟨i,h⟩ => h ▸ hx i

/-- A prescribed new element in a finite closed set can be matched inside the
same set. Algebraic images lie in the set by closedness. For generic images,
the two closures already occupied have the same finite size. -/
private theorem add_inside {ι : Type} [Finite ι] (fin : FiniteTypes L M) (min : Minimal L M)
    {D : Finset M} (closed : acl L (D : Set M) = D) {x y : ι → M} (m : tupleType L x = tupleType L y)
    (hx : ∀ i, x i ∈ D) (hy : ∀ i, y i ∈ D) {a : M} (ha : a ∈ D) :
    ∃ b ∈ D, tupleType L (point x a) = tupleType L (point y b) := by
  obtain ⟨f,hf⟩ := extendTuple L (Eq.refl _) (fin (ι ⊕ Unit)) m (fun _ : Unit => a)
  have eq : tupleType L (point x a) = tupleType L (point y (f ())) := by
    have unique : (fun _ : Unit => f ()) = f := funext fun u => by cases u; rfl
    simpa [point,unique] using hf
  by_cases alg : a ∈ tupleClosure L x
  · exact ⟨f (),closure_inside closed hy ((algebraic_match fin eq).mp alg),eq⟩
  have proper : tupleClosure L x ⊂ (D : Set M) := Set.ssubset_iff_subset_ne.mpr
    ⟨closure_inside closed hx,fun h => alg (h ▸ ha)⟩
  have less := (finite_tupleClosure fin x).encard_lt_encard proper
  rw [closure_card fin m] at less
  have gap : ∃ b ∈ D, b ∉ tupleClosure L y := by
    by_contra! nogap
    exact (not_le_of_gt less) (Set.encard_mono (show (D : Set M) ⊆ tupleClosure L y from nogap))
  obtain ⟨b,hb,hAlg⟩ := gap
  exact ⟨b,hb,eq.trans (generic_type min (fun h => alg ((algebraic_match fin eq).mpr h)) hAlg)⟩

private theorem extend_inside (fin : FiniteTypes L M) (min : Minimal L M)
    {D : Finset M} (closed : acl L (D : Set M) = D) (n : ℕ) {ι : Type} [Finite ι]
    {x y : ι → M} (m : tupleType L x = tupleType L y)
    (hx : ∀ i, x i ∈ D) (hy : ∀ i, y i ∈ D) (a : Fin n → M) (ha : ∀ i, a i ∈ D) :
    ∃ b : Fin n → M, (∀ i, b i ∈ D) ∧ tupleType L (Sum.elim x a) = tupleType L (Sum.elim y b) := by
  induction n generalizing ι with
  | zero =>
    let pick : ι ⊕ Fin 0 → ι := Sum.elim id Fin.elim0
    have cut (p : ι → M) (v : Fin 0 → M) : p ∘ pick = Sum.elim p v := by
      funext j; rcases j with i|i; rfl; exact Fin.elim0 i
    have mm := match_subtuple m pick
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,?_⟩
    rwa [cut x a,cut y Fin.elim0] at mm
  | succ n ih =>
    obtain ⟨v,hv,one⟩ := add_inside fin min closed m hx hy (ha 0)
    have xIn (i : ι ⊕ Unit) : point x (a 0) i ∈ D := by cases i <;> first | exact hx _ | exact ha 0
    have yIn (i : ι ⊕ Unit) : point y v i ∈ D := by cases i <;> first | exact hy _ | exact hv
    obtain ⟨w,hw,all⟩ := ih one xIn yIn (fun j => a j.succ) (fun j => ha j.succ)
    let pick : ι ⊕ Fin (n+1) → (ι ⊕ Unit) ⊕ Fin n :=
      Sum.elim (fun i => Sum.inl (Sum.inl i)) (Fin.cases (Sum.inl (Sum.inr ())) Sum.inr)
    have cut (p : ι → M) (u : Fin (n+1) → M) :
        Sum.elim (point p (u 0)) (fun j => u j.succ) ∘ pick = Sum.elim p u := by
      funext i
      rcases i with i|i
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    let b : Fin (n+1) → M := Fin.cons v w
    refine ⟨b,fun i => Fin.cases hv hw i,?_⟩
    have mm := match_subtuple all pick
    rw [cut x a] at mm
    exact (cut y b) ▸ mm

/-- Every elementary match between two tuples in a finite closed set extends to
a permutation of that set that matches the full first-order types of all tuples. -/
theorem finite_extension {ι : Type} [Finite ι] (fin : FiniteTypes L M) (min : Minimal L M)
    (D : Finset M) (closed : acl L (D : Set M) = D) (x y : ι → D)
    (m : tupleType L (fun i => (x i).val) = tupleType L (fun i => (y i).val)) :
    ∃ e : D ≃ D, (∀ i, e (x i) = y i) ∧ ∀ (n : ℕ) (w : Fin n → D),
      tupleType L (fun j => (w j).val) = tupleType L (fun j => (e (w j)).val) := by
  classical
  let z := enumerate D
  obtain ⟨v,hv,joint⟩ := extend_inside fin min closed D.card m (fun i => (x i).property)
    (fun i => (y i).property) z (fun i => (D.equivFin.symm i).property)
  let map (a : D) : D := ⟨v (D.equivFin a),hv _⟩
  have zv : tupleType L z = tupleType L v := match_subtuple joint Sum.inr
  have equal {α : Type} {s t : α → M} (vs : tupleType L s = tupleType L t) (i j : α) :
      s i = s j ↔ t i = t j := by
    have h := Set.ext_iff.mp vs ((Term.var i).equal (Term.var j))
    change ((Term.var i).equal (Term.var j)).Realize s ↔ ((Term.var i).equal (Term.var j)).Realize t at h
    exact Formula.realize_equal.symm.trans (h.trans Formula.realize_equal)
  have inj : Injective map := by
    intro a b he
    have zEq := (equal zv (D.equivFin a) (D.equivFin b)).mpr (congrArg Subtype.val he)
    exact Subtype.ext (by simpa [z,enumerate] using zEq)
  let e := _root_.Equiv.ofBijective map ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨e,?_,?_⟩
  · intro i
    have h := (equal joint (Sum.inr (D.equivFin (x i))) (Sum.inl i)).mp (by simp [z,enumerate])
    exact Subtype.ext h
  · intro n w
    have h := match_subtuple zv (fun j => D.equivFin (w j))
    have cut : z ∘ (fun j => D.equivFin (w j)) = (fun j => (w j).val) := by
      funext j; simp [z,enumerate]
    rwa [cut] at h

end ProjectiveAlgebraic

@[expose] public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M]

/-- A permutation of a closed set preserves the inherited pregeometry on every
subset, using algebraic closure in the ambient structure on both sides. -/
def PreservesClosure (L : Language) {M : Type*} [L.Structure M] (D : Finset M) (e : D ≃ D) : Prop :=
  ∀ (V : Set D) (a : D), a.val ∈ acl L (Subtype.val '' V) ↔
    (e a).val ∈ acl L ((fun d : D => (e d).val) '' V)

/-- View an element of a finite subset in a larger finite subset. -/
def includePoint {T U : Finset M} (h : T ⊆ U) (x : T) : U := ⟨x.val,h x.property⟩

private theorem image_closure {A : Type*} (f : A → M) (S : Set A) (a : M) :
    a ∈ acl L (f '' S) ↔ ∃ (n : ℕ) (w : Fin n → A), (∀ i, w i ∈ S) ∧ a ∈ tupleClosure L (f ∘ w) := by
  classical
  constructor
  · rintro ⟨n,x,inc,ha⟩
    choose w hw eq using fun j => inc (Set.mem_range_self j)
    exact ⟨n,w,hw,(show f ∘ w = x from funext eq) ▸ ha⟩
  · rintro ⟨n,w,inside,ha⟩
    exact ⟨n,f ∘ w,fun _ ⟨j,eq⟩ => ⟨w j,inside j,eq⟩,ha⟩

private theorem preserves_of_elementary (fin : FiniteTypes L M) {D : Finset M} (e : D ≃ D)
    (elem : ∀ (n : ℕ) (u : Fin n → D), tupleType L (fun j => (u j).val) =
      tupleType L (fun j => (e (u j)).val)) : PreservesClosure L D e := by
  classical
  intro V d
  simp only [image_closure]
  have each (n : ℕ) (w : Fin n → D) : d.val ∈ tupleClosure L (Subtype.val ∘ w) ↔
      (e d).val ∈ tupleClosure L ((fun z : D => (e z).val) ∘ w) := by
    let I := Fin n ⊕ Unit
    let z := point w d
    let idx := Fintype.equivFin I
    have m := elem _ (z ∘ idx.symm)
    have pull := match_subtuple m idx
    have cut (f : D → M) : (fun j => f ((z ∘ idx.symm) j)) ∘ idx = point (f ∘ w) (f d) := by
      funext j
      rcases j with j|j <;> simp [Function.comp_def,z,point]
    change tupleType L ((fun j => Subtype.val ((z ∘ idx.symm) j)) ∘ idx) =
      tupleType L ((fun j => (fun t : D => (e t).val) ((z ∘ idx.symm) j)) ∘ idx) at pull
    rw [cut (fun t => t.val),cut (fun t => (e t).val)] at pull
    exact algebraic_match fin pull
  exact exists_congr fun n => exists_congr fun w => and_congr_right fun _ => each n w

/-- The local homogeneity and extension clauses. Given finite closed `S ⊆ D`,
any two points of `D \\ S` are related by a permutation fixing `S` pointwise
and preserving closure on every subset. That same permutation extends inside
every larger finite closed set. -/
theorem localHomogeneity (fin : FiniteTypes L M) (min : Minimal L M)
    (S D : Finset M) (sub : S ⊆ D) (sclosed : acl L (S : Set M) = S) (dclosed : acl L (D : Set M) = D)
    (a b : D) (ha : a.val ∉ S) (hb : b.val ∉ S) :
    ∃ e : D ≃ D, e a = b ∧ (∀ d : D, d.val ∈ S → e d = d) ∧ PreservesClosure L D e ∧
      ∀ (U : Finset M) (inc : D ⊆ U), acl L (U : Set M) = U →
        ∃ g : U ≃ U, (∀ d : D, g (includePoint inc d) = includePoint inc (e d)) ∧ PreservesClosure L U g := by
  classical
  let s (i : Fin S.card) := includePoint sub (S.equivFin.symm i)
  let x := point s a
  let y := point s b
  have eq : tupleClosure L (enumerate S) = (S : Set M) := by
    rw [← acl_range,range_enumerate,sclosed]
  have m := generic_type min (x := enumerate S) (a := a.val) (b := b.val) (fun h => ha (eq.subset h)) (fun h => hb (eq.subset h))
  have cut (v : D) : (fun i => (point s v i).val) = point (enumerate S) v.val := by
    funext i; cases i <;> rfl
  have initial : tupleType L (fun i => (x i).val) = tupleType L (fun i => (y i).val) := by
    simpa only [x,y,cut] using m
  obtain ⟨e,fix,elem⟩ := finite_extension fin min D dclosed x y initial
  refine ⟨e,fix (.inr ()),?_,preserves_of_elementary fin e elem,?_⟩
  · intro d hd
    let u : S := ⟨d.val,hd⟩
    have h := fix (.inl (S.equivFin u))
    have id' : s (S.equivFin u) = d := by simp [s,u,includePoint]
    change e (s (S.equivFin u)) = s (S.equivFin u) at h
    rwa [id'] at h
  · intro U inc closed
    let u := D.equivFin.symm
    obtain ⟨g,extension,elemU⟩ := finite_extension fin min U closed
      (fun i => includePoint inc (u i)) (fun i => includePoint inc (e (u i))) (elem _ u)
    refine ⟨g,?_,preserves_of_elementary fin g elemU⟩
    intro d
    simpa [u] using extension (D.equivFin d)

end ProjectiveAlgebraic

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveIndiscernibles ProjectiveBlocks Function

/-- A noninjective self-surjection on finite/cofinite codes forces algebraic
closure in its graph language to be nondegenerate, provided the infinite graph
structure has finite type spectra and finite/cofinite unary definable sets. -/
theorem nondegenerateClosure {M : Type*} [Infinite M] (k : ℕ) (f : Codes M k → Codes M k) :
    letI := graphStructure f
    FiniteTypes (graphLanguage k) M → Minimal (graphLanguage k) M →
      Surjective f → ¬ Injective f → ¬ Degenerate (graphLanguage k) M := by
  let := graphStructure f
  intro fin min surj collision deg
  obtain ⟨c,d,_,s,eq,block⟩ := symmetricBlockModel fin min deg
  let := s
  exact collision (obstructionOfBlockModel c d k f block eq surj)

end ProjectiveTransfer

@[expose] public section

namespace ProjectiveSupports

open ProjectiveAlgebraic ProjectiveTransfer ProjectiveIndiscernibles Set Function

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- Necessity in the finite point-support permutation interpretation. The
hypothesis concerns a supported noninjective surjection on a power of the
actual internal power set. Its graph supplies a supported nondegenerate,
locally finite, locally homogeneous pregeometry on the atoms. -/
theorem supportedNecessity (am : Amorphous G) {k : ℕ} (F : (Fin k → Power G) → (Fin k → Power G))
    (hs : ∃ E, SupportedPowerMap G F E) (surj : Surjective F) (collides : ¬ Injective F) :
    ∃ cl : Set A → Set A, Geometry G cl := by
  classical
  let := am.1
  obtain ⟨E,hE⟩ := hs
  let e := powersEquiv G am k
  let f (x : Codes A k) := e.symm (F (e x))
  have support : SupportedCodeMap G f E := supports_conjugate G am F E hE
  have onto : Surjective f := e.symm.surjective.comp (surj.comp e.surjective)
  have collision : ¬ Injective f := by
    intro inj
    apply collides
    intro a b eq
    have h : f (e.symm a) = f (e.symm b) := by simp [f,eq]
    exact e.symm.injective (inj h)
  let := graphStructure f
  have act : SupportedStructure G (graphLanguage k) E := graph_supported G f E support
  obtain ⟨fin,min⟩ := structure_properties G am E act
  obtain ⟨ext,mono,idem,fc,lf,exchange⟩ := pregeometry fin min
  have nondeg := nondegenerateClosure k f fin min onto collision
  unfold Degenerate at nondeg
  push Not at nondeg
  refine ⟨acl (graphLanguage k),⟨E,?_⟩,ext,mono,idem,fc,lf,exchange,nondeg,localHomogeneity fin min⟩
  intro σ hg fix S
  obtain ⟨p,rfl⟩ := act σ hg fix
  exact acl_image fin p S

end ProjectiveSupports

@[expose] public section

namespace ProjectiveSupports

/-- In the finite point-support permutation interpretation, projective type,
dual Dedekind infinity of the internal powerset, and of some or every positive
finite power are equivalent. The two implications construct a supported
pregeometry from the map and a supported map from the pregeometry. -/
theorem projectivePowers {A : Type*} (G : Subgroup (Equiv.Perm A)) (am : Amorphous G) :
    ((∃ cl : Set A → Set A, Geometry G cl) ↔ DuallyInfinitePower G 1) ∧
    ((∃ cl : Set A → Set A, Geometry G cl) ↔ ∃ k > 0, DuallyInfinitePower G k) ∧
    ((∃ cl : Set A → Set A, Geometry G cl) ↔ ∀ k > 0, DuallyInfinitePower G k) := by
  have any {k : ℕ} (h : DuallyInfinitePower G k) : ∃ cl : Set A → Set A, Geometry G cl := by
    obtain ⟨F,supp,surj,collision⟩ := h
    exact supportedNecessity G am F supp surj collision
  have all (h : ∃ cl : Set A → Set A, Geometry G cl) (k : ℕ) (pos : 0 < k) : DuallyInfinitePower G k := by
    obtain ⟨_,geom⟩ := h
    exact allPositivePowers am geom k pos
  exact ⟨⟨fun h => all h 1 Nat.zero_lt_one,any⟩,
    ⟨fun h => ⟨1,Nat.zero_lt_one,all h 1 Nat.zero_lt_one⟩,fun ⟨_,_,h⟩ => any h⟩,
    ⟨all,fun h => any (h 1 Nat.zero_lt_one)⟩⟩

end ProjectiveSupports
