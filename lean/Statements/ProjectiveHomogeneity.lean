module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Range

/-!
# Algebraic closure in the encoded structure

`ProjectiveAlgebraic.pregeometry` gives the locally finite pregeometry laws.
`ProjectiveAlgebraic.localHomogeneity` proves transitivity over a closed base
and extension of the same closure-preserving permutation to every larger
finite closed set.
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

/-- Finitely many full first-order types at each finite arity. -/
def FiniteTypes (L : Language) (A : Type*) [L.Structure A] : Prop :=
  ∀ (ι : Type) [Finite ι], (typesIn L A ι).Finite

variable {L : Language} {A B ι κ : Type*} [L.Structure A] [L.Structure B]

/-- Restriction/reordering retains equality of complete types. -/
theorem match_subtuple {a : ι → A} {b : ι → B}
    (m : tupleType L a = tupleType L b) (f : κ → ι) : tupleType L (a ∘ f) = tupleType L (b ∘ f) := by
  ext φ
  have h := Set.ext_iff.mp m (φ.relabel f)
  simpa only [tupleType,Set.mem_ofPred_eq,Formula.realize_relabel] using h


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

public section

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

public section

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

public section

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

public section

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

public section

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

public section

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
