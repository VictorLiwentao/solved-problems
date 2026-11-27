module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Tactic.Linarith

/-!
# Total indiscernibility of finite algebraic blocks

The protected declaration `ProjectiveIndiscernibles.totalIndiscernibility` removes
the order from an order-indiscernible sequence indexed by the rationals.
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

public section

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

public section

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

public section

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

public section

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
