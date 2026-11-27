module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Range

/-!
# Extracting order-indiscernibles

The complete type of every finite tuple of distinct new blocks occurs on the
original sequence of distinct blocks. The finite Ramsey argument and iterative
extension are both carried out in the source structure.
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

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes

variable {d : ℕ} {M : Type*} {κ ι : Type} (L : Language) [L.Structure M]

/-- One tuple lists the finite core followed by all positions in the designated blocks. -/
def marked (core : κ → M) (B : ℚ → Fin d → M) (m : ι → ℚ) : κ ⊕ (ι × Fin d) → M :=
  Sum.elim core fun ij => B (m ij.1) ij.2

/-- Ordered indiscernibility over the named core, stated using increasing embeddings
of the rationals. Parameters can list their blocks in any order. -/
def OrderIndiscernible (core : κ → M) (B : ℚ → Fin d → M) : Prop :=
  ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (f : ℚ → ℚ), StrictMono f →
    tupleType L (marked core B m) = tupleType L (marked core B (f ∘ m))

end ProjectiveIndiscernibles

public section

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

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

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

public section

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
