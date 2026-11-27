module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Order.RelClasses
public import Mathlib.SetTheory.Cardinal.Finite


/-!
# Internal self-surjections in the pure membership language

The Separation instances in this reference use actual finite Mathlib first-order
formulas. Internal sets and graphs are elements of the displayed model.
-/

@[expose] public section

namespace ProjectiveZF

open FirstOrder FirstOrder.Language

universe u v

/-- The pure language of set theory has membership as its only nonlogical symbol. -/
inductive Predicate : ℕ → Type
  | membership : Predicate 2

def setLanguage : Language where
  Functions _ := Empty
  Relations := Predicate

instance {V : Type u} [Membership V V] : setLanguage.Structure V where
  funMap := fun {_} f => nomatch f
  RelMap := fun {_} r => match r with | .membership => fun v => v 0 ∈ v 1

/-- A variable, or a named set parameter of a schema instance. -/
inductive Atom (V : Type u) (ι : Type v)
  | var : ι → Atom V ι
  | param : V → Atom V ι

variable {V : Type u} {ι : Type v}

def Atom.eval : Atom V ι → (ι → V) → V
  | .var i, v => v i
  | .param a, _ => a

def Atom.term : Atom V ι → setLanguage.Term (V ⊕ ι)
  | .var i => .var (.inr i)
  | .param a => .var (.inl a)

/-- Terms needed in a pure relational language are variables and parameters. -/
def Term (t : (ι → V) → V) : Prop := ∃ a : Atom V ι, ∀ v, a.eval v = t v

theorem termVar (i : ι) : Term (fun v : ι → V => v i) := ⟨.var i,fun _ => rfl⟩

theorem termParam (c : V) : Term (fun _ : ι → V => c) := ⟨.param c,fun _ => rfl⟩

theorem termLift {f : (ι → V) → V} (h : Term f) : Term (fun v : Option ι → V => f (v ∘ some)) := by
  obtain ⟨a,ha⟩ := h
  cases a with
  | var i => exact ⟨.var (some i),fun v => ha (v ∘ some)⟩
  | param b => exact ⟨.param b,fun v => ha (v ∘ some)⟩

theorem termReindex {κ : Type*} {f : (ι → V) → V} (h : Term f) (g : ι → κ) : Term (fun v : κ → V => f (v ∘ g)) := by
  obtain ⟨a,ha⟩ := h
  cases a with
  | var i => exact ⟨.var (g i),fun v => ha (v ∘ g)⟩
  | param b => exact ⟨.param b,fun v => ha (v ∘ g)⟩

variable [Membership V V]

@[simp] theorem Atom.realize_term (a : Atom V ι) (v : ι → V) : a.term.realize (Sum.elim id v) = a.eval v := by cases a <;> rfl

/-- An actual finite Mathlib first-order formula in the pure membership
language defines the predicate. Parameters occur only in the finitely many
free-variable positions used by that formula. -/
def Definable (P : (ι → V) → Prop) : Prop :=
  ∃ φ : setLanguage.Formula (V ⊕ ι), ∀ v, φ.Realize (Sum.elim id v) ↔ P v

theorem defEq {s t : (ι → V) → V} (hs : Term s) (ht : Term t) : Definable (fun v => s v = t v) := by
  obtain ⟨a,ha⟩ := hs
  obtain ⟨b,hb⟩ := ht
  exact ⟨a.term.equal b.term,fun v => by simp [ha,hb]⟩

theorem defMem {s t : (ι → V) → V} (hs : Term s) (ht : Term t) : Definable (fun v => s v ∈ t v) := by
  obtain ⟨a,ha⟩ := hs
  obtain ⟨b,hb⟩ := ht
  let r : setLanguage.Relations 2 := Predicate.membership
  refine ⟨r.formula ![a.term,b.term],fun v => ?_⟩
  rw [Formula.realize_rel]
  change a.term.realize (Sum.elim id v) ∈ b.term.realize (Sum.elim id v) ↔ _
  simp [ha,hb]

theorem defImp {P Q : (ι → V) → Prop} (hP : Definable P) (hQ : Definable Q) : Definable (fun v => P v → Q v) := by
  obtain ⟨p,hp⟩ := hP
  obtain ⟨q,hq⟩ := hQ
  exact ⟨p.imp q,fun v => Formula.realize_imp.trans (imp_congr (hp v) (hq v))⟩

theorem defNot {P : (ι → V) → Prop} (h : Definable P) : Definable (fun v => ¬ P v) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.not,fun v => Formula.realize_not.trans (not_congr (hp v))⟩

theorem defAnd {P Q : (ι → V) → Prop} (p : Definable P) (q : Definable Q) : Definable (fun v => P v ∧ Q v) := by
  obtain ⟨a,ha⟩ := p
  obtain ⟨b,hb⟩ := q
  exact ⟨a ⊓ b,fun v => Formula.realize_inf.trans (and_congr (ha v) (hb v))⟩

theorem defOr {P Q : (ι → V) → Prop} (p : Definable P) (q : Definable Q) : Definable (fun v => P v ∨ Q v) := by
  obtain ⟨a,ha⟩ := p
  obtain ⟨b,hb⟩ := q
  exact ⟨a ⊔ b,fun v => Formula.realize_sup.trans (or_congr (ha v) (hb v))⟩

theorem defIff {P Q : (ι → V) → Prop} (p : Definable P) (q : Definable Q) : Definable (fun v => P v ↔ Q v) := by
  obtain ⟨a,ha⟩ := p
  obtain ⟨b,hb⟩ := q
  exact ⟨a.iff b,fun v => Formula.realize_iff.trans (iff_congr (ha v) (hb v))⟩

theorem defAll {P : (ι → V) → V → Prop}
    (h : Definable (fun v : Option ι → V => P (v ∘ some) (v none))) : Definable (fun v => ∀ a, P v a) := by
  obtain ⟨φ,hφ⟩ := h
  let idx : V ⊕ Option ι → (V ⊕ ι) ⊕ Unit := Sum.elim (Sum.inl ∘ Sum.inl) (fun j => j.elim (.inr ()) (Sum.inl ∘ Sum.inr))
  refine ⟨(φ.relabel idx).iAlls Unit,fun v => ?_⟩
  rw [Formula.realize_iAlls]
  have atVal (u : Unit → V) : (φ.relabel idx).Realize (Sum.elim (Sum.elim id v) u) ↔ P v (u ()) := by
    rw [Formula.realize_relabel]
    have cut : (Sum.elim (Sum.elim id v) u) ∘ idx = Sum.elim id (fun j : Option ι => j.elim (u ()) v) := by
      funext j; rcases j with j|(_|j) <;> rfl
    rw [cut]
    exact hφ _
  exact ⟨fun hu a => (atVal (fun _ => a)).mp (hu _),fun ha u => (atVal u).mpr (ha _)⟩

theorem defEx {P : (ι → V) → V → Prop}
    (h : Definable (fun v : Option ι → V => P (v ∘ some) (v none))) : Definable (fun v => ∃ a, P v a) := by
  obtain ⟨φ,hφ⟩ := defNot (defAll (P := fun v a => ¬P v a) (defNot h))
  exact ⟨φ,fun v => (hφ v).trans (by push Not; rfl)⟩

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open FirstOrder FirstOrder.Language

variable {V ι κ : Type*} [Membership V V]

/-- Substituting projections and set parameters into a definable predicate
preserves pure first-order definability. -/
theorem defSubst {P : (ι → V) → Prop} (h : Definable P) (u : ι → (κ → V) → V) (hu : ∀ i, Term (u i)) :
    Definable (fun v => P (fun i => u i v)) := by
  obtain ⟨φ,hφ⟩ := h
  choose a ha using hu
  let idx : V ⊕ ι → V ⊕ κ := Sum.elim Sum.inl fun i => match a i with | .var j => .inr j | .param b => .inl b
  refine ⟨φ.relabel idx,fun v => ?_⟩
  rw [Formula.realize_relabel]
  have cut : (Sum.elim id v) ∘ idx = Sum.elim id (fun i => u i v) := by
    funext j
    rcases j with j|i
    · rfl
    · have eq := ha i v
      rcases hj : a i with j|c <;> simpa [idx,hj,Atom.eval] using eq
  rw [cut]
  exact hφ _

/-- Pure first-order definability with one or two displayed free arguments. -/
def Unary (P : V → Prop) := Definable (fun v : Unit → V => P (v ()))
def Binary (P : V → V → Prop) := Definable (fun v : Bool → V => P (v false) (v true))

theorem defUnary {P : V → Prop} (h : Unary P) {s : (ι → V) → V} (hs : Term s) :
    Definable (fun v => P (s v)) := defSubst h (fun _ => s) (fun _ => hs)

theorem defBinary {P : V → V → Prop} (h : Binary P) {s t : (ι → V) → V} (hs : Term s) (ht : Term t) :
    Definable (fun v => P (s v) (t v)) :=
  defSubst h (fun b => if b then t else s) (fun b => by cases b <;> assumption)

/-- Membership-language descriptions of singletons, unordered pairs, and
Kuratowski ordered pairs, with the represented set as the last argument. -/
def IsSingle (a z : V) : Prop := ∀ w, w ∈ z ↔ w = a
def IsDouble (a b z : V) : Prop := ∀ w, w ∈ z ↔ w = a ∨ w = b
def IsPair (a b z : V) : Prop := ∀ w, w ∈ z ↔ IsSingle a w ∨ IsDouble a b w

def Edge (f x y : V) : Prop := ∃ p, IsPair x y p ∧ p ∈ f

/-- Discharge the syntactic obligations left by a fixed first-order formula. -/
macro "zf_terms" : tactic => `(tactic| first | assumption | exact termVar _ | exact termParam _ | (simp only [Function.comp_assoc]; apply termReindex; assumption) | solve_by_elim (maxDepth := 6) only [*, termLift])

macro "zf_logic" : tactic => `(tactic| repeat' first
  | assumption
  | apply defIff | apply defAnd | apply defOr | apply defNot | apply defEx | apply defAll | apply defImp
  | apply defMem | apply defEq | zf_terms)

theorem defSingle {s t : (ι → V) → V} (hs : Term s) (ht : Term t) : Definable (fun v => IsSingle (s v) (t v)) := by
  unfold IsSingle
  zf_logic

theorem defDouble {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => IsDouble (s v) (t v) (u v)) := by unfold IsDouble; zf_logic

theorem defPair {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => IsPair (s v) (t v) (u v)) := by
  unfold IsPair
  apply defAll
  apply defIff
  · apply defMem <;> zf_terms
  · apply defOr
    · apply defSingle <;> zf_terms
    · apply defDouble <;> zf_terms

theorem defEdge {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => Edge (s v) (t v) (u v)) := by
  unfold Edge
  apply defEx
  apply defAnd
  · apply defPair <;> zf_terms
  · apply defMem <;> zf_terms

/-- A set of ordered pairs qualifying as a function from `X` into `Y`.
The last condition gives uniqueness for the entire range of the graph. -/
def IsMap (X Y f : V) : Prop :=
  (∀ p, p ∈ f → ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧ IsPair x y p) ∧
  (∀ x, x ∈ X → ∃ y, Edge f x y) ∧
  (∀ x y z, Edge f x y → Edge f x z → y = z)

macro "zf_map_formula" : tactic => `(tactic| repeat' first
  | assumption
  | apply defPair | apply defEdge
  | apply defIff | apply defAnd | apply defOr | apply defNot | apply defEx | apply defAll | apply defImp
  | apply defMem | apply defEq | zf_terms)

theorem defMap {s t u : (ι → V) → V} (hs : Term s) (ht : Term t) (hu : Term u) :
    Definable (fun v => IsMap (s v) (t v) (u v)) := by unfold IsMap; zf_map_formula

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open Set Function

/-- The fragment of pure ZF used below: Extensionality, Pairing, Union,
Power Set, and Separation for actual membership-language formulas with set
parameters. No well-foundedness or standardness of the model is imposed. -/
structure Core (V : Type*) [Membership V V] : Prop where
  ext : ∀ a b : V, (∀ x, x ∈ a ↔ x ∈ b) → a = b
  pairing : ∀ a b : V, ∃ p : V, IsDouble a b p
  union : ∀ a : V, ∃ u : V, ∀ x, x ∈ u ↔ ∃ y, y ∈ a ∧ x ∈ y
  power : ∀ a : V, ∃ p : V, ∀ x, x ∈ p ↔ ∀ y, y ∈ x → y ∈ a
  separation : ∀ (a : V) (P : V → Prop), Unary P → ∃ b : V, ∀ x, x ∈ b ↔ x ∈ a ∧ P x

variable {V : Type*} [Membership V V] (M : Core V)

/-- The external extent of an internal set. -/
def elts (a : V) : Set V := {x | x ∈ a}

noncomputable def double (a b : V) : V := (M.pairing a b).choose
noncomputable def single (a : V) : V := double M a a
noncomputable def ordered (a b : V) : V := double M (single M a) (double M a b)
noncomputable def power (a : V) : V := (M.power a).choose
noncomputable def both (a b : V) : V := (M.union (double M a b)).choose

@[simp] theorem mem_double {a b t : V} : t ∈ double M a b ↔ t = a ∨ t = b := (M.pairing a b).choose_spec t
@[simp] theorem mem_single {a t : V} : t ∈ single M a ↔ t = a := by simp [single]
@[simp] theorem mem_power {a t : V} : t ∈ power M a ↔ ∀ x, x ∈ t → x ∈ a := (M.power a).choose_spec t
@[simp] theorem mem_both {a b t : V} : t ∈ both M a b ↔ t ∈ a ∨ t ∈ b := by
  rw [both,(M.union (double M a b)).choose_spec]; simp [or_and_right,exists_or]

@[simp] theorem single_iff (a z : V) : IsSingle a z ↔ z = single M a := by
  refine ⟨fun h => M.ext _ _ (fun x => (h x).trans (mem_single M).symm),?_⟩
  rintro rfl x
  exact mem_single M

@[simp] theorem double_iff (a b z : V) : IsDouble a b z ↔ z = double M a b := by
  refine ⟨fun h => M.ext _ _ (fun x => (h x).trans (mem_double M).symm),?_⟩
  rintro rfl x
  exact mem_double M

@[simp] theorem pair_iff (a b z : V) : IsPair a b z ↔ z = ordered M a b := by
  refine ⟨fun h => M.ext _ _ (fun x => ?_),?_⟩
  · simpa only [ordered,mem_double,single_iff M,double_iff M] using h x
  · rintro rfl x
    simp [ordered,single_iff M,double_iff M]

@[simp] theorem edge_iff (f a b : V) : Edge f a b ↔ ordered M a b ∈ f := by simp [Edge,pair_iff M]

private theorem ext_double (a b : V) : elts (double M a b) = {a,b} := by ext x; exact mem_double M
private theorem ext_single (a : V) : elts (single M a) = {a} := by ext x; exact mem_single M

/-- Equality of Kuratowski ordered pairs implies equality of both entries in
any extensional membership structure with pairing. -/
theorem ordered_inj {a b c d : V} (eq : ordered M a b = ordered M c d) : a = c ∧ b = d := by
  have family := congrArg (fun z => elts '' elts z) eq
  simp only [ordered,ext_double,Set.image_insert_eq,Set.image_singleton,ext_single] at family
  have common (a b : V) : ∀ W ∈ ({{a},{a,b}} : Set (Set V)), a ∈ W := by simp
  have cIn : {c} ∈ ({{a},{a,b}} : Set (Set V)) := by rw [family]; simp
  have ac : a = c := Set.mem_singleton_iff.mp (common a b {c} cIn)
  subst c
  have union (a b x : V) : (∃ W ∈ ({{a},{a,b}} : Set (Set V)), x ∈ W) ↔ x = a ∨ x = b := by simp
  have same (x : V) : x = a ∨ x = b ↔ x = a ∨ x = d := by rw [← union a b x,family,union]
  have hb := (same b).mp (Or.inr rfl)
  have hd := (same d).mpr (Or.inr rfl)
  exact ⟨rfl,by rcases hb with h|h <;> rcases hd with k|k <;> grind⟩

include M in
theorem pair_coords {p x y a b : V} (h : IsPair x y p) (h' : IsPair a b p) : x = a ∧ y = b :=
  ordered_inj M (((pair_iff M _ _ _).mp h).symm.trans ((pair_iff M _ _ _).mp h'))

/-- A common set bounding every possible internal ordered pair from `X × Y`. -/
noncomputable def pairBound (X Y : V) := power M (power M (both M X Y))

theorem pair_mem_bound {X Y x y : V} (hx : x ∈ X) (hy : y ∈ Y) : ordered M x y ∈ pairBound M X Y := by
  rw [pairBound,mem_power]
  intro z hz
  rcases (mem_double M).mp hz with rfl|rfl
  · rw [mem_power]
    intro t ht
    exact (mem_single M).mp ht ▸ (mem_both M).mpr (Or.inl hx)
  · rw [mem_power]
    intro t ht
    rcases (mem_double M).mp ht with rfl|rfl
    · exact (mem_both M).mpr (Or.inl hx)
    · exact (mem_both M).mpr (Or.inr hy)

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- The actual elements, relative to the membership relation of the model. -/
abbrev El (s : V) := {a : V // a ∈ s}

include M

theorem edge_typed {X Y f a b : V} (hf : IsMap X Y f) (he : Edge f a b) : a ∈ X ∧ b ∈ Y := by
  obtain ⟨p,pair,mem⟩ := he
  obtain ⟨x,hx,y,hy,rep⟩ := hf.1 _ mem
  obtain ⟨rfl,rfl⟩ := pair_coords M pair rep
  exact ⟨hx,hy⟩

theorem graph_ext {X Y f g : V} (hf : IsMap X Y f) (hg : IsMap X Y g)
    (same : ∀ a ∈ X, ∀ b, Edge f a b ↔ Edge g a b) : f = g := by
  apply M.ext
  have sub {s t : V} (hs : IsMap X Y s) (h : ∀ a ∈ X, ∀ b, Edge s a b → Edge t a b) : ∀p, p ∈ s → p ∈ t := by
    intro p hp
    obtain ⟨a,ha,b,_,pair⟩ := hs.1 _ hp
    obtain rfl := (pair_iff M _ _ _).mp pair
    exact (edge_iff M _ _ _).mp (h a ha b ((edge_iff M _ _ _).mpr hp))
  exact fun p => ⟨sub hf (fun a ha b => (same a ha b).mp) p,sub hg (fun a ha b => (same a ha b).mpr) p⟩

/-- Every definable binary relation gives an internal set of ordered pairs
on prescribed domains, by a single instance of Separation. -/
theorem graphSeparation (X Y : V) (R : V → V → Prop) (h : Binary R) :
    ∃ f : V, (∀ p, p ∈ f ↔ ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧ R x y ∧ IsPair x y p) ∧
      ∀ x y, Edge f x y ↔ x ∈ X ∧ y ∈ Y ∧ R x y := by
  let P (p : V) := ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧ R x y ∧ IsPair x y p
  have d : Unary P := by
    unfold Unary P
    repeat' first | apply defBinary h | apply defPair | apply defMem | apply defAnd | apply defEx | zf_terms
  obtain ⟨f,rep⟩ := M.separation (pairBound M X Y) P d
  have mem (p : V) : p ∈ f ↔ P p := by
    rw [rep]
    refine ⟨And.right,fun hp => ⟨?_,hp⟩⟩
    obtain ⟨x,hx,y,hy,_,pair⟩ := hp
    exact (pair_iff M _ _ _).mp pair ▸ pair_mem_bound M hx hy
  refine ⟨f,mem,?_⟩
  intro x y
  rw [edge_iff M,mem]
  constructor
  · rintro ⟨a,ha,b,hb,r,p⟩
    obtain ⟨rfl,rfl⟩ := ordered_inj M ((pair_iff M _ _ _).mp p)
    exact ⟨ha,hb,r⟩
  · rintro ⟨hx,hy,r⟩
    exact ⟨x,hx,y,hy,r,(pair_iff M _ _ _).mpr rfl⟩

/-- A definable total functional relation has an internal function graph.
The graph is supplied by Separation; there is no selection of internal
preimages using the ambient axiom of choice. -/
theorem mapFrom (X Y : V) (R : V → V → Prop) (h : Binary R)
    (total : ∀ x ∈ X, ∃ y, y ∈ Y ∧ R x y)
    (unique : ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Y, R x y → R x z → y = z) :
    ∃ f : V, IsMap X Y f ∧ ∀ x y, Edge f x y ↔ x ∈ X ∧ y ∈ Y ∧ R x y := by
  obtain ⟨f,mem,edge⟩ := graphSeparation M X Y R h
  refine ⟨f,⟨?_,?_,?_⟩,edge⟩
  · intro p hp
    obtain ⟨a,ha,b,hb,_,rep⟩ := (mem p).mp hp
    exact ⟨a,ha,b,hb,rep⟩
  · intro a ha
    obtain ⟨b,hb,rel⟩ := total a ha
    exact ⟨b,(edge a b).mpr ⟨ha,hb,rel⟩⟩
  · intro x y z hy hz
    obtain ⟨hx,hy,ry⟩ := (edge x y).mp hy
    obtain ⟨_,hz,rz⟩ := (edge x z).mp hz
    exact unique x hx y hy z hz ry rz

/-- The internal exponential contains precisely the function graphs that are
sets of the model. It is obtained by separating them from a power set. -/
noncomputable def exponential (X I : V) : V :=
  (M.separation (power M (pairBound M I X)) (IsMap I X) (defMap (termParam _) (termParam _) (termVar ()))).choose

@[simp] theorem mem_exponential {X I f : V} : f ∈ exponential M X I ↔ IsMap I X f := by
  have rule := (M.separation (power M (pairBound M I X)) (IsMap I X)
    (defMap (termParam _) (termParam _) (termVar ()))).choose_spec f
  change f ∈ exponential M X I ↔ _ at rule
  rw [rule]
  refine ⟨And.right,fun h => ⟨(mem_power M).mpr ?_,h⟩⟩
  intro t ht
  obtain ⟨a,ha,b,hb,rep⟩ := h.1 _ ht
  exact (pair_iff M _ _ _).mp rep ▸ pair_mem_bound M ha hb

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

include M

/-- The members of any externally finite set of model elements can be collected
into a single internal set using Pairing, Union and an empty Separation. -/
theorem representsFinite (seed : V) {S : Set V} (finite : S.Finite) : ∃ t : V, elts t = S := by
  classical
  induction S,finite using Set.Finite.induction_on with
  | empty =>
    obtain ⟨t,ht⟩ := M.separation seed (fun x => x ≠ x) (defNot (defEq (termVar ()) (termVar ())))
    refine ⟨t,Set.ext fun x => ?_⟩
    change x ∈ t ↔ False
    simp [ht]
  | @insert a S _ _ ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨both M (single M a) t,Set.ext fun x => ?_⟩
    change x ∈ both _ _ _ ↔ x = a ∨ x ∈ S
    rw [mem_both,mem_single,← ht]
    rfl

/-- The model contains the graph of any function on an externally finite set
of elements. This is a finite construction even when the function originally
appears as an external parameter. -/
theorem finiteGraph {X Y : V} [Finite (El X)] (f : El X → El Y) :
    ∃ g : V, IsMap X Y g ∧ ∀ (x : El X) (y : V), Edge g x.val y ↔ y = (f x).val := by
  let pair (x : El X) := ordered M x.val (f x).val
  obtain ⟨g,rep⟩ := representsFinite M X (Set.finite_range pair)
  have mem (p : V) : p ∈ g ↔ ∃ x : El X, ordered M x.val (f x).val = p := Set.ext_iff.mp rep p
  have edge (a b : V) : Edge g a b ↔ ∃ x : El X, x.val = a ∧ (f x).val = b := by
    rw [edge_iff M,mem]
    exact exists_congr fun x => ⟨ordered_inj M,fun ⟨ha,hb⟩ => by rw [ha,hb]⟩
  refine ⟨g,⟨?_,?_,?_⟩,?_⟩
  · intro p hp
    obtain ⟨x,h⟩ := (mem p).mp hp
    exact ⟨x.val,x.property,(f x).val,(f x).property,(pair_iff M _ _ _).mpr h.symm⟩
  · intro a ha
    let x : El X := ⟨a,ha⟩
    exact ⟨(f x).val,(edge _ _).mpr ⟨x,rfl,rfl⟩⟩
  · intro a b c h k
    obtain ⟨x,hx,hb⟩ := (edge _ _).mp h
    obtain ⟨y,hy,hc⟩ := (edge _ _).mp k
    obtain rfl : x = y := Subtype.ext (hx.trans hy.symm)
    exact hb.symm.trans hc
  · intro a b
    rw [edge]
    refine ⟨fun ⟨x,h,h'⟩ => ?_,fun h => ⟨a,rfl,h.symm⟩⟩
    obtain rfl : x = a := Subtype.ext h
    exact h'.symm

/-- The internal first-order assertion that the displayed sets are in bijection. -/
def Equinumerous (X Y : V) : Prop := ∃ f : V, IsMap X Y f ∧
  (∀ y, y ∈ Y → ∃ x, x ∈ X ∧ Edge f x y) ∧ (∀ x z y, Edge f x y → Edge f z y → x = z)

omit M in
theorem defEquinumerous {ι : Type*} {s t : (ι → V) → V} (hs : Term s) (ht : Term t) :
    Definable (fun v => Equinumerous (s v) (t v)) := by
  unfold Equinumerous
  repeat' first | apply defMap | apply defEdge | apply defAnd | apply defImp | apply defAll | apply defEx
                | apply defEq | apply defMem | zf_terms

/-- Any internal bijection induces a bijection on the external elements.
Conversely, external bijections on finite domains have internal graphs. -/
theorem equiv_of_equinumerous {X Y : V} (h : Equinumerous X Y) : Nonempty (El X ≃ El Y) := by
  classical
  obtain ⟨g,map,onto,unique⟩ := h
  choose value edge using fun x : El X => map.2.1 x.val x.property
  let f (x : El X) : El Y := ⟨value x,(edge_typed M map (edge x)).2⟩
  refine ⟨Equiv.ofBijective f ⟨?_,?_⟩⟩
  · intro a b eq
    apply Subtype.ext
    have cut : value a = value b := congrArg Subtype.val eq
    exact unique _ _ _ (edge a) (cut ▸ edge b)
  · intro y
    obtain ⟨x,hx,hy⟩ := onto y.val y.property
    exact ⟨⟨x,hx⟩,Subtype.ext (map.2.2 _ _ _ (edge _) hy)⟩

theorem equinumerous_of_finite {X Y : V} [Finite (El X)] (e : El X ≃ El Y) : Equinumerous X Y := by
  obtain ⟨g,map,edge⟩ := finiteGraph M e
  refine ⟨g,map,?_,?_⟩
  · intro y hy
    let t : El Y := ⟨y,hy⟩
    exact ⟨(e.symm t).val,(e.symm t).property,(edge _ _).mpr (congrArg Subtype.val (e.apply_symm_apply t).symm)⟩
  · intro a b y ha hb
    let x : El X := ⟨a,(edge_typed M map ha).1⟩
    let z : El X := ⟨b,(edge_typed M map hb).1⟩
    have cut : (e x).val = (e z).val := ((edge x y).mp ha).symm.trans ((edge z y).mp hb)
    exact congrArg Subtype.val (e.injective (Subtype.ext cut))

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- A first-order parity test that needs no standardness assumption on the
ambient universe or on its natural numbers. -/
def Balanced (X : V) : Prop := ∃ U W : V, (∀ x, x ∈ X ↔ x ∈ U ∨ x ∈ W) ∧
  (∀ x, x ∈ U → x ∉ W) ∧ Equinumerous U W

theorem defBalanced {ι : Type*} {s : (ι → V) → V} (hs : Term s) : Definable (fun v => Balanced (s v)) := by
  unfold Balanced
  repeat' first | apply defEquinumerous | apply defIff | apply defAnd | apply defOr | apply defEx | apply defAll
                | apply defNot | apply defImp | apply defMem | zf_terms

private noncomputable def partEquiv {X U W : V} (cover : ∀ x : V, x ∈ X ↔ x ∈ U ∨ x ∈ W) (disj : ∀ x, x ∈ U → x ∉ W) :
    open Classical in El X ≃ (El U ⊕ El W) := by
  classical
  refine {
    toFun := fun x => if h : x.val ∈ U then .inl ⟨_,h⟩ else .inr ⟨_,((cover _).mp x.property).resolve_left h⟩
    invFun := Sum.elim (fun u => ⟨u.val,(cover _).mpr (Or.inl u.property)⟩) (fun w => ⟨w.val,(cover _).mpr (Or.inr w.property)⟩)
    left_inv := ?_
    right_inv := ?_ }
  · intro x; by_cases h : x.val ∈ U <;> simp [h]
  · rintro (x|x)
    · simp [x.property]
    · have outside : x.val ∉ U := fun h => disj _ h x.property
      simp [outside]

private noncomputable def numbered {X : V} {n : ℕ} (w : Fin n → V) (h : elts X = range w) (inj : Injective w) :
    Fin n ≃ El X := by
  let v (i : Fin n) : El X := ⟨w i,h.superset (mem_range_self i)⟩
  apply Equiv.ofBijective v
  refine ⟨fun i j h' => inj (congrArg Subtype.val h'),?_⟩
  intro x
  obtain ⟨i,hi⟩ := h.subset x.property
  exact ⟨i,Subtype.ext hi⟩

include M

/-- On every externally finite set, internal equinumerous halves exist exactly
when the actual number of members is even. -/
theorem balanced_iff_even (X : V) [Finite (El X)] : Balanced X ↔ Even (Nat.card (El X)) := by
  classical
  constructor
  · rintro ⟨U,W,cover,disj,eq⟩
    obtain ⟨e⟩ := equiv_of_equinumerous M eq
    let cut := partEquiv cover disj
    let := Finite.of_equiv (El X) cut
    let := Finite.of_injective (Sum.inl : El U → El U ⊕ El W) Sum.inl_injective
    let := Finite.of_injective (Sum.inr : El W → El U ⊕ El W) Sum.inr_injective
    refine ⟨Nat.card (El U),?_⟩
    rw [Nat.card_congr cut,Nat.card_sum,← Nat.card_congr e]
  · rintro ⟨m,card⟩
    let := Fintype.ofFinite (El X)
    let e := Fintype.equivOfCardEq (α := Fin m ⊕ Fin m) (β := El X) (by simpa [Nat.card_eq_fintype_card] using card.symm)
    let l (i : Fin m) := (e (.inl i)).val
    let r (i : Fin m) := (e (.inr i)).val
    obtain ⟨U,hU⟩ := representsFinite M X (Set.finite_range l)
    obtain ⟨W,hW⟩ := representsFinite M X (Set.finite_range r)
    have L := numbered l hU (Subtype.val_injective.comp (e.injective.comp Sum.inl_injective))
    have R := numbered r hW (Subtype.val_injective.comp (e.injective.comp Sum.inr_injective))
    let := Finite.of_equiv (Fin m) L
    refine ⟨U,W,?_,?_,equinumerous_of_finite M (L.symm.trans R)⟩
    · intro x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := e.surjective (⟨x,hx⟩ : El X)
        rcases i with i|i
        · exact Or.inl (hU.superset ⟨i,congrArg Subtype.val hi⟩)
        · exact Or.inr (hW.superset ⟨i,congrArg Subtype.val hi⟩)
      · rintro (hu|hw)
        · obtain ⟨i,rfl⟩ := hU.subset hu
          exact (e (.inl i)).property
        · obtain ⟨i,rfl⟩ := hW.subset hw
          exact (e (.inr i)).property
    · intro x hu hw
      obtain ⟨i,hi⟩ := hU.subset hu
      obtain ⟨j,hj⟩ := hW.subset hw
      exact Sum.inl_ne_inr (e.injective (Subtype.ext (hi.trans hj.symm)))

end ProjectiveZF

public section

namespace ProjectiveZF

open Set Function

/-- If infinitely many elements of a linear order have finitely many strict
predecessors, every natural number occurs as one of those predecessor counts. -/
theorem ranksAttained {B : Type*} [LinearOrder B] (large : {b : B | (Iio b).Finite}.Infinite) (n : ℕ) :
    ∃ b : B, (Iio b).Finite ∧ (Iio b).ncard = n := by
  classical
  obtain ⟨T,sub,num⟩ := large.exists_subset_card_eq (n+1)
  have nonempty : T.Nonempty := Finset.card_pos.mp (num ▸ Nat.succ_pos n)
  let a := T.max' nonempty
  have finite : (Iio a).Finite := sub (T.max'_mem nonempty)
  have bounded : (Iic a).Finite := (finite.insert a).subset (by intro x h; rcases le_iff_lt_or_eq.mp h with h|h; exact Set.mem_insert_of_mem _ h; exact Set.mem_insert_iff.mpr (Or.inl h))
  let D := bounded.toFinset
  have cap : T ⊆ D := fun x hx => bounded.mem_toFinset.mpr (T.le_max' _ hx)
  have size := Finset.card_le_card cap
  rw [num] at size
  have enough : n < D.card := size
  let e := D.orderIsoOfFin (k := D.card) rfl
  let i : Fin D.card := ⟨n,enough⟩
  let b := (e i).val
  let v (j : Fin n) := (e ⟨j.val,j.isLt.trans enough⟩).val
  have inj : Injective v := fun j t eq => Fin.ext (congrArg (Fin.val : Fin D.card → ℕ) (e.injective (Subtype.ext eq)))
  have eq : Set.range v = Iio b := by
    ext z
    constructor
    · rintro ⟨j,rfl⟩
      exact (e.lt_iff_lt).mpr (show (⟨j.val,j.isLt.trans enough⟩ : Fin D.card) < i from j.isLt)
    · intro h
      have ba : b ≤ a := bounded.mem_toFinset.mp (e i).property
      let zD : D := ⟨z,bounded.mem_toFinset.mpr (le_trans (le_of_lt h) ba)⟩
      have before : e.symm zD < i := (e.lt_iff_lt).mp (by simpa [zD] using (show zD < e i from h))
      refine ⟨⟨(e.symm zD).val,before⟩,?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply zD)
  refine ⟨b,eq ▸ Set.finite_range v,?_⟩
  rw [← eq,Set.ncard_range_of_injective inj,Nat.card_fin]

/-- Any predicate that tests parity correctly on the finite strict initial
segments separates two infinite subsets when such segments have unbounded size. -/
theorem rankParitySplits {B : Type*} [LinearOrder B] (large : {b : B | (Iio b).Finite}.Infinite)
    (P : B → Prop) (parity : ∀ b, (Iio b).Finite → (P b ↔ Even (Iio b).ncard)) :
    {b | P b}.Infinite ∧ {b | ¬P b}.Infinite := by
  classical
  choose b small rank using ranksAttained large
  have inj : Injective b := fun i j h => (rank i).symm.trans (h ▸ rank j)
  constructor
  · apply (Set.infinite_range_of_injective (f := fun j : ℕ => b (2*j)) (inj.comp (by intro i j h; dsimp at h; omega))).mono
    rintro _ ⟨j,rfl⟩
    exact (parity _ (small _)).mpr (by rw [rank]; exact even_two_mul j)
  · apply (Set.infinite_range_of_injective (f := fun j : ℕ => b (2*j+1)) (inj.comp (by intro i j h; dsimp at h; omega))).mono
    rintro _ ⟨j,rfl⟩ h
    have odd := (parity _ (small _)).mp h
    rw [rank] at odd
    exact Nat.not_even_two_mul_add_one _ odd

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- Every internally represented subset of `X` is externally finite or
cofinite. This is the finite/cofinite clause for omega-standard models. -/
def SmallSubsets (X : V) : Prop := ∀ t : V,
  {x : El X | x.val ∈ t}.Finite ∨ {x : El X | x.val ∉ t}.Finite

include M in
theorem small_definable {X : V} (small : SmallSubsets X) {P : V → Prop} (h : Unary P) :
    {x : El X | P x.val}.Finite ∨ {x : El X | ¬P x.val}.Finite := by
  obtain ⟨z,hz⟩ := M.separation X P h
  have eq (x : El X) : (x.val ∈ z) = P x.val := propext <| (hz x.val).trans (and_iff_right x.property)
  simpa only [eq] using small z

/-- Finitely many predecessors of even size can be recognized by a pure
first-order formula with a finite parameter list. -/
def EvenRay (X : V) (R : V → V → Prop) (x : V) : Prop :=
  ∃ T : V, (∀ a, a ∈ T ↔ a ∈ X ∧ R a x) ∧ Balanced T

theorem defEvenRay (X : V) (R : V → V → Prop) (dr : Binary R) : Unary (EvenRay X R) := by
  unfold Unary EvenRay
  repeat' first | apply defBinary dr | apply defBalanced | apply defIff | apply defEx | apply defAll | apply defAnd
                | apply defMem | zf_terms

private def rayEquiv {X T : V} [LinearOrder (El X)] {R : V → V → Prop} (ord : ∀ a b : El X, R a.val b.val ↔ a < b)
    (x : El X) (rep : ∀ a, a ∈ T ↔ a ∈ X ∧ R a x.val) : El T ≃ (Iio x : Set (El X)) where
  toFun t := ⟨⟨t.val,((rep _).mp t.property).1⟩,(ord _ x).mp ((rep _).mp t.property).2⟩
  invFun t := ⟨t.val.val,(rep _).mpr ⟨t.val.property,(ord _ x).mpr t.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

include M

theorem rayParity {X : V} [LinearOrder (El X)] (R : V → V → Prop) (dr : Binary R)
    (ord : ∀ a b : El X, R a.val b.val ↔ a < b) (x : El X) (finite : (Iio x).Finite) :
    EvenRay X R x.val ↔ Even (Iio x).ncard := by
  have cast (T : V) (rep : ∀ a, a ∈ T ↔ a ∈ X ∧ R a x.val) : Balanced T ↔ Even (Iio x).ncard := by
    let e := rayEquiv ord x rep
    let := finite.to_subtype
    let := Finite.of_equiv (Iio x : Set (El X)) e.symm
    rw [balanced_iff_even M,Nat.card_congr e,Nat.card_coe_set_eq]
  refine ⟨fun ⟨T,h,bal⟩ => (cast T h).mp bal,fun even => ?_⟩
  obtain ⟨T,rep⟩ := M.separation X (fun a => R a x.val) (defBinary dr (termVar ()) (termParam _))
  exact ⟨T,rep,(cast T rep).mpr even⟩

private theorem finite_lower {X : V} [LinearOrder (El X)] (small : SmallSubsets X) (R : V → V → Prop) (dr : Binary R)
    (ord : ∀ a b : El X, R a.val b.val ↔ a < b) : {x : El X | (Iio x).Finite}.Finite := by
  by_contra large
  obtain ⟨ev,odd⟩ := rankParitySplits large (fun x => EvenRay X R x.val) (rayParity M R dr ord)
  exact (small_definable M small (defEvenRay X R dr)).elim ev odd

/-- A set whose internal subsets are all externally finite or cofinite cannot
be both externally infinite and internally linearly ordered. The order here
may be any relation definable in the pure membership language. -/
theorem finiteOfDefinableOrder (X : V) [LinearOrder (El X)] (small : SmallSubsets X) (R : V → V → Prop) (dr : Binary R)
    (ord : ∀ a b : El X, R a.val b.val ↔ a < b) : Finite (El X) := by
  have low := finite_lower M small R dr ord
  have high : {x : El X | (Ioi x).Finite}.Finite := by
    let : LinearOrder (El X) := inferInstanceAs (LinearOrder (El X)ᵒᵈ)
    exact finite_lower M small (fun a b => R b a) (defBinary dr (termVar true) (termVar false)) (fun a b => ord b a)
  apply Set.finite_univ_iff.mp
  apply (low.union high).subset
  intro b _
  have sides := small_definable M small (P := fun a => R a b.val) (defBinary dr (termVar ()) (termParam _))
  have cut (a : El X) : R a.val b.val = (a < b) := propext (ord a b)
  simp only [cut] at sides
  exact sides.imp_right (fun h => h.subset fun _ hx => lt_asymm hx)

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V]

/-- A designated internal omega consists exactly of the standard von Neumann
numerals, and each numeral contains the earlier ones. No global transitivity
or well-foundedness of the membership structure is required. -/
structure StandardOmega (ω : V) where
  numeral : ℕ ↪ V
  members : ∀ z, z ∈ ω ↔ ∃ n, numeral n = z
  earlier : ∀ (n : ℕ) (z : V), z ∈ numeral n ↔ ∃ j : Fin n, numeral j.val = z

/-- The membership-language definition of having finite cardinality. -/
def FiniteIn (ω X : V) : Prop := ∃ n, n ∈ ω ∧ Equinumerous n X

/-- The original internal definition of amorphousness: infinite, and every
internal subset is finite or has a finite relative complement. -/
def AmorphousIn (ω X : V) : Prop := ¬ FiniteIn ω X ∧
  ∀ T, (∀ a, a ∈ T → a ∈ X) → FiniteIn ω T ∨
    ∃ U, (∀ a, a ∈ U ↔ a ∈ X ∧ a ∉ T) ∧ FiniteIn ω U

theorem defFiniteIn {ι : Type*} {o s : (ι → V) → V} (ho : Term o) (hs : Term s) :
    Definable (fun v => FiniteIn (o v) (s v)) := by
  unfold FiniteIn
  repeat' first | apply defEquinumerous | apply defEx | apply defAnd | apply defMem | zf_terms

theorem defAmorphousIn {ι : Type*} {o s : (ι → V) → V} (ho : Term o) (hs : Term s) :
    Definable (fun v => AmorphousIn (o v) (s v)) := by
  unfold AmorphousIn
  repeat' first | apply defFiniteIn | apply defIff | apply defAnd | apply defOr | apply defNot | apply defAll
                | apply defEx | apply defImp | apply defMem | zf_terms

noncomputable def StandardOmega.enumerate {ω : V} (std : StandardOmega ω) (n : ℕ) : Fin n ≃ El (std.numeral n) := by
  let f (i : Fin n) : El (std.numeral n) := ⟨_,(std.earlier n _).mpr ⟨i,rfl⟩⟩
  apply Equiv.ofBijective f
  refine ⟨fun a b eq => Fin.ext (std.numeral.injective (congrArg Subtype.val eq)),?_⟩
  intro x
  obtain ⟨i,h⟩ := (std.earlier n x.val).mp x.property
  exact ⟨i,Subtype.ext h⟩

variable (M : Core V)
include M

/-- In an omega-standard membership model, internal finiteness is equivalent
to external finiteness of the set of members. -/
theorem finiteIn_iff {ω : V} (std : StandardOmega ω) (X : V) : FiniteIn ω X ↔ Finite (El X) := by
  classical
  constructor
  · rintro ⟨n,mem,eq⟩
    obtain ⟨k,rfl⟩ := (std.members n).mp mem
    obtain ⟨e⟩ := equiv_of_equinumerous M eq
    exact Finite.of_equiv (Fin k) ((std.enumerate k).trans e)
  · intro small
    let := small
    let := Fintype.ofFinite (El X)
    let n := Fintype.card (El X)
    let en := std.enumerate n
    let := Finite.of_equiv (Fin n) en
    exact ⟨std.numeral n,(std.members _).mpr ⟨n,rfl⟩,equinumerous_of_finite M (en.symm.trans (Fintype.equivFin (El X)).symm)⟩

private def restrictEquiv {X Y : V} {P : El X → Prop} (sub : ∀ a ∈ Y, a ∈ X)
    (rule : ∀ a : El X, a.val ∈ Y ↔ P a) : El Y ≃ {a : El X // P a} where
  toFun y := ⟨⟨y.val,sub y.val y.property⟩,(rule _).mp y.property⟩
  invFun a := ⟨a.val.val,(rule _).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite/cofinite condition used in the external order argument is an
exact interpretation of the original internal condition in omega-standard models. -/
theorem amorphousIn_iff {ω : V} (std : StandardOmega ω) (X : V) :
    AmorphousIn ω X ↔ Infinite (El X) ∧ SmallSubsets X := by
  classical
  constructor
  · rintro ⟨inf,h⟩
    refine ⟨(not_finite_iff_infinite).mp (fun f => inf ((finiteIn_iff M std X).mpr f)),?_⟩
    intro t
    obtain ⟨T,rep⟩ := M.separation X (fun a => a ∈ t) (defMem (termVar ()) (termParam _))
    have inc (a : V) (ha : a ∈ T) := ((rep a).mp ha).1
    have same (a : El X) : a.val ∈ T ↔ a.val ∈ t := (rep a.val).trans (and_iff_right a.property)
    rcases h T inc with finite | ⟨U,co,finite⟩
    · let := (finiteIn_iff M std _).mp finite
      exact Or.inl (show Finite _ from Finite.of_equiv (El T) (restrictEquiv inc same))
    · let := (finiteIn_iff M std _).mp finite
      let e := restrictEquiv (fun a ha => ((co a).mp ha).1) (fun a : El X => (co a.val).trans ((and_iff_right a.property).trans (not_congr (same a))))
      exact Or.inr (show Finite _ from Finite.of_equiv (El U) e)
  · rintro ⟨inf,small⟩
    refine ⟨fun f => (not_finite_iff_infinite.mpr inf) ((finiteIn_iff M std X).mp f),?_⟩
    intro T sub
    rcases small T with fin|fin
    · let : Finite {a : El X // a.val ∈ T} := fin.to_subtype
      let e := restrictEquiv sub (fun a : El X => Iff.rfl)
      exact Or.inl ((finiteIn_iff M std T).mpr (Finite.of_equiv _ e.symm))
    · obtain ⟨U,co⟩ := M.separation X (fun a => a ∉ T) (defNot (defMem (termVar ()) (termParam _)))
      let : Finite {a : El X // a.val ∉ T} := fin.to_subtype
      let e := restrictEquiv (fun a ha => ((co a).mp ha).1) (fun a : El X => (co a.val).trans (and_iff_right a.property))
      exact Or.inr ⟨U,co,(finiteIn_iff M std U).mpr (Finite.of_equiv _ e.symm)⟩

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- A pure first-order graph relation defining a map between two displayed
carrier sets, including the possibility of a definable class graph. -/
def Represents {X Y : V} (R : V → V → Prop) (f : El X → El Y) : Prop :=
  ∀ a b, R a.val b.val ↔ f a = b

include M

/-- A surjective definable map transfers the finite/cofinite property to its
image. An arbitrary internal subset is pulled back by a Separation formula. -/
theorem small_of_surjection {X Y : V} (small : SmallSubsets X) (r : V → V → Prop) (dr : Binary r)
    (f : El X → El Y) (rep : Represents r f) (surj : Surjective f) : SmallSubsets Y := by
  intro T
  let P (a : V) := ∃ b, b ∈ Y ∧ b ∈ T ∧ r a b
  have d : Unary P := by
    unfold Unary P
    repeat' first | apply defBinary dr | apply defEx | apply defAnd | apply defMem | zf_terms
  have eq (a : El X) : P a.val = ((f a).val ∈ T) := by
    apply propext
    refine ⟨fun ⟨b,by',bt,rel⟩ => ?_,fun h => ⟨(f a).val,(f a).property,h,(rep a (f a)).mpr rfl⟩⟩
    have v := (rep a ⟨b,by'⟩).mp rel
    exact (congrArg Subtype.val v) ▸ bt
  have cut {S : Set (El Y)} (h : (f ⁻¹' S).Finite) : S.Finite := (Set.image_preimage_eq S surj) ▸ h.image f
  have side := small_definable M small d
  simp only [eq] at side
  exact side.imp cut cut

/-- Finite image for maps from the atoms into an internally definable linear
order. This version may be used when only the graph relation has been supplied. -/
theorem finiteDefinableImage {X Y : V} (small : SmallSubsets X) [LinearOrder (El Y)]
    (O : V → V → Prop) (orderForm : Binary O) (ord : ∀ a b : El Y, O a.val b.val ↔ a < b)
    (R : V → V → Prop) (relForm : Binary R) (f : El X → El Y) (rep : Represents R f) : (range f).Finite := by
  classical
  let P (b : V) := ∃ a, a ∈ X ∧ R a b
  have defP : Unary P := by
    unfold Unary P
    repeat' first | apply defBinary relForm | apply defEx | apply defAnd | apply defMem | zf_terms
  obtain ⟨Z,hZ⟩ := M.separation Y P defP
  let g (x : El X) : El Z := ⟨(f x).val,(hZ _).mpr ⟨(f x).property,x.val,x.property,(rep x (f x)).mpr rfl⟩⟩
  let lift (z : El Z) : El Y := ⟨z.val,((hZ _).mp z.property).1⟩
  have inj : Injective lift := fun x y eq => Subtype.ext (congrArg (Subtype.val : El Y → V) eq)
  have onto : Surjective g := by
    intro z
    obtain ⟨_,a,ha,rel⟩ := (hZ z.val).mp z.property
    exact ⟨⟨a,ha⟩,Subtype.ext <| congrArg (Subtype.val : El Y → V) ((rep ⟨a,ha⟩ (lift z)).mp rel)⟩
  have rz : Represents R g := fun a z => (rep a (lift z)).trans (by exact ⟨fun h => Subtype.ext (congrArg (Subtype.val : El Y → V) h),fun h => Subtype.ext (congrArg (Subtype.val : El Z → V) h)⟩)
  have sm := small_of_surjection M small R relForm g rz onto
  let : LinearOrder (El Z) := LinearOrder.lift' lift inj
  let := finiteOfDefinableOrder M Z sm O orderForm (fun a b => ord (lift a) (lift b))
  have factor : lift ∘ g = f := rfl
  rw [← factor]
  exact (Set.finite_range lift).subset (Set.range_comp_subset_range g lift)

/-- The internally represented image of a function. -/
def ImageOf (X f Z : V) : Prop := ∀ y, y ∈ Z ↔ ∃ x, x ∈ X ∧ Edge f x y

/-- For an internally amorphous set in a pure omega-standard membership
model, every internal function into an internal linear order has an internally
finite image. The codomain, its order relation, the function and the image
are all sets of the model. -/
theorem orderedImageFinite {ω : V} (std : StandardOmega ω) {X Y : V} (am : AmorphousIn ω X)
    (order f : V) (lin : IsStrictTotalOrder (El Y) (fun a b => Edge order a.val b.val)) (map : IsMap X Y f) :
    ∃ Z : V, ImageOf X f Z ∧ FiniteIn ω Z := by
  classical
  let rel (a b : El Y) := Edge order a.val b.val
  let : IsStrictTotalOrder (El Y) rel := lin
  let : LinearOrder (El Y) := linearOrderOfSTO rel
  choose value hv using fun a : El X => map.2.1 a.val a.property
  let g (a : El X) : El Y := ⟨value a,(edge_typed M map (hv a)).2⟩
  have rep : Represents (Edge f) g := fun a b => ⟨fun h => Subtype.ext (map.2.2 _ _ _ (hv a) h),fun h => (congrArg Subtype.val h) ▸ hv a⟩
  have edgeF (z : V) : Binary (Edge z) := defEdge (termParam z) (termVar false) (termVar true)
  have small := (amorphousIn_iff M std X).mp am
  have finite := finiteDefinableImage M small.2 (Edge order) (edgeF order) (fun _ _ => Iff.rfl) (Edge f) (edgeF f) g rep
  obtain ⟨Z,hZ⟩ := representsFinite M Y (finite.image Subtype.val)
  have cut (z : V) : z ∈ Z ↔ ∃ a : El X, (g a).val = z := by
    change z ∈ elts Z ↔ _
    rw [hZ]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,h⟩
      exact ⟨a,h⟩
    · rintro ⟨a,h⟩
      exact ⟨g a,⟨a,rfl⟩,h⟩
  refine ⟨Z,?_,(finiteIn_iff M std Z).mpr ?_⟩
  · intro z
    rw [cut]
    constructor
    · rintro ⟨a,eq⟩
      exact ⟨a.val,a.property,eq ▸ hv a⟩
    · rintro ⟨a,ha,h⟩
      exact ⟨⟨a,ha⟩,map.2.2 _ _ _ (hv _) h⟩
  · exact ((hZ ▸ finite.image Subtype.val : (elts Z).Finite)).to_subtype

end ProjectiveZF
