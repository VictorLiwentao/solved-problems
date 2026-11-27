module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.ModelTheory.Semantics


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

variable {V : Type*} [Membership V V] (M : Core V)

/-- A coordinate of an internal graph is changed to the given value. -/
def Patch (i y s t : V) : Prop := ∀ j z, Edge t j z ↔ (j = i ∧ z = y) ∨ (j ≠ i ∧ Edge s j z)

theorem defPatch {ι : Type*} {i y s t : (ι → V) → V} (hi : Term i) (hy : Term y) (hs : Term s) (ht : Term t) :
    Definable (fun u => Patch (i u) (y u) (s u) (t u)) := by unfold Patch; zf_map_formula

include M

/-- Coordinate replacement exists internally. -/
theorem patchExists {X I s i y : V} (hs : IsMap I X s) (hi : i ∈ I) (hy : y ∈ X) :
    ∃ t, IsMap I X t ∧ Patch i y s t := by
  let R (j z : V) := (j = i ∧ z = y) ∨ (j ≠ i ∧ Edge s j z)
  have d : Binary R := by unfold Binary R; zf_map_formula
  have typed {j z : V} (h : R j z) : j ∈ I ∧ z ∈ X := by
    rcases h with ⟨rfl,rfl⟩|⟨_,edge⟩
    · exact ⟨hi,hy⟩
    · exact edge_typed M hs edge
  have total (j) (hj : j ∈ I) : ∃ z, z ∈ X ∧ R j z := by
    by_cases eq : j = i
    · exact ⟨y,hy,Or.inl ⟨eq,rfl⟩⟩
    · obtain ⟨z,hz⟩ := hs.2.1 _ hj
      exact ⟨z,(edge_typed M hs hz).2,Or.inr ⟨eq,hz⟩⟩
  have unique (j) (_ : j ∈ I) (a) (_ : a ∈ X) (b) (_ : b ∈ X) (x : R j a) (y : R j b) : a = b := by
    rcases x with ⟨xi,xa⟩|⟨xi,xa⟩ <;> rcases y with ⟨yi,yb⟩|⟨yi,yb⟩
    · exact xa.trans yb.symm
    · exact (yi xi).elim
    · exact (xi yi).elim
    · exact hs.2.2 _ _ _ xa yb
  obtain ⟨t,ht,rule⟩ := mapFrom M I X R d total unique
  exact ⟨t,ht,fun j z => (rule j z).trans ⟨fun h => h.2.2,fun h => ⟨(typed h).1,(typed h).2,h⟩⟩⟩

theorem patchUnique {X I s t u i y : V} (ht : IsMap I X t) (hu : IsMap I X u) (p : Patch i y s t) (q : Patch i y s u) :
    t = u := graph_ext M ht hu fun j _ z => (p j z).trans (q j z).symm

omit M in
theorem patchBack {I X s t i a b : V} (hs : IsMap I X s) (old : Edge s i b) (p : Patch i a s t) : Patch i b t s := by
  intro j z
  by_cases eq : j = i
  · subst j
    simp
    exact ⟨fun h => hs.2.2 _ _ _ h old,fun h => h ▸ old⟩
  · simpa [eq] using (p j z).symm

omit M in
theorem patchAbsorb {s t u i a b : V} (p : Patch i a s t) (q : Patch i b s u) : Patch i b t u := by
  intro j z
  by_cases eq : j = i
  · simpa [eq] using q j z
  · simpa [eq] using ((q j z).trans (by simpa [eq] using (p j z).symm))

/-- A constant graph is an internal element of the function space. -/
theorem constantGraph {X I a : V} (ha : a ∈ X) : ∃ s, IsMap I X s ∧ ∀ j ∈ I, Edge s j a := by
  let R (_ z : V) := z = a
  obtain ⟨s,hs,edge⟩ := mapFrom M I X R (by unfold Binary R; zf_map_formula)
    (fun j _ => ⟨a,ha,rfl⟩) (fun _ _ _ _ _ _ h k => h.trans k.symm)
  exact ⟨s,hs,fun j hj => (edge j a).mpr ⟨hj,ha,rfl⟩⟩

end ProjectiveZF

@[expose] public section

namespace ProjectiveZF

variable {V : Type*} [Membership V V]

/-- A noninjective self-surjection is an actual set of the membership model,
with a preimage for each internal element and a witnessed collision. -/
def DualInfinite (X : V) : Prop := ∃ f : V, IsMap X X f ∧
  (∀ y, y ∈ X → ∃ x, x ∈ X ∧ Edge f x y) ∧
  ∃ a, a ∈ X ∧ ∃ b, b ∈ X ∧ a ≠ b ∧ ∃ y, Edge f a y ∧ Edge f b y

/-- The coordinate operation composes the given internal map at `i`, leaving
all other coordinates fixed. -/
def Step (f i s t : V) : Prop := ∃ a b, Edge s i a ∧ Edge f a b ∧ Patch i b s t

private theorem defStep {ι : Type*} {f i s t : (ι → V) → V} (hf : Term f) (hi : Term i) (hs : Term s) (ht : Term t) :
    Definable (fun v => Step (f v) (i v) (s v) (t v)) := by
  unfold Step
  repeat' first | apply defPatch | apply defEdge | apply defAnd | apply defEx | zf_terms

/-- In every model of this fragment of pure ZF, dual Dedekind infinity of `X`
implies dual Dedekind infinity of its internal function space `X^I` for every
internally nonempty `I`. The graph of the lifted function is produced inside
the model by a first-order Separation instance. -/
theorem coordinateLift (M : Core V) (X I i : V) (hi : i ∈ I) (dual : DualInfinite X) :
    DualInfinite (exponential M X I) := by
  obtain ⟨f,hf,onto,a,ha,b,hb,ne,c,hac,hbc⟩ := dual
  let E := exponential M X I
  have mapmem (s : V) : s ∈ E ↔ IsMap I X s := mem_exponential M
  have total (s : V) (hs : s ∈ E) : ∃ t, t ∈ E ∧ Step f i s t := by
    have smap := (mapmem s).mp hs
    obtain ⟨x,hx⟩ := smap.2.1 _ hi
    obtain ⟨y,hy⟩ := hf.2.1 x (edge_typed M smap hx).2
    obtain ⟨t,ht,p⟩ := patchExists M smap hi (edge_typed M hf hy).2
    exact ⟨t,(mapmem t).mpr ht,x,y,hx,hy,p⟩
  have unique (s : V) (hs : s ∈ E) (t) (ht : t ∈ E) (u) (hu : u ∈ E) (st : Step f i s t) (su : Step f i s u) : t = u := by
    obtain ⟨x,y,hx,hy,pt⟩ := st
    obtain ⟨x',y',hx',hy',pu⟩ := su
    obtain rfl := ((mapmem s).mp hs).2.2 i x x' hx hx'
    obtain rfl := hf.2.2 _ _ _ hy hy'
    exact patchUnique M ((mapmem t).mp ht) ((mapmem u).mp hu) pt pu
  have form : Binary (Step f i) := defStep (termParam f) (termParam i) (termVar false) (termVar true)
  obtain ⟨F,map,rule⟩ := mapFrom M E E (Step f i) form total unique
  refine ⟨F,map,?_,?_⟩
  · intro t ht
    have tmap := (mapmem t).mp ht
    obtain ⟨y,hy⟩ := tmap.2.1 _ hi
    obtain ⟨x,hx,xy⟩ := onto _ (edge_typed M tmap hy).2
    obtain ⟨s,smap,p⟩ := patchExists M tmap hi hx
    have hs := (mapmem s).mpr smap
    exact ⟨s,hs,(rule s t).mpr ⟨hs,ht,x,y,(p i x).mpr (Or.inl ⟨rfl,rfl⟩),xy,patchBack tmap hy p⟩⟩
  · obtain ⟨s,sm,edge⟩ := constantGraph (I := I) M ha
    obtain ⟨t,tm,pt⟩ := patchExists M sm hi hb
    obtain ⟨u,um,pu⟩ := patchExists M sm hi (edge_typed M hf hac).2
    have hs := (mapmem s).mpr sm
    have ht := (mapmem t).mpr tm
    have hu := (mapmem u).mpr um
    have bt : Edge t i b := (pt i b).mpr (Or.inl ⟨rfl,rfl⟩)
    refine ⟨s,hs,t,ht,fun eq => ne (sm.2.2 i a b (edge i hi) (eq ▸ bt)),u,?_,?_⟩
    · exact (rule s u).mpr ⟨hs,hu,a,c,edge i hi,hac,pu⟩
    · exact (rule t u).mpr ⟨ht,hu,b,c,bt,hbc,patchAbsorb pt pu⟩

end ProjectiveZF
