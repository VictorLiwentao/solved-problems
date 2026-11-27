module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.Data.Fin.Tuple.Basic

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
