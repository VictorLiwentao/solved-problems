module

public import SolvedProblems.RadoConverse

@[expose] public section

namespace RadoSelection

universe u v

/-- The pure set operations used in the proof. In ZF the transitive bound can
be taken to be the transitive closure of the singleton of the input. Separation,
power set, binary union and adjoining a single point are the ordinary set operations. -/
structure Material (V : Type u) (I : Type v) [LT I] extends Hierarchy V I where
  empty : V
  empty_mem : ∀ z, ¬ mem z empty
  add : V → V → V
  add_mem : ∀ z x s, mem z (add x s) ↔ z = x ∨ mem z s
  join : V → V → V
  join_mem : ∀ z a b, mem z (join a b) ↔ mem z a ∨ mem z b
  sep : V → (V → Prop) → V
  sep_mem : ∀ z s p, mem z (sep s p) ↔ mem z s ∧ p z
  power : V → V
  power_mem : ∀ w s, mem w (power s) ↔ ∀ z, mem z w → mem z s
  transitive_bound : ∀ b, ∃ t, (∀ z, mem z b → mem z t) ∧
    ∀ x, mem x t → ∀ z, mem z x → mem z t

namespace Material

variable {V : Type u} {I : Type v} [LinearOrder I] (M : Material V I)

/-- The carrier can be presented as elements of one set. Injectivity lets the
carrier use any extensional presentation of those elements. -/
def Represented (A : Type w) : Prop :=
  ∃ (s : V) (e : A → V), Function.Injective e ∧ ∀ a, M.mem (e a) s

/-- The indexed family of answers takes values in one set (the union of the family).
Tags need only be injective within each answer set. -/
def SelectionPrinciple : Prop :=
  ∀ (J : Type u), M.Represented J → ∀ A : J → Type u,
    (∃ (s : V) (e : (j : J) → A j → V),
      (∀ j, Function.Injective (e j)) ∧ ∀ j x, M.mem (e j x) s) → RadoOn J A

def BooleanPrinciple : Prop :=
  ∀ (B : Type u), M.Represented B → ∀ [BooleanAlgebra B] [Nontrivial B], BooleanPoint B

private theorem subcarrier {A : Type w} {B : Type w'} (h : M.Represented A)
    (f : B → A) (hi : Function.Injective f) : M.Represented B := by
  obtain ⟨s,e,he,hb⟩ := h
  exact ⟨s,e ∘ f,he.comp hi,fun b => hb (f b)⟩

private theorem predicates {A : Type w} (h : M.Represented A) : M.Represented (A → Prop) := by
  obtain ⟨s,e,he,hb⟩ := h
  let code := fun (p : A → Prop) => M.sep s (fun z => ∃ a, e a = z ∧ p a)
  have readback (p : A → Prop) (a : A) : M.mem (e a) (code p) ↔ p a := by
    rw [M.sep_mem]
    constructor
    · rintro ⟨_,x,ex,hx⟩
      exact he ex ▸ hx
    · exact fun ha => ⟨hb a,a,rfl,ha⟩
  refine ⟨M.power s,code,?_,?_⟩
  · intro p q eq
    funext a
    exact propext ((readback p a).symm.trans (eq ▸ readback q a))
  · exact fun p => (M.power_mem _ _).mpr (fun z hz => ((M.sep_mem z _ _).mp hz).1)

private theorem samples {A : Type w} (h : M.Represented A) : M.Represented (Sample A) :=
  M.subcarrier (M.predicates h) Sample.contains (fun _ _ e => Sample.ext fun a =>
    Iff.of_eq (congrFun e a))

private theorem sums {A : Type w} {B : Type w'} (ha : M.Represented A) (hb : M.Represented B) :
    M.Represented (A ⊕ B) := by
  obtain ⟨s,f,hf,fs⟩ := ha
  obtain ⟨t,g,hg,gt⟩ := hb
  let d := M.join s t
  have fd (a) := (M.join_mem _ s t).mpr (Or.inl (fs a))
  have gd (b) := (M.join_mem _ s t).mpr (Or.inr (gt b))
  let one := fun z => M.add z M.empty
  have mem_one (z a : V) : M.mem z (one a) ↔ z = a :=
    (M.add_mem _ _ _).trans (or_iff_left (M.empty_mem z))
  let left := fun a => one (f a)
  let right := fun b => M.add d (one (g b))
  have noSelf : ¬ M.mem d d := fun h => lt_irrefl _ (M.lower h)
  have nl (a) : ¬ M.mem d (left a) := fun h => noSelf (Eq.mpr (congrArg (fun z => M.mem z d) ((mem_one _ _).mp h)) (fd a))
  have yr (b) : M.mem d (right b) := (M.add_mem _ _ _).mpr (Or.inl rfl)
  have diff (a b) : left a ≠ right b := fun eq => nl a (eq ▸ yr b)
  refine ⟨M.power (M.add d d), Sum.elim left right, ?_, ?_⟩
  · intro a b eq
    cases a <;> cases b
    case inl.inl x y =>
      change left x = left y at eq
      have hm : M.mem (f x) (left y) := (congrArg (M.mem (f x)) eq).mp ((mem_one _ _).mpr rfl)
      exact congrArg Sum.inl (hf ((mem_one _ _).mp hm))
    case inl.inr x y => exact (diff x y eq).elim
    case inr.inl x y => exact (diff y x eq.symm).elim
    case inr.inr x y =>
      change right x = right y at eq
      have hz : M.mem (g x) (right y) := (congrArg (M.mem (g x)) eq).mp
        ((M.add_mem _ _ _).mpr (Or.inr ((mem_one _ _).mpr rfl)))
      rcases (M.add_mem _ _ _).mp hz with hx | hx
      · exact (noSelf ((congrArg (fun z => M.mem z d) hx).mp (gd x))).elim
      · exact congrArg Sum.inr (hg ((mem_one _ _).mp hx))
  · intro a
    apply (M.power_mem _ _).mpr
    intro z hz
    apply (M.add_mem _ _ _).mpr
    cases a with
    | inl x => exact Or.inr ((congrArg (fun a => M.mem a d) ((mem_one _ _).mp hz)).mpr (fd x))
    | inr y => exact ((M.add_mem _ _ _).mp hz).imp_right (fun h => (congrArg (fun a => M.mem a d) ((mem_one _ _).mp h)).mpr (gd y))

private theorem quotientCarrier {X : Type w} {Y : Type w'} (h : M.Represented X)
    (f : X → Y) (onto : Function.Surjective f) : M.Represented Y :=
  M.subcarrier (M.predicates h) (fun y x => f x = y) (by
    intro y z eq
    obtain ⟨x,hx⟩ := onto y
    exact hx.symm.trans ((Iff.of_eq (congrFun eq x)).mp hx))

private theorem quotientRepresented {J : Type u} (h : M.Represented J) :
    M.Represented ((cones J).Germ Bool) := by
  have functions := M.subcarrier (M.predicates (M.samples h))
    (fun (f : Sample J → Bool) x => f x = true) (by
      intro f g h
      funext x
      have eq := Iff.of_eq (congrFun h x)
      cases a : f x <;> cases b : g x <;> simp_all)
  apply M.quotientCarrier functions (Filter.Germ.ofFun (l := cones J))
  exact fun g => Filter.Germ.inductionOn g fun f => ⟨f,rfl⟩

private theorem queryAnswers (J : Type u) :
    ∃ (s : V) (e : J → ULift.{u} Bool → V),
      (∀ j, Function.Injective (e j)) ∧ ∀ j x, M.mem (e j x) s := by
  let a := M.empty
  let b := M.add a a
  have hne : a ≠ b := fun eq => M.empty_mem a ((congrArg (M.mem a) eq).mpr ((M.add_mem a a a).mpr (Or.inl rfl)))
  let f := fun (x : ULift.{u} Bool) => if x.down then b else a
  refine ⟨M.add a (M.add b a),fun _ => f, fun _ => ?_, fun _ x => ?_⟩
  · rintro ⟨x⟩ ⟨y⟩ h
    cases x <;> cases y <;> simp_all [f]
  · apply (M.add_mem _ _ _).mpr
    rcases x with ⟨x⟩
    cases x with
    | false => exact Or.inl rfl
    | true => exact Or.inr ((M.add_mem _ _ _).mpr (Or.inl rfl))

/-- Rado selection and BPI are equivalent on the sets of any pure ranked material
universe with the indicated ZF set operations. No form of choice is required in
the metatheory. The Rado input includes its local selections on every finite domain. -/
theorem equivalence [WellFoundedLT I] [∀ p : Prop, Decidable p] : M.SelectionPrinciple ↔ M.BooleanPrinciple := by
  constructor
  · intro rl B hb alg nt
    obtain ⟨x,enc,inj,bound⟩ := hb
    obtain ⟨t,xt,closed⟩ := M.transitive_bound x
    let T := {z : V // M.mem z t}
    have rt : M.Represented T := ⟨t,Subtype.val,Subtype.val_injective,Subtype.property⟩
    have rq := M.sums rt (M.predicates (M.samples rt))
    obtain ⟨U,F⟩ := fine_of_queries (rl (Query T) rq _ (M.queryAnswers _))
    let H : Hierarchy T I := {
      rank := fun z => M.rank z.val
      mem := fun a b => M.mem a.val b.val
      lower := M.lower
      ext := by
        intro a b same
        apply Subtype.ext
        apply M.ext
        intro z
        exact ⟨fun hz => (same ⟨z,closed _ a.property z hz⟩).mp hz,
          fun hz => (same ⟨z,closed _ b.property z hz⟩).mpr hz⟩ }
    exact boolean_from_fine H F B (fun b => ⟨enc b, xt _ (bound b)⟩) (fun _ _ h => inj (congrArg Subtype.val h))
  · intro bpi J hj A _
    obtain ⟨U,F⟩ := quotient_fine J (@bpi _ (M.quotientRepresented hj) (germAlgebra _) (nontrivial_quotient J))
    exact F.rado A

end Material
end RadoSelection
