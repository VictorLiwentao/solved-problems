module

public import SolvedProblems.RadoAtomBool
public import SolvedProblems.RadoOrderability
public import SolvedProblems.RadoTagged

@[expose] public section

namespace RadoSelection
universe u v

/-- Material sets with urelements. Extensionality applies only to sets. The
power set contains exactly the set-valued subsets; atoms are never subsets. -/
structure WithAtoms (V : Type u) (I : Type v) [LT I] where
  atom : V → Prop
  rank : V → I
  mem : V → V → Prop
  lower : ∀ {x y}, mem x y → rank x < rank y
  atom_empty : ∀ x, atom x → ∀ z, ¬ mem z x
  ext : ∀ {x y}, ¬ atom x → ¬ atom y → (∀ z, mem z x ↔ mem z y) → x = y
  empty : V
  empty_set : ¬ atom empty
  empty_mem : ∀ z, ¬ mem z empty
  add : V → V → V
  add_set : ∀ x s, ¬ atom (add x s)
  add_mem : ∀ z x s, mem z (add x s) ↔ z = x ∨ mem z s
  join : V → V → V
  join_set : ∀ s t, ¬ atom (join s t)
  join_mem : ∀ z s t, mem z (join s t) ↔ mem z s ∨ mem z t
  sep : V → (V → Prop) → V
  sep_set : ∀ s p, ¬ atom (sep s p)
  sep_mem : ∀ z s p, mem z (sep s p) ↔ mem z s ∧ p z
  power : V → V
  power_set : ∀ s, ¬ atom (power s)
  power_mem : ∀ w s, mem w (power s) ↔ ¬ atom w ∧ ∀ z, mem z w → mem z s
  transitive_bound : ∀ b, ∃ t, ¬ atom t ∧ (∀ z, mem z b → mem z t) ∧
    ∀ x, mem x t → ∀ z, mem z x → mem z t

namespace WithAtoms
variable {V : Type u} {I : Type v} [LinearOrder I] (M : WithAtoms V I)

/-- An injective presentation by elements of a single material set. -/
def Represented (A : Type w) : Prop :=
  ∃ (s : V) (e : A → V), ¬ M.atom s ∧ Function.Injective e ∧ ∀ a, M.mem (e a) s

def SelectionPrinciple : Prop :=
  ∀ (J : Type u), M.Represented J → ∀ A : J → Type u,
    (∃ (s : V) (e : (j : J) → A j → V), ¬ M.atom s ∧
      (∀ j, Function.Injective (e j)) ∧ ∀ j x, M.mem (e j x) s) → RadoOn J A

def BooleanPrinciple : Prop :=
  ∀ (B : Type u), M.Represented B → ∀ [BooleanAlgebra B] [Nontrivial B], BooleanPoint B

/-- Each *set* of urelements has some linear order. No order of the class of all
urelements, and no simultaneous choice of these orders, is part of this assertion. -/
def AtomOrder : Prop :=
  ∀ s : V, ¬ M.atom s → (∀ a, M.mem a s → M.atom a) →
    ∃ r : {z : V // M.mem z s} → {z : V // M.mem z s} → Prop,
      StrictOn (fun _ => True) r

private theorem subcarrier {A : Type w} {B : Type w'} (h : M.Represented A)
    (f : B → A) (hi : Function.Injective f) : M.Represented B := by
  obtain ⟨s,e,ns,he,hb⟩ := h
  exact ⟨s,e ∘ f,ns,he.comp hi,fun b => hb (f b)⟩

private theorem predicates {A : Type w} (h : M.Represented A) : M.Represented (A → Prop) := by
  obtain ⟨s,e,ns,he,hb⟩ := h
  let code := fun (p : A → Prop) => M.sep s (fun z => ∃ a, e a = z ∧ p a)
  have readback (p : A → Prop) (a : A) : M.mem (e a) (code p) ↔ p a := by
    rw [M.sep_mem]
    constructor
    · rintro ⟨_,x,ex,hx⟩
      exact he ex ▸ hx
    · exact fun ha => ⟨hb a,a,rfl,ha⟩
  refine ⟨M.power s,code,M.power_set _,?_,?_⟩
  · intro p q eq
    funext a
    exact propext ((readback p a).symm.trans (eq ▸ readback q a))
  · exact fun p => (M.power_mem _ _).mpr ⟨M.sep_set _ _,fun z hz => ((M.sep_mem z _ _).mp hz).1⟩

private theorem samples {A : Type w} (h : M.Represented A) : M.Represented (Sample A) :=
  M.subcarrier (M.predicates h) Sample.contains (fun _ _ e => Sample.ext fun a =>
    Iff.of_eq (congrFun e a))

private theorem sums {A : Type w} {B : Type w'} (ha : M.Represented A) (hb : M.Represented B) :
    M.Represented (A ⊕ B) := by
  obtain ⟨s,f,_,hf,fs⟩ := ha
  obtain ⟨t,g,_,hg,gt⟩ := hb
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
  refine ⟨M.power (M.add d d), Sum.elim left right, M.power_set _, ?_, ?_⟩
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
    refine ⟨?_,?_⟩
    · cases a <;> exact M.add_set _ _
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

private theorem germs {J : Type u} (h : M.Represented J) (F : Filter J) :
    M.Represented (F.Germ Bool) := by
  have functions := M.subcarrier (M.predicates h)
    (fun (f : J → Bool) x => f x = true) (by
      intro f g h
      funext x
      have eq := Iff.of_eq (congrFun h x)
      cases a : f x <;> cases b : g x <;> simp_all)
  apply M.quotientCarrier functions (Filter.Germ.ofFun (l := F))
  exact fun g => Filter.Germ.inductionOn g fun f => ⟨f,rfl⟩

private theorem queryAnswers (J : Type u) :
    ∃ (s : V) (e : J → ULift.{u} Bool → V),
      ¬ M.atom s ∧ (∀ j, Function.Injective (e j)) ∧ ∀ j x, M.mem (e j x) s := by
  let a := M.empty
  let b := M.add a a
  have hne : a ≠ b := fun eq => M.empty_mem a ((congrArg (M.mem a) eq).mpr ((M.add_mem a a a).mpr (Or.inl rfl)))
  let f := fun (x : ULift.{u} Bool) => if x.down then b else a
  refine ⟨M.add a (M.add b a),fun _ => f, M.add_set _ _, fun _ => ?_, fun _ x => ?_⟩
  · rintro ⟨x⟩ ⟨y⟩ h
    cases x <;> cases y <;> simp_all [f]
  · apply (M.add_mem _ _ _).mpr
    rcases x with ⟨x⟩
    cases x with
    | false => exact Or.inl rfl
    | true => exact Or.inr ((M.add_mem _ _ _).mpr (Or.inl rfl))

private theorem comparisonDomain {J : Type u} (h : M.Represented J) :
    M.Represented (Comparisons J) := by
  have pairs : M.Represented (J × J) := by
    let graph := fun (xy : J × J) (s : J ⊕ J) => s = .inl xy.1 ∨ s = .inr xy.2
    apply M.subcarrier (M.predicates (M.sums h h)) graph
    rintro ⟨x,y⟩ ⟨z,w⟩ eq
    apply Prod.ext
    · have hx : graph (z,w) (.inl x) := (Iff.of_eq (congrFun eq (.inl x))).mp (Or.inl rfl)
      rcases hx with h | h
      · exact Sum.inl.inj h
      · cases h
    · have hy : graph (z,w) (.inr y) := (Iff.of_eq (congrFun eq (.inr y))).mp (Or.inr rfl)
      rcases hy with h | h
      · cases h
      · exact Sum.inr.inj h
  apply M.subcarrier (M.predicates pairs) (fun (c : Comparisons J) x => c x = true)
  intro a b e
  funext x
  have he := Iff.of_eq (congrFun e x)
  cases aeq : a x <;> cases beq : b x <;> simp_all

private def optionLt {A : Type u} (r : A → A → Prop) : Option A → Option A → Prop
  | some a, some b => r a b
  | some _, none => True
  | none, _ => False

private theorem optionStrict {A : Type u} {r : A → A → Prop} (o : StrictOn (fun _ => True) r) :
    StrictOn (fun _ => True) (optionLt r) := by
  constructor
  · intro x _
    cases x with
    | none => exact id
    | some x => exact o.irrefl _ trivial
  · intro x y z _ _ _ hxy hyz
    cases x <;> cases y <;> cases z <;>
      first | exact hxy.elim | exact hyz.elim | exact trivial | exact o.trans trivial trivial trivial hxy hyz
  · intro x y _ _ hn
    cases x <;> cases y
    · exact (hn rfl).elim
    · exact Or.inr trivial
    · exact Or.inl trivial
    · exact o.compare trivial trivial (fun h => hn (congrArg some h))

private theorem order_transitive [WellFoundedLT I] [∀ p : Prop, Decidable p] (ord : M.AtomOrder)
    (t : V) (closed : ∀ x, M.mem x t → ∀ z, M.mem z x → M.mem z t)
    {U : (Sample {z : V // M.mem z t} → Prop) → Prop} (F : Fine U) :
    ∃ r : {z : V // M.mem z t} → {z : V // M.mem z t} → Prop, StrictOn (fun _ => True) r := by
  let a := M.sep t M.atom
  let A := {z : V // M.mem z a}
  let T := {z : V // M.mem z t}
  obtain ⟨r,o⟩ := ord a (M.sep_set _ _) (fun z hz => ((M.sep_mem _ _ _).mp hz).2)
  let tag := fun (x : T) => if hx : M.atom x.val then
    some (⟨x.val,(M.sep_mem _ _ _).mpr ⟨x.property,hx⟩⟩ : A) else none
  let H : Tagged T I (Option A) := {
    rank := fun x => M.rank x.val
    mem := fun x y => M.mem x.val y.val
    lower := M.lower
    tag := tag
    ext := by
      intro x y eq same
      apply Subtype.ext
      by_cases hx : M.atom x.val <;> by_cases hy : M.atom y.val
      · simpa only [tag, dite_eq_left hx, dite_eq_left hy, Option.some.injEq, Subtype.mk.injEq] using eq
      · simp only [tag, dite_eq_left hx, dite_eq_right hy, reduceCtorEq] at eq
      · simp only [tag, dite_eq_right hx, dite_eq_left hy, reduceCtorEq] at eq
      · apply M.ext hx hy
        intro z
        exact ⟨fun hz => (same ⟨z,closed _ x.property _ hz⟩).mp hz,
          fun hz => (same ⟨z,closed _ y.property _ hz⟩).mpr hz⟩ }
  exact tagged_order H (optionStrict o) F

/-- Over sets with urelements, BPI is equivalent to Rado selection together with
linear orderability of every individual set of atoms. -/
theorem equivalence [WellFoundedLT I] [∀ p : Prop, Decidable p] :
    M.BooleanPrinciple ↔ M.SelectionPrinciple ∧ M.AtomOrder := by
  constructor
  · intro bpi
    constructor
    · intro J h A _
      obtain ⟨U,F⟩ := quotient_fine J (@bpi _ (M.germs (M.samples h) (cones J))
        (germAlgebra _) (nontrivial_quotient J))
      exact F.rado A
    · intro s ns _
      let A := {z : V // M.mem z s}
      have a : M.Represented A := ⟨s,Subtype.val,ns,Subtype.val_injective,Subtype.property⟩
      exact order_from_comparison_point A (@bpi _ (M.germs (M.comparisonDomain a) (orderFilter A))
        (germAlgebra _) (comparison_quotient_nontrivial A))
  · rintro ⟨rl,ord⟩ B hb alg nt
    have fine {T : Type u} (rt : M.Represented T) : ∃ U : (Sample T → Prop) → Prop, Fine U :=
      fine_of_queries (rl (Query T) (M.sums rt (M.predicates (M.samples rt))) _ (M.queryAnswers _))
    obtain ⟨U,F⟩ := fine hb
    obtain ⟨x,enc,_,inj,bound⟩ := hb
    obtain ⟨t,nt',xt,closed⟩ := M.transitive_bound x
    let T := {z : V // M.mem z t}
    have rt : M.Represented T := ⟨t,Subtype.val,nt',Subtype.val_injective,Subtype.property⟩
    obtain ⟨_,G⟩ := fine rt
    obtain ⟨r,o⟩ := M.order_transitive ord t closed G
    let e := fun b : B => (⟨enc b, xt _ (bound b)⟩ : T)
    exact boolean_of_fine_order F (r := fun b c => r (e b) (e c))
      ⟨fun _ _ => o.irrefl _ trivial, fun _ _ _ => o.trans trivial trivial trivial,
        fun _ _ hn => o.compare trivial trivial (fun h => hn (inj (congrArg Subtype.val h)))⟩

end WithAtoms
end RadoSelection
