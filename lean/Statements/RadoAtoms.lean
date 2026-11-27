module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Filter.Germ.Basic

@[expose] public section

namespace RadoSelection
universe u v
open Filter
attribute [-instance] BooleanAlgebra.toBiheytingAlgebra BooleanAlgebra.toGeneralizedBooleanAlgebra

/-- An unordered finite subset: only its membership predicate is data. Existence of
a listing is a proposition and supplies no simultaneous choice of enumerations. -/
structure Sample (A : Type u) where
  contains : A → Prop
  finite : ∃ l : List A, ∀ x, contains x ↔ x ∈ l

instance {A : Type u} : Membership A (Sample A) := ⟨Sample.contains⟩
namespace Sample
variable {A : Type u}

theorem ext {s t : Sample A} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  cases s with | mk s hs =>
    cases t with | mk t ht =>
      have e : s = t := funext fun x => propext (h x)
      cases e
      rfl

def ofList (l : List A) : Sample A := ⟨(· ∈ l), ⟨l, fun _ => Iff.rfl⟩⟩

def adjoin (a : A) (s : Sample A) : Sample A where
  contains x := x = a ∨ x ∈ s
  finite := by
    obtain ⟨l, hl⟩ := s.finite
    exact ⟨a :: l, fun x => (or_congr Iff.rfl (hl x)).trans List.mem_cons.symm⟩

theorem mem_adjoin {x a : A} {s : Sample A} : x ∈ adjoin a s ↔ x = a ∨ x ∈ s := Iff.rfl

@[elab_as_elim] theorem induction {P : Sample A → Prop} (s : Sample A)
    (empty : P (ofList [])) (step : ∀ a s, P s → P (adjoin a s)) : P s := by
  obtain ⟨l, hl⟩ := s.finite
  have eq : s = ofList l := ext hl
  rw [eq]
  clear eq hl
  induction l with
  | nil => exact empty
  | cons a l ih =>
    have eq' : ofList (a :: l) = adjoin a (ofList l) :=
      ext fun _ => List.mem_cons
    exact eq' ▸ step a _ ih
end Sample

/-- A strict linear order on the indicated domain. -/
structure StrictOn {A : Type u} (D : A → Prop) (r : A → A → Prop) : Prop where
  irrefl : ∀ x, D x → ¬ r x x
  trans : ∀ {x y z}, D x → D y → D z → r x y → r y z → r x z
  compare : ∀ {x y}, D x → D y → x ≠ y → r x y ∨ r y x

/-- A proper ultrafilter on unordered finite samples containing every point cone.
All operations act on predicates, so the definition requires no decidable equality. -/
structure Fine {A : Type u} (U : (Sample A → Prop) → Prop) : Prop where
  proper : ¬ U (fun _ => False)
  mono : ∀ {p q : Sample A → Prop}, (∀ s, p s → q s) → U p → U q
  inter : ∀ {p q : Sample A → Prop}, U p → U q → U (fun s => p s ∧ q s)
  decide : ∀ p, U p ∨ U (fun s => ¬ p s)
  cone : ∀ x, U (fun s => x ∈ s)

/-- Rado's indexed selection principle. Local choices and the global choice are
graphs of functions. This spells out their unique-value condition without using a
choice operator to turn a uniquely determined value into a term. -/
def RadoOn (J : Type u) (A : J → Type v) : Prop :=
  (∀ j, ∃ l : List (A j), ∀ x, x ∈ l) →
  ∀ c : Sample J → (j : J) → A j → Prop,
    (∀ s j, j ∈ s → ∃! x, c s j x) →
    ∃ g : (j : J) → A j → Prop,
      (∀ j, ∃! x, g j x) ∧
      ∀ d : Sample J, ∃ e : Sample J, (∀ j ∈ d, j ∈ e) ∧
        ∀ j ∈ d, ∀ x, (g j x ↔ c e j x)
namespace Fine
variable {J : Type u} {U : (Sample J → Prop) → Prop} (F : Fine U)
include F

private theorem all : U (fun _ => True) := by
  rcases F.decide (fun _ => False) with h | h
  · exact (F.proper h).elim
  · exact F.mono (fun _ _ => trivial) h

private theorem holdsSomewhere [∀ p : Prop, Decidable p] {p : Sample J → Prop} (h : U p) :
    ∃ s, p s := by
  apply Decidable.byContradiction
  intro hn
  exact F.proper (F.mono (fun s hs => hn ⟨s,hs⟩) h)

private theorem finiteUnion {X : Type v} (l : List X) (c : X → Sample J → Prop)
    (h : U (fun s => ∃ x ∈ l, c x s)) : ∃ x ∈ l, U (c x) := by
  induction l with
  | nil =>
    exact (F.proper (F.mono (fun _ ⟨_, hx, _⟩ => List.not_mem_nil hx) h)).elim
  | cons a l ih =>
    rcases F.decide (c a) with ha | ha
    · exact ⟨a, List.mem_cons_self, ha⟩
    · have h' : U (fun s => ∃ x ∈ l, c x s) := by
        apply F.mono _ (F.inter h ha)
        rintro s ⟨⟨x, hx, hxc⟩, hna⟩
        rcases List.mem_cons.mp hx with rfl | hxl
        · exact (hna hxc).elim
        · exact ⟨x,hxl,hxc⟩
      obtain ⟨x,hx,hc⟩ := ih h'
      exact ⟨x,List.mem_cons_of_mem _ hx,hc⟩

private theorem finiteInter (s : Sample J) (p : J → Sample J → Prop)
    (h : ∀ j ∈ s, U (p j)) : U (fun d => ∀ j ∈ s, p j d) := by
  induction s using Sample.induction with
  | empty =>
    exact F.mono (fun _ _ j hj => (List.not_mem_nil (α := J) (a := j) hj).elim) F.all
  | step a s ih =>
    have ha := h a (Or.inl rfl)
    have hs := ih (fun j hj => h j (Or.inr hj))
    apply F.mono _ (F.inter ha hs)
    rintro d ⟨hda, hds⟩ j (rfl | hj)
    · exact hda
    · exact hds j hj

theorem rado [∀ p : Prop, Decidable p] (A : J → Type v) : RadoOn J A := by
  intro fin c hc
  let cell := fun (j : J) (x : A j) (e : Sample J) => j ∈ e ∧ c e j x
  let g := fun (j : J) (x : A j) => U (cell j x)
  have single (j : J) : ∃! x, g j x := by
    obtain ⟨l,hl⟩ := fin j
    have cover : U (fun e => ∃ x ∈ l, cell j x e) := by
      apply F.mono _ (F.cone j)
      intro e he
      obtain ⟨x,hx,_⟩ := hc e j he
      exact ⟨x, hl x, he, hx⟩
    obtain ⟨x,_,hx⟩ := F.finiteUnion l _ cover
    refine ⟨x, hx, ?_⟩
    intro y hy
    obtain ⟨e,he⟩ := F.holdsSomewhere (F.inter hx hy)
    exact (hc e j he.1.1).unique he.2.2 he.1.2
  refine ⟨g, single, ?_⟩
  intro d
  let agrees := fun (j : J) (e : Sample J) =>
    j ∈ e ∧ ∀ x, g j x ↔ c e j x
  have hj (j : J) : U (agrees j) := by
    obtain ⟨x,hx,ux⟩ := single j
    apply F.mono _ hx
    rintro e ⟨hje,hcx⟩
    refine ⟨hje, fun y => ⟨fun hy => ux y hy ▸ hcx, fun hy => ?_⟩⟩
    exact (hc e j hje).unique hy hcx ▸ hx
  obtain ⟨e,he⟩ := F.holdsSomewhere (F.finiteInter d agrees (fun j _ => hj j))
  exact ⟨e,fun j h => (he j h).1, fun j h => (he j h).2⟩
end Fine

abbrev Query (T : Type u) := T ⊕ (Sample T → Prop)

private def points {T : Type u} (d : Sample (Query T)) : Sample T where
  contains t := Sum.inl t ∈ d
  finite := by
    obtain ⟨l, hl⟩ := d.finite
    let proj : Query T → Option T := Sum.elim some (fun _ => none)
    refine ⟨l.filterMap proj, fun t => (hl _).trans ?_⟩
    constructor
    · intro h
      exact List.mem_filterMap.mpr ⟨Sum.inl t, h, rfl⟩
    · intro h
      obtain ⟨q,hq,eq⟩ := List.mem_filterMap.mp h
      cases q with
      | inl x =>
        have hxt : x = t := Option.some.inj eq
        exact hxt ▸ hq
      | inr _ => cases eq

private theorem fine_of_agreement {T : Type u} [∀ p : Prop, Decidable p]
    {U : (Sample T → Prop) → Prop}
    (h : ∀ d : List (Query T), ∃ s : Sample T,
      (∀ t, Sum.inl t ∈ d → t ∈ s) ∧
      ∀ p, Sum.inr p ∈ d → (U p ↔ p s)) : Fine U := by
  constructor
  · let p : Sample T → Prop := fun _ => False
    obtain ⟨s,_,h⟩ := h [Sum.inr p]
    exact (h p List.mem_cons_self).mp
  · intro p q hpq hp
    obtain ⟨s,_,hs⟩ := h [Sum.inr p, Sum.inr q]
    exact (hs q (by simp)).mpr (hpq s ((hs p (by simp)).mp hp))
  · intro p q hp hq
    let pq : Sample T → Prop := fun s => p s ∧ q s
    obtain ⟨s,_,hs⟩ := h [Sum.inr p, Sum.inr q, Sum.inr pq]
    exact (hs pq (by simp)).mpr ⟨(hs p (by simp)).mp hp, (hs q (by simp)).mp hq⟩
  · intro p
    let np : Sample T → Prop := fun s => ¬ p s
    obtain ⟨s,_,hs⟩ := h [Sum.inr p, Sum.inr np]
    by_cases hp : p s
    · exact Or.inl ((hs p (by simp)).mpr hp)
    · exact Or.inr ((hs np (by simp)).mpr hp)
  · intro t
    let cone : Sample T → Prop := fun s => t ∈ s
    obtain ⟨s,ht,hs⟩ := h [Sum.inl t, Sum.inr cone]
    exact (hs cone (by simp)).mpr (ht t (by simp))

theorem fine_of_queries {T : Type u} [∀ p : Prop, Decidable p]
    (rl : RadoOn (Query T) (fun _ => ULift.{v} Bool)) : ∃ U : (Sample T → Prop) → Prop, Fine U := by
  let answer : Query T → Type v := fun _ => ULift.{v} Bool
  let val := fun (s : Sample (Query T)) (j : Query T) => ULift.up.{v}
    (match j with | .inl _ => false | .inr p => decide (p (points s)))
  have finite (j : Query T) : ∃ l : List (answer j), ∀ x, x ∈ l := by
    refine ⟨[⟨false⟩,⟨true⟩], ?_⟩
    rintro ⟨b⟩
    cases b <;> simp
  obtain ⟨g,_,agree⟩ := rl finite (fun s j x => x = val s j)
    (fun s j _ => ⟨val s j, rfl, fun _ h => h⟩)
  let U := fun (p : Sample T → Prop) => g (Sum.inr p) (ULift.up true)
  refine ⟨U, fine_of_agreement ?_⟩
  intro d
  obtain ⟨e,he,ge⟩ := agree (Sample.ofList d)
  refine ⟨points e, fun t ht => he (Sum.inl t) ht, ?_⟩
  intro p hp
  change g (Sum.inr p) (ULift.up true) ↔ p (points e)
  rw [ge (Sum.inr p) hp]
  change ULift.up.{v} true = ULift.up (decide (p (points e))) ↔ p (points e)
  simp

/-- A homomorphism to the two-element Boolean algebra, given on the standard
generators of the Boolean signature (join then follows by De Morgan). -/
def BooleanPoint (B : Type u) [BooleanAlgebra B] : Prop :=
  ∃ f : B → Bool, f ⊥ = false ∧ f ⊤ = true ∧
    (∀ x y, f (x ⊓ y) = (f x && f y)) ∧ ∀ x, f xᶜ = !(f x)

private def Listing {A : Type u} (r : A → A → Prop) (s : Sample A) (l : List A) : Prop :=
  (∀ x, x ∈ s ↔ x ∈ l) ∧ l.Pairwise r

private theorem insert_sorted {A : Type u} [∀ p : Prop, Decidable p] {r : A → A → Prop}
    (o : StrictOn (fun _ => True) r) (a : A) (l : List A) (hl : List.Pairwise r l)
    (ha : a ∉ l) : ∃ w : List A, (∀ x, x ∈ w ↔ x = a ∨ x ∈ l) ∧ w.Pairwise r := by
  induction l with
  | nil => exact ⟨[a],fun x => List.mem_cons, List.pairwise_singleton ..⟩
  | cons b l ih =>
    obtain ⟨hb, hl⟩ := List.pairwise_cons.mp hl
    have hn : a ≠ b := fun e => ha (List.mem_cons.mpr (Or.inl e))
    rcases o.compare trivial trivial hn with hab | hba
    · refine ⟨a :: b :: l, fun _ => List.mem_cons, List.pairwise_cons.mpr ⟨?_, ?_⟩⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxl
        · exact hab
        · exact o.trans trivial trivial trivial hab (hb _ hxl)
      · exact List.pairwise_cons.mpr ⟨hb,hl⟩
    · obtain ⟨w,hw,pw⟩ := ih hl (fun h => ha (List.mem_cons_of_mem _ h))
      refine ⟨b :: w, ?_, List.pairwise_cons.mpr ⟨?_,pw⟩⟩
      · intro x
        rw [List.mem_cons, hw, List.mem_cons, or_left_comm]
      · intro x hx
        rcases (hw x).mp hx with rfl | hxl
        · exact hba
        · exact hb _ hxl

private theorem listing_exists {A : Type u} [∀ p : Prop, Decidable p] {r : A → A → Prop}
    (o : StrictOn (fun _ => True) r) (s : Sample A) : ∃ l, Listing r s l := by
  induction s using Sample.induction with
  | empty => exact ⟨[],fun _ => Iff.rfl,.nil⟩
  | step a s ih =>
    obtain ⟨l, hl, pl⟩ := ih
    by_cases ha : a ∈ s
    · refine ⟨l, ?_, pl⟩
      intro x
      exact (or_iff_right_of_imp fun h => h ▸ ha).trans (hl x)
    · obtain ⟨w,hw,pw⟩ := insert_sorted o a l pl (fun h => ha ((hl _).mpr h))
      exact ⟨w, fun x => (or_congr Iff.rfl (hl x)).trans (hw x).symm, pw⟩

private theorem listing_unique {A : Type u} [∀ p : Prop, Decidable p] {r : A → A → Prop}
    (o : StrictOn (fun _ => True) r) {l w : List A} (hl : l.Pairwise r) (hw : w.Pairwise r)
    (same : ∀ x, x ∈ l ↔ x ∈ w) : l = w := by
  induction l generalizing w with
  | nil =>
    cases w with
    | nil => rfl
    | cons a w => exact (List.not_mem_nil ((same a).mpr List.mem_cons_self)).elim
  | cons a l ih =>
    cases w with
    | nil => exact (List.not_mem_nil ((same a).mp List.mem_cons_self)).elim
    | cons b w =>
      obtain ⟨ah, hl⟩ := List.pairwise_cons.mp hl
      obtain ⟨bh, hwTail⟩ := List.pairwise_cons.mp hw
      have eq : a = b := by
        apply Decidable.byContradiction
        intro hn
        have hab := (List.mem_cons.mp ((same a).mp List.mem_cons_self)).resolve_left hn
        have hba := (List.mem_cons.mp ((same b).mpr List.mem_cons_self)).resolve_left (Ne.symm hn)
        exact o.irrefl _ trivial (o.trans trivial trivial trivial (ah b hba) (bh a hab))
      subst b
      congr 1
      apply ih hl hwTail
      intro x
      by_cases hx : x = a
      · subst x
        exact ⟨fun h => (o.irrefl _ trivial (ah _ h)).elim,
          fun h => (o.irrefl _ trivial (bh _ h)).elim⟩
      · simpa only [List.mem_cons, hx, false_or] using same x

private theorem below_complement {B : Type u} [BooleanAlgebra B] {b x : B}
    (h : b ⊓ x = ⊥) : b ≤ xᶜ := by
  calc
    b = b ⊓ ⊤ := (inf_top_eq _).symm
    _ = b ⊓ (x ⊔ xᶜ) := congrArg (b ⊓ ·) (le_antisymm (BooleanAlgebra.top_le_sup_compl x) le_top)
    _ = (b ⊓ x) ⊔ (b ⊓ xᶜ) := inf_sup_left .. 
    _ ≤ xᶜ := sup_le (h ▸ bot_le) inf_le_right

private def piece {B : Type u} [BooleanAlgebra B] [∀ p : Prop, Decidable p] : List B → B
  | [] => ⊤
  | x :: l => let b := piece l; if b ⊓ x = ⊥ then b else b ⊓ x

private theorem piece_invariants {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    [∀ p : Prop, Decidable p] (l : List B) :
    piece l ≠ ⊥ ∧ ∀ x ∈ l, piece l ≤ x ∨ piece l ≤ xᶜ := by
  induction l with
  | nil => exact ⟨top_ne_bot,fun _ h => (List.not_mem_nil h).elim⟩
  | cons a l ih =>
    change (if piece l ⊓ a = ⊥ then piece l else piece l ⊓ a) ≠ ⊥ ∧ _
    by_cases h : piece l ⊓ a = ⊥
    · simp only [piece, ite_eq_left h]
      refine ⟨ih.1, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact Or.inr (below_complement h)
      · exact ih.2 x hxl
    · simp only [piece, ite_eq_right h]
      refine ⟨h, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact Or.inl inf_le_right
      · exact (ih.2 x hxl).imp (le_trans inf_le_left) (le_trans inf_le_left)

theorem boolean_of_fine_order {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    [∀ p : Prop, Decidable p] {U : (Sample B → Prop) → Prop} (F : Fine U)
    {r : B → B → Prop} (o : StrictOn (fun _ => True) r) : BooleanPoint B := by
  let atSample := fun (s : Sample B) (x : B) => ∃ l, Listing r s l ∧ piece l ≤ x
  have eval (s : Sample B) : ∃ b : B, b ≠ ⊥ ∧ (∀ x ∈ s, b ≤ x ∨ b ≤ xᶜ) ∧
      ∀ x, atSample s x ↔ b ≤ x := by
    obtain ⟨l,hl⟩ := listing_exists o s
    have inv := piece_invariants l
    refine ⟨piece l, inv.1, fun x hx => inv.2 x ((hl.1 x).mp hx), fun x => ⟨?_,?_⟩⟩
    · rintro ⟨w,hw,hx⟩
      have eq := listing_unique o hw.2 hl.2 (fun y => (hw.1 y).symm.trans (hl.1 y))
      exact eq ▸ hx
    · exact fun h => ⟨l,hl,h⟩
  let truth := fun x => U (atSample · x)
  have botF (s : Sample B) : ¬ atSample s ⊥ := by
    obtain ⟨b,hb,_,hs⟩ := eval s
    exact fun h => hb (le_bot_iff.mp ((hs _).mp h))
  have topT (s : Sample B) : atSample s ⊤ := by
    obtain ⟨_,_,_,hs⟩ := eval s
    exact (hs _).mpr le_top
  have meet (s : Sample B) (x y : B) :
      atSample s (x ⊓ y) ↔ atSample s x ∧ atSample s y := by
    obtain ⟨_,_,_,hs⟩ := eval s
    rw [hs, hs, hs, le_inf_iff]
  have complement (s : Sample B) (x : B) (hx : x ∈ s) :
      atSample s xᶜ ↔ ¬ atSample s x := by
    obtain ⟨b,hb,dec,hs⟩ := eval s
    rw [hs, hs]
    constructor
    · intro h₁ h₂
      apply hb
      have h := le_inf h₂ h₁
      exact le_bot_iff.mp (le_trans h (BooleanAlgebra.inf_compl_le_bot x))
    · exact (dec _ hx).resolve_left
  have neg (x : B) : truth xᶜ ↔ ¬ truth x := by
    constructor
    · intro hn hp
      exact F.proper (F.mono (fun s h => ((complement s x h.1).mp h.2.1) h.2.2)
        (F.inter (F.cone x) (F.inter hn hp)))
    · intro h
      rcases F.decide (atSample · x) with yes | no
      · exact (h yes).elim
      · exact F.mono (fun s hn => (complement s x hn.1).mpr hn.2) (F.inter (F.cone x) no)
  have conj (x y : B) : truth (x ⊓ y) ↔ truth x ∧ truth y := by
    constructor
    · intro h
      exact ⟨F.mono (fun s hs => ((meet s x y).mp hs).1) h,
        F.mono (fun s hs => ((meet s x y).mp hs).2) h⟩
    · exact fun h => F.mono (fun s => (meet s x y).mpr) (F.inter h.1 h.2)
  have yes : truth ⊤ := F.mono (fun s _ => topT s) (F.cone (⊤ : B))
  have no : ¬ truth ⊥ := fun h => F.proper (F.mono botF h)
  refine ⟨fun x => decide (truth x), by simp [no], by simp [yes], ?_, ?_⟩
  · intro x y
    by_cases hx : truth x <;> by_cases hy : truth y <;> simp [propext (conj x y), hx, hy]
  · intro x
    simp only [propext (neg x), decide_not]

def cones (T : Type u) : Filter (Sample T) where
  sets p := ∃ l : List T, ∀ s : Sample T, (∀ x ∈ l, x ∈ s) → p s
  univ_sets := ⟨[],fun _ _ => trivial⟩
  sets_of_superset := fun ⟨l,h⟩ h' => ⟨l,fun s hs => h' (h s hs)⟩
  inter_sets := fun ⟨l,hl⟩ ⟨w,hw⟩ => ⟨l ++ w, fun s hs =>
    ⟨hl s (fun x hx => hs x (List.mem_append_left _ hx)),
      hw s (fun x hx => hs x (List.mem_append_right _ hx))⟩⟩

abbrev germAlgebra {X : Type u} (f : Filter X) : BooleanAlgebra (f.Germ Bool) where
  __ := (inferInstance : DistribLattice (f.Germ Bool))
  __ := (inferInstance : BoundedOrder (f.Germ Bool))
  compl := Germ.map Bool.not
  inf_compl_le_bot g := by
    induction g using Germ.inductionOn with | h g =>
      apply Germ.coe_le.mpr
      exact Filter.Eventually.of_forall (fun s => show (g s && !(g s)) ≤ false by cases g s <;> decide)
  top_le_sup_compl g := by
    induction g using Germ.inductionOn with | h g =>
      apply Germ.coe_le.mpr
      exact Filter.Eventually.of_forall (fun s => show true ≤ (g s || !(g s)) by cases g s <;> decide)
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

theorem nontrivial_quotient (T : Type u) : Nontrivial ((cones T).Germ Bool) := by
  refine ⟨⟨Germ.const (l := cones T) false, Germ.const (l := cones T) true, ?_⟩⟩
  intro e
  have eventual : (fun _ : Sample T => false) =ᶠ[cones T] (fun _ => true) := Germ.coe_eq.mp e
  obtain ⟨l, h⟩ := eventual
  exact Bool.noConfusion (h (Sample.ofList l) (fun _ hx => hx))

private def germOf {T : Type u} [∀ p : Prop, Decidable p] (p : Sample T → Prop) :
    (cones T).Germ Bool := Germ.ofFun (fun s => decide (p s))

theorem quotient_fine (T : Type u) [∀ p : Prop, Decidable p]
    (bpi : @BooleanPoint ((cones T).Germ Bool) (germAlgebra _)) :
    ∃ U : (Sample T → Prop) → Prop, Fine U := by
  let _ := germAlgebra (cones T)
  obtain ⟨f,fb,ft,fi,fc⟩ := bpi
  have botEq : germOf (fun _ : Sample T => False) = ⊥ := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => by simp)
  have negEq (p : Sample T → Prop) : germOf (fun s => ¬ p s) = (germOf p)ᶜ := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun s => show decide (¬ p s) = !(decide (p s)) by simp)
  have meetEq (p q : Sample T → Prop) :
      germOf (fun s => p s ∧ q s) = germOf p ⊓ germOf q := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun s => show decide (p s ∧ q s) = (decide (p s) && decide (q s)) by
      by_cases hp : p s <;> by_cases hq : q s <;> simp [hp, hq])
  refine ⟨fun p => f (germOf p) = true, ?_⟩
  constructor
  · rw [botEq, fb]
    exact Bool.noConfusion
  · intro p q h hfp
    have ee : (fun s => p s ∧ q s) = p := funext (fun s => propext ⟨And.left,fun hs => ⟨hs,h s hs⟩⟩)
    have hv := fi (germOf p) (germOf q)
    rw [← meetEq, ee, hfp, Bool.true_and] at hv
    exact hv.symm
  · intro p q hp hq
    rw [meetEq, fi, hp, hq]
    rfl
  · intro p
    by_cases hp : f (germOf p) = true
    · exact Or.inl hp
    · exact Or.inr (by rw [negEq, fc, Bool.eq_false_iff.mpr hp]; rfl)
  · intro x
    have coneEq : germOf (fun s : Sample T => x ∈ s) = ⊤ := by
      apply Germ.coe_eq.mpr
      refine ⟨[x], fun s h => ?_⟩
      change decide (x ∈ s) = true
      exact decide_eq_true (h x List.mem_cons_self)
    rw [coneEq, ft]

private def EarlierBit {A : Type u} (r : A → A → Prop) (s : Sample A)
    (p q : A → Prop) : Prop :=
  ∃ t ∈ s, ¬ p t ∧ q t ∧ ∀ z ∈ s, r z t → (p z ↔ q z)

private theorem earliest {A : Type u} [∀ p : Prop, Decidable p]
    {D : A → Prop} {r : A → A → Prop} (o : StrictOn D r)
    (s : Sample A) (p : A → Prop) (hp : ∀ x, p x → D x)
    (hne : ∃ x ∈ s, p x) :
    ∃ t ∈ s, p t ∧ ∀ z ∈ s, p z → ¬ r z t := by
  induction s using Sample.induction with
  | empty => obtain ⟨_, h, _⟩ := hne; exact False.elim (List.not_mem_nil h)
  | step a s ih =>
    by_cases hex : ∃ x ∈ s, p x
    · obtain ⟨t, ht, hpt, hmin⟩ := ih hex
      by_cases hnew : p a ∧ r a t
      · refine ⟨a, Or.inl rfl, hnew.1, ?_⟩
        intro z hz hpz hza
        rcases Sample.mem_adjoin.mp hz with rfl | hzs
        · exact o.irrefl _ (hp _ hpz) hza
        · exact hmin z hzs hpz (o.trans (hp _ hpz) (hp _ hnew.1) (hp _ hpt) hza hnew.2)
      · refine ⟨t, Or.inr ht, hpt, ?_⟩
        intro z hz hpz hzt
        rcases Sample.mem_adjoin.mp hz with rfl | hzs
        · exact hnew ⟨hpz, hzt⟩
        · exact hmin z hzs hpz hzt
    · obtain ⟨t, ht, hpt⟩ := hne
      rcases Sample.mem_adjoin.mp ht with rfl | hts
      · refine ⟨t, Or.inl rfl, hpt, ?_⟩
        intro z hz hpz hzt
        rcases Sample.mem_adjoin.mp hz with rfl | hzs
        · exact o.irrefl _ (hp _ hpz) hzt
        · exact hex ⟨z, hzs, hpz⟩
      · exact False.elim (hex ⟨t, hts, hpt⟩)

private theorem bit_compare {A : Type u} [∀ p : Prop, Decidable p]
    {D : A → Prop} {r : A → A → Prop} (o : StrictOn D r)
    {p q : A → Prop} {s : Sample A}
    (hd : ∀ x, ¬ (p x ↔ q x) → D x) (hne : ∃ x ∈ s, ¬ (p x ↔ q x)) :
    EarlierBit r s p q ∨ EarlierBit r s q p := by
  obtain ⟨t, ht, hdiff, hmin⟩ := earliest o s (fun x => ¬ (p x ↔ q x)) hd hne
  have before : ∀ z ∈ s, r z t → (p z ↔ q z) := by
    intro z hz hzt
    apply Decidable.byContradiction
    intro hn
    exact hmin z hz hn hzt
  by_cases hp : p t
  · right
    refine ⟨t, ht, ?_, hp, fun z hz hzt => (before z hz hzt).symm⟩
    exact fun hq => hdiff ⟨fun _ => hq, fun _ => hp⟩
  · left
    refine ⟨t, ht, hp, ?_, before⟩
    apply Decidable.byContradiction
    intro hq
    exact hdiff ⟨fun h => (hp h).elim, fun h => (hq h).elim⟩

private theorem bit_trans {A : Type u} [∀ p : Prop, Decidable p]
    {D : A → Prop} {r : A → A → Prop} (o : StrictOn D r)
    {p q v : A → Prop} {s : Sample A}
    (hp : ∀ x, p x → D x) (hq : ∀ x, q x → D x) (hv : ∀ x, v x → D x)
    (h₁ : EarlierBit r s p q) (h₂ : EarlierBit r s q v) : EarlierBit r s p v := by
  obtain ⟨a, ha, hpa, hqa, ab⟩ := h₁
  obtain ⟨b, hb, hqb, hvb, bb⟩ := h₂
  have hne : a ≠ b := fun h => hqb (h ▸ hqa)
  rcases o.compare (hq a hqa) (hv b hvb) hne with hab | hba
  · refine ⟨a, ha, hpa, (bb a ha hab).mp hqa, ?_⟩
    intro z hz hza
    by_cases hzd : D z
    · exact (ab z hz hza).trans (bb z hz (o.trans hzd (hq a hqa) (hv b hvb) hza hab))
    · exact ⟨fun hpz => (hzd (hq _ ((ab z hz hza).mp hpz))).elim,
        fun hvz => (hzd (hv _ hvz)).elim⟩
  · refine ⟨b, hb, fun hpb => hqb ((ab b hb hba).mp hpb), hvb, ?_⟩
    intro z hz hzb
    by_cases hzd : D z
    · exact (ab z hz (o.trans hzd (hv b hvb) (hq a hqa) hzb hba)).trans (bb z hz hzb)
    · exact ⟨fun hpz => (hzd (hp _ hpz)).elim, fun hvz => (hzd (hv _ hvz)).elim⟩

structure Tagged (A : Type u) (I : Type v) [LT I] (K : Type w) where
  rank : A → I
  mem : A → A → Prop
  lower : ∀ {t x}, mem t x → rank t < rank x
  tag : A → K
  ext : ∀ {x y}, tag x = tag y → (∀ t, mem t x ↔ mem t y) → x = y

private def byKey {A : Type u} {K : Type w} (key : A → K) (r : K → K → Prop)
    (s : A → A → Prop) (x y : A) : Prop := r (key x) (key y) ∨ (key x = key y ∧ s x y)

private theorem byKey_strict {A : Type u} {K : Type w} [∀ p : Prop, Decidable p]
    (D : A → Prop) (key : A → K) {r : K → K → Prop} (rk : StrictOn (fun _ => True) r)
    {s : A → A → Prop} (hs : ∀ k, StrictOn (fun x => D x ∧ key x = k) s) :
    StrictOn D (byKey key r s) := by
  constructor
  · rintro x hx (h | ⟨_,h⟩)
    · exact rk.irrefl _ trivial h
    · exact (hs _).irrefl x ⟨hx,rfl⟩ h
  · rintro x y z hx hy hz (hxy | ⟨exy,hxy⟩) (hyz | ⟨eyz,hyz⟩)
    · exact Or.inl (rk.trans trivial trivial trivial hxy hyz)
    · exact Or.inl (eyz ▸ hxy)
    · exact Or.inl (exy ▸ hyz)
    · exact Or.inr ⟨exy.trans eyz,
        (hs _).trans ⟨hx,rfl⟩ ⟨hy,exy.symm⟩ ⟨hz,(exy.trans eyz).symm⟩ hxy hyz⟩
  · intro x y hx hy hn
    by_cases e : key x = key y
    · rcases (hs _).compare ⟨hx,rfl⟩ ⟨hy,e.symm⟩ hn with h | h
      · exact Or.inl (Or.inr ⟨e,h⟩)
      · exact Or.inr (Or.inr ⟨e.symm,h⟩)
    · exact (rk.compare trivial trivial e).imp Or.inl Or.inl

private def stack {A : Type u} {I : Type v} [LT I] (rank : A → I) (D : I → Prop)
    (rec : ∀ j, D j → A → A → Prop) : A → A → Prop :=
  byKey rank (· < ·) (fun x y => ∃ h, rec (rank x) h x y)

private theorem stack_strict {A : Type u} {I : Type v} [LinearOrder I] [∀ p : Prop, Decidable p]
    (rank : A → I) (D : I → Prop) (rec : ∀ j, D j → A → A → Prop)
    (ok : ∀ j h, StrictOn (fun x => rank x = j) (rec j h)) :
    StrictOn (fun x => D (rank x)) (stack rank D rec) := by
  apply byKey_strict _ _ (r := (· < ·))
    ⟨fun _ _ => lt_irrefl _, fun _ _ _ => lt_trans, fun _ _ hn => lt_or_gt_of_ne hn⟩
  intro i
  constructor
  · rintro x ⟨hx,_⟩ ⟨_,h⟩
    exact (ok _ hx).irrefl x rfl h
  · rintro x y z ⟨hx,hxi⟩ ⟨hy,hyi⟩ ⟨_,hzi⟩ ⟨_,hxy⟩ ⟨_,hyz⟩
    have eq := hyi.trans hxi.symm
    have hyz' : rec (rank x) hx y z :=
      eq.rec (motive := fun j _ => ∀ hj, rec j hj y z) (fun _ => hyz) hx
    exact ⟨hx,(ok _ hx).trans rfl eq (hzi.trans hxi.symm) hxy hyz'⟩
  · rintro x y ⟨hx,hxi⟩ ⟨hy,hyi⟩ hn
    have eq := hxi.trans hyi.symm
    rcases (ok _ hx).compare rfl eq.symm hn with h | h
    · exact Or.inl ⟨hx,h⟩
    · exact Or.inr ⟨hy,eq.rec (motive := fun j _ => ∀ hj, rec j hj y x) (fun _ => h) hy⟩

private def layer {A : Type u} {I : Type v} {K : Type w} [LinearOrder I] [WellFoundedLT I]
    (H : Tagged A I K) (r : K → K → Prop) (U : (Sample A → Prop) → Prop) (i : I) : A → A → Prop :=
  wellFounded_lt.fix (C := fun _ => A → A → Prop) (fun j rec =>
    byKey H.tag r (fun x y => U (fun s => EarlierBit (stack H.rank (· < j) rec) s (H.mem · x) (H.mem · y)))) i

private theorem layer_eq {A : Type u} {I : Type v} {K : Type w} [LinearOrder I] [WellFoundedLT I]
    (H : Tagged A I K) (r : K → K → Prop) (U : (Sample A → Prop) → Prop) (i : I) :
    layer H r U i = byKey H.tag r (fun x y => U (fun s => EarlierBit
      (stack H.rank (· < i) (fun j _ => layer H r U j)) s (H.mem · x) (H.mem · y))) := by
  unfold layer
  rw [WellFounded.fix_eq]

private theorem Fine.disj {A : Type u} {U : (Sample A → Prop) → Prop}
    (F : Fine U) {p q : Sample A → Prop} (h : U (fun s => p s ∨ q s)) : U p ∨ U q := by
  rcases F.decide p with yes | no
  · exact Or.inl yes
  · exact Or.inr (F.mono (fun _ h => h.1.resolve_left h.2) (F.inter h no))

private theorem layer_strict {A : Type u} {I : Type v} {K : Type w} [LinearOrder I]
    [WellFoundedLT I] [∀ p : Prop, Decidable p] (H : Tagged A I K)
    {r : K → K → Prop} (rk : StrictOn (fun _ => True) r) {U : (Sample A → Prop) → Prop}
    (F : Fine U) (i : I) : StrictOn (fun x => H.rank x = i) (layer H r U i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have o := stack_strict H.rank (· < i) (fun j _ => layer H r U j) ih
    have mem_lower {x : A} (hx : H.rank x = i) (t : A) (h : H.mem t x) : H.rank t < i :=
      hx ▸ H.lower h
    rw [layer_eq]
    apply byKey_strict _ _ rk
    intro k
    constructor
    · intro x _ h
      exact F.proper (F.mono (fun _ ⟨_, _, h₁, h₂, _⟩ => h₁ h₂) h)
    · intro x y z hx hy hz hxy hyz
      exact F.mono (fun _ h => bit_trans o (mem_lower hx.1) (mem_lower hy.1) (mem_lower hz.1) h.1 h.2)
        (F.inter hxy hyz)
    · intro x y hx hy hn
      have witness : ∃ t, ¬ (H.mem t x ↔ H.mem t y) := by
        apply Decidable.byContradiction
        intro h
        apply hn
        apply H.ext (hx.2.trans hy.2.symm)
        intro t
        apply Decidable.byContradiction
        intro h'
        exact h ⟨t, h'⟩
      obtain ⟨t, ht⟩ := witness
      have hdiff (z : A) (hz : ¬ (H.mem z x ↔ H.mem z y)) : H.rank z < i := by
        by_cases hh : H.mem z x
        · exact mem_lower hx.1 z hh
        · by_cases hh' : H.mem z y
          · exact mem_lower hy.1 z hh'
          · exact (hz ⟨fun h => (hh h).elim, fun h => (hh' h).elim⟩).elim
      exact F.disj (F.mono (fun s hs => bit_compare o hdiff ⟨t, hs, ht⟩) (F.cone t))

theorem tagged_order {A : Type u} {I : Type v} {K : Type w} [LinearOrder I]
    [WellFoundedLT I] [∀ p : Prop, Decidable p] (H : Tagged A I K)
    {r : K → K → Prop} (rk : StrictOn (fun _ => True) r) {U : (Sample A → Prop) → Prop}
    (F : Fine U) : ∃ s : A → A → Prop, StrictOn (fun _ => True) s := by
  exact ⟨stack H.rank (fun _ => True) (fun j _ => layer H r U j),
    stack_strict H.rank (fun _ => True) _ (fun j _ => layer_strict H rk F j)⟩

abbrev Comparisons (A : Type u) := A × A → Bool

def orderFilter (A : Type u) : Filter (Comparisons A) where
  sets p := ∃ l : List A, ∀ c : Comparisons A, StrictOn (· ∈ l) (fun x y => c (x,y) = true) → p c
  univ_sets := ⟨[],fun _ _ => trivial⟩
  sets_of_superset := fun ⟨l,hl⟩ h => ⟨l,fun c hc => h (hl c hc)⟩
  inter_sets := by
    rintro p q ⟨l, hl⟩ ⟨w,hw⟩
    refine ⟨l ++ w, fun c hc => ⟨hl c ?_, hw c ?_⟩⟩
    · have inc (x : A) := @List.mem_append_left A x l w
      exact ⟨fun x hx => hc.irrefl x (inc _ hx),
        fun hx hy hz => hc.trans (inc _ hx) (inc _ hy) (inc _ hz),
        fun hx hy => hc.compare (inc _ hx) (inc _ hy)⟩
    · have inc (x : A) := @List.mem_append_right A x l w
      exact ⟨fun x hx => hc.irrefl x (inc _ hx),
        fun hx hy hz => hc.trans (inc _ hx) (inc _ hy) (inc _ hz),
        fun hx hy => hc.compare (inc _ hx) (inc _ hy)⟩

theorem firstIndex_injective {A : Type u} [∀ p : Prop, Decidable p] (l : List A)
    {x y : A} (hx : x ∈ l) (eq : l.idxOf x = l.idxOf y) : x = y := by
  let i : Fin l.length := ⟨l.idxOf x, List.idxOf_lt_length_of_mem hx⟩
  let j : Fin l.length := ⟨l.idxOf y, eq ▸ i.isLt⟩
  exact (List.getElem_idxOf i.isLt).symm.trans
    ((congrArg l.get (show i = j from Fin.ext eq)).trans (List.getElem_idxOf j.isLt))

theorem comparison_quotient_nontrivial (A : Type u) [∀ p : Prop, Decidable p] :
    Nontrivial ((orderFilter A).Germ Bool) := by
  let F := orderFilter A
  refine ⟨⟨Germ.const (l := F) false, Germ.const (l := F) true, ?_⟩⟩
  intro eq
  have ev : (fun _ : Comparisons A => false) =ᶠ[F] (fun _ => true) := Germ.coe_eq.mp eq
  obtain ⟨l,hl⟩ := ev
  let c := fun xy : A × A => decide (l.idxOf xy.1 < l.idxOf xy.2)
  apply Bool.noConfusion (hl c ?_)
  refine ⟨fun _ _ h => (lt_irrefl _) (of_decide_eq_true h), ?_, ?_⟩
  · intro x y z _ _ _ hxy hyz
    exact decide_eq_true (Nat.lt_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))
  · intro x y hx _ hn
    have e : l.idxOf x ≠ l.idxOf y := fun h => hn (firstIndex_injective l hx h)
    exact (lt_or_gt_of_ne e).imp decide_eq_true decide_eq_true

theorem order_from_comparison_point (A : Type u) [∀ p : Prop, Decidable p]
    (point : @BooleanPoint ((orderFilter A).Germ Bool) (germAlgebra _)) :
    ∃ r : A → A → Prop, StrictOn (fun _ => True) r := by
  let F := orderFilter A
  let _ := germAlgebra F
  obtain ⟨f,fb,_,fi,fc⟩ := point
  let val := fun p : Comparisons A → Bool => f (Germ.ofFun (l := F) p)
  have mono (p q : Comparisons A → Bool) (h : ∀ᶠ c in F, p c = true → q c = true) :
      val p = true → val q = true := by
    intro hp
    have eq : Germ.ofFun (l := F) p ⊓ Germ.ofFun q = Germ.ofFun p := by
      apply Germ.coe_eq.mpr
      refine h.mono (fun c hc => ?_)
      change (p c && q c) = p c
      cases ep : p c with
      | false => rfl
      | true => rw [hc ep]; rfl
    have hm := fi (Germ.ofFun p) (Germ.ofFun q)
    change f (Germ.ofFun p ⊓ Germ.ofFun q) = (val p && val q) at hm
    rw [eq, show f (Germ.ofFun p) = true from hp, hp, Bool.true_and] at hm
    exact hm.symm
  let ev := fun x y (c : Comparisons A) => c (x,y)
  refine ⟨fun x y => val (ev x y) = true, ?_, ?_, ?_⟩
  · intro x _ h
    apply Bool.noConfusion ((fb.symm.trans ?_) : false = true)
    apply mono (ev x x) (fun _ => false) _ h
    exact ⟨[x],fun _ ho hx => (ho.irrefl x List.mem_cons_self hx).elim⟩
  · intro x y z _ _ _ hxy hyz
    let xy_yz := fun c => ev x y c && ev y z c
    have hh := fi (Germ.ofFun (ev x y)) (Germ.ofFun (ev y z))
    change val xy_yz = (val (ev x y) && val (ev y z)) at hh
    apply mono xy_yz (ev x z) _ (by rw [hh, hxy, hyz]; rfl)
    exact ⟨[x,y,z],fun _ ho h => ho.trans (x := x) (y := y) (z := z) (by simp) (by simp) (by simp)
      (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2⟩
  · intro x y _ _ hn
    by_cases h : val (ev x y) = true
    · exact Or.inl h
    · right
      let neg := fun c => !(ev x y c)
      have hneg := fc (Germ.ofFun (ev x y))
      change val neg = !(val (ev x y)) at hneg
      apply mono neg (ev y x) _ (by rw [hneg, Bool.eq_false_iff.mpr h]; rfl)
      refine ⟨[x,y],fun c ho hnxy => ?_⟩
      rcases ho.compare (by simp) (by simp) hn with hxy | hyx
      · change (!(c (x,y))) = true at hnxy
        simp [hxy] at hnxy
      · exact hyx

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
