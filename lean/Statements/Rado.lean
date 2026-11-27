module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.SetTheory.ZFC.VonNeumann

@[expose] public section

namespace RadoSelection

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

/-- Finite induction into propositions never selects a listing as a function of s. -/
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

/-- An extensional transitive membership system equipped with decreasing ranks.
Every member of a point of the system is represented by another point of the system. -/
structure Hierarchy (A : Type u) (I : Type v) [LT I] where
  rank : A → I
  mem : A → A → Prop
  lower : ∀ {t x}, mem t x → rank t < rank x
  ext : ∀ {x y}, (∀ t, mem t x ↔ mem t y) → x = y

end RadoSelection

namespace RadoSelection

universe u v

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

def Selection : Prop := ∀ (J : Type u) (A : J → Type v), RadoOn J A

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

/-- The global choice is the graph of the unique label whose cell is large.
The finite answer hypothesis gives existence; the disjointness gives uniqueness. -/
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

/-- Project the dummy queries in a finite query domain to the underlying point sample. -/
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

/-- Request finitely many subset queries and point-cone queries at once. -/
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

theorem fine_of_selection {T : Type u} [∀ p : Prop, Decidable p]
    (rl : Selection.{u,v}) : ∃ U : (Sample T → Prop) → Prop, Fine U :=
  fine_of_queries (rl _ _)

/-- Rado selection is equivalent to fine ultrafilters on unordered finite subsets,
at every index universe and every answer universe. Only classical logic is used. -/
theorem selection_iff_fine [∀ p : Prop, Decidable p] :
    Selection.{u,v} ↔ ∀ T : Type u, ∃ U : (Sample T → Prop) → Prop, Fine U := by
  constructor
  · exact fun rl _ => fine_of_selection rl
  · intro fine J A
    obtain ⟨_,F⟩ := fine J
    exact F.rado A

end RadoSelection

namespace RadoSelection

/-- Compare two incidence words on the finite sample at their first difference. -/
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

/-- Incidence words which differ on the sample compare in one direction. -/
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

/-- Put the previously constructed layer orders end to end, below the current rank. -/
private def below {A : Type u} {I : Type v} [LT I] (H : Hierarchy A I) (i : I)
    (rec : ∀ j, j < i → A → A → Prop) (x y : A) : Prop :=
  H.rank x < H.rank y ∨ ∃ hx : H.rank x < i, H.rank x = H.rank y ∧ rec (H.rank x) hx x y

private theorem below_strict {A : Type u} {I : Type v} [LinearOrder I]
    (H : Hierarchy A I) (i : I) (rec : ∀ j, j < i → A → A → Prop)
    (hrec : ∀ j h, StrictOn (fun x => H.rank x = j) (rec j h)) :
    StrictOn (fun x => H.rank x < i) (below H i rec) := by
  constructor
  · rintro x _ (h | ⟨hx, _, h⟩)
    · exact lt_irrefl _ h
    · exact (hrec _ hx).irrefl x rfl h
  · rintro x y z hx _ _ (hxy | ⟨_, exy, hxy⟩) (hyz | ⟨_, eyz, hyz⟩)
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl (eyz ▸ hxy)
    · exact Or.inl (exy ▸ hyz)
    · refine Or.inr ⟨hx, exy.trans eyz, ?_⟩
      have hyz' : rec (H.rank x) hx y z := exy.symm.rec (motive := fun j _ => ∀ hj, rec j hj y z) (fun _ => hyz) hx
      exact (hrec _ hx).trans rfl exy.symm (exy.trans eyz).symm hxy hyz'
  · intro x y hx hy hn
    rcases lt_trichotomy (H.rank x) (H.rank y) with h | e | h
    · exact Or.inl (Or.inl h)
    · rcases (hrec _ hx).compare rfl e.symm hn with h | h
      · exact Or.inl (Or.inr ⟨hx, e, h⟩)
      · refine Or.inr (Or.inr ⟨hy, e.symm, ?_⟩)
        exact e.rec (motive := fun j _ => ∀ hj, rec j hj y x) (fun _ => h) hy
    · exact Or.inr (Or.inl h)

private def layer {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    (H : Hierarchy A I) (U : (Sample A → Prop) → Prop) (i : I) : A → A → Prop :=
  wellFounded_lt.fix (C := fun _ => A → A → Prop) (fun j rec x y =>
    U (fun s => EarlierBit (below H j rec) s (H.mem · x) (H.mem · y))) i

private theorem layer_eq {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    (H : Hierarchy A I) (U : (Sample A → Prop) → Prop) (i : I) (x y : A) :
    layer H U i x y ↔ U (fun s => EarlierBit
      (below H i (fun j _ => layer H U j)) s (H.mem · x) (H.mem · y)) := by
  unfold layer
  rw [WellFounded.fix_eq]

private theorem Fine.disj {A : Type u} {U : (Sample A → Prop) → Prop}
    (F : Fine U) {p q : Sample A → Prop} (h : U (fun s => p s ∨ q s)) : U p ∨ U q := by
  rcases F.decide p with yes | no
  · exact Or.inl yes
  · exact Or.inr (F.mono (fun _ h => h.1.resolve_left h.2) (F.inter h no))

private theorem layer_strict {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    [∀ p : Prop, Decidable p] (H : Hierarchy A I) {U : (Sample A → Prop) → Prop}
    (F : Fine U) (i : I) : StrictOn (fun x => H.rank x = i) (layer H U i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have o := below_strict H i (fun j _ => layer H U j) ih
    have mem_lower {x : A} (hx : H.rank x = i) (t : A) (h : H.mem t x) : H.rank t < i :=
      hx ▸ H.lower h
    constructor
    · intro x _ h
      have h' := (layer_eq H U i x x).mp h
      exact F.proper (F.mono (fun _ ⟨_, _, h₁, h₂, _⟩ => h₁ h₂) h')
    · intro x y z hx hy hz hxy hyz
      apply (layer_eq H U i x z).mpr
      exact F.mono (fun _ h => bit_trans o (mem_lower hx) (mem_lower hy) (mem_lower hz) h.1 h.2)
        (F.inter ((layer_eq H U i x y).mp hxy) ((layer_eq H U i y z).mp hyz))
    · intro x y hx hy hn
      have witness : ∃ t, ¬ (H.mem t x ↔ H.mem t y) := by
        apply Decidable.byContradiction
        intro h
        apply hn
        apply H.ext
        intro t
        apply Decidable.byContradiction
        intro h'
        exact h ⟨t, h'⟩
      obtain ⟨t, ht⟩ := witness
      have hdiff (z : A) (hz : ¬ (H.mem z x ↔ H.mem z y)) : H.rank z < i := by
        by_cases hh : H.mem z x
        · exact mem_lower hx z hh
        · by_cases hh' : H.mem z y
          · exact mem_lower hy z hh'
          · exact (hz ⟨fun h => (hh h).elim, fun h => (hh' h).elim⟩).elim
      have h := F.disj (F.mono (fun s hs => bit_compare o hdiff ⟨t, hs, ht⟩) (F.cone t))
      exact h.imp (layer_eq H U i x y).mpr (layer_eq H U i y x).mpr

/-- A single fine ultrafilter on unordered finite subsets orders a pure transitive
membership hierarchy. The relation is defined by recursion on its given well-founded
ranks. The only logical input is decidability of propositions (classical logic). -/
theorem order_from_fine {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    [∀ p : Prop, Decidable p] (H : Hierarchy A I) {U : (Sample A → Prop) → Prop}
    (F : Fine U) : ∃ r : A → A → Prop, StrictOn (fun _ => True) r := by
  let r := fun x y => H.rank x < H.rank y ∨
    (H.rank x = H.rank y ∧ layer H U (H.rank x) x y)
  refine ⟨r, ?_, ?_, ?_⟩
  · rintro x _ (h | ⟨_, h⟩)
    · exact lt_irrefl _ h
    · exact (layer_strict H F _).irrefl x rfl h
  · rintro x y z _ _ _ (hxy | ⟨exy, hxy⟩) (hyz | ⟨eyz, hyz⟩)
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl (eyz ▸ hxy)
    · exact Or.inl (exy ▸ hyz)
    · refine Or.inr ⟨exy.trans eyz, ?_⟩
      have hyz' : layer H U (H.rank x) y z := exy ▸ hyz
      exact (layer_strict H F _).trans rfl exy.symm (exy.trans eyz).symm hxy hyz'
  · intro x y _ _ hn
    rcases lt_trichotomy (H.rank x) (H.rank y) with h | e | h
    · exact Or.inl (Or.inl h)
    · rcases (layer_strict H F _).compare rfl e.symm hn with h | h
      · exact Or.inl (Or.inr ⟨e, h⟩)
      · exact Or.inr (Or.inr ⟨e.symm, e ▸ h⟩)
    · exact Or.inr (Or.inl h)

end RadoSelection

namespace RadoSelection

-- Use the Boolean algebra’s given lattice and bounds directly.
attribute [-instance] BooleanAlgebra.toBiheytingAlgebra BooleanAlgebra.toGeneralizedBooleanAlgebra

/-- A homomorphism to the two-element Boolean algebra, given on the standard
generators of the Boolean signature (join then follows by De Morgan). -/
def BooleanPoint (B : Type u) [BooleanAlgebra B] : Prop :=
  ∃ f : B → Bool, f ⊥ = false ∧ f ⊤ = true ∧
    (∀ x y, f (x ⊓ y) = (f x && f y)) ∧ ∀ x, f xᶜ = !(f x)

/-- Increasing listings of one unordered sample. Existence and uniqueness below
enable a definition of the local truth value by a formula, without making choices. -/
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

/-- Greedily retain a nonzero cell of the generating literals along the unique
ordered listing. A zero intersection leaves the previous cell below the complement. -/
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

private theorem fine_boolean {B : Type u} [BooleanAlgebra B] [Nontrivial B]
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

/-- Pull an unordered finite sample back along an injection. The proof of
finiteness enumerates its finite preimage one point at a time, inside Prop. -/
private def preimage {A : Type u} {B : Type v} [∀ p : Prop, Decidable p]
    (e : B → A) (hi : Function.Injective e) (s : Sample A) : Sample B where
  contains x := e x ∈ s
  finite := by
    induction s using Sample.induction with
    | empty => exact ⟨[], fun x => ⟨fun h => (List.not_mem_nil h).elim,
          fun h => (List.not_mem_nil h).elim⟩⟩
    | step a s ih =>
      obtain ⟨l,hl⟩ := ih
      by_cases h : ∃ b, e b = a
      · obtain ⟨b,rfl⟩ := h
        exact ⟨b :: l, fun x => (or_congr hi.eq_iff (hl x)).trans List.mem_cons.symm⟩
      · refine ⟨l, fun x => (or_iff_right_of_imp ?_).trans (hl x)⟩
        exact fun hx => (h ⟨x,hx⟩).elim

/-- The local implication over a pure transitive hierarchy: every nontrivial
Boolean algebra whose carrier is included in the hierarchy has a two-valued
homomorphism, using just the given fine ultrafilter on the hierarchy. -/
theorem boolean_from_fine {T : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    [∀ p : Prop, Decidable p] (H : Hierarchy T I) {U : (Sample T → Prop) → Prop}
    (F : Fine U) (B : Type w) [BooleanAlgebra B] [Nontrivial B]
    (e : B → T) (hi : Function.Injective e) : BooleanPoint B := by
  obtain ⟨r,o⟩ := order_from_fine H F
  let rb := fun x y => r (e x) (e y)
  have ob : StrictOn (fun _ => True) rb :=
    ⟨fun x _ => o.irrefl (e x) trivial,
      fun _ _ _ => o.trans trivial trivial trivial,
      fun _ _ hn => o.compare trivial trivial (fun h => hn (hi h))⟩
  let V := fun (p : Sample B → Prop) => U (fun s => p (preimage e hi s))
  have G : Fine V := {
    proper := F.proper
    mono := fun h => F.mono (fun s => h (preimage e hi s))
    inter := F.inter
    decide := fun p => F.decide (fun s => p (preimage e hi s))
    cone := fun x => F.cone (e x) }
  exact fine_boolean G ob

end RadoSelection

namespace RadoSelection
open Filter

universe u v

attribute [-instance] BooleanAlgebra.toBiheytingAlgebra BooleanAlgebra.toGeneralizedBooleanAlgebra

/-- The Boolean prime ideal theorem in its two-valued homomorphism formulation. -/
def BooleanPrime : Prop :=
  ∀ (B : Type u) [BooleanAlgebra B] [Nontrivial B], BooleanPoint B

/-- A predicate is large in the cone filter when all samples containing one
finite list of requirements satisfy it. The list is only a witness in Prop. -/
def cones (T : Type u) : Filter (Sample T) where
  sets p := ∃ l : List T, ∀ s : Sample T, (∀ x ∈ l, x ∈ s) → p s
  univ_sets := ⟨[],fun _ _ => trivial⟩
  sets_of_superset := fun ⟨l,h⟩ h' => ⟨l,fun s hs => h' (h s hs)⟩
  inter_sets := fun ⟨l,hl⟩ ⟨w,hw⟩ => ⟨l ++ w, fun s hs =>
    ⟨hl s (fun x hx => hs x (List.mem_append_left _ hx)),
      hw s (fun x hx => hs x (List.mem_append_right _ hx))⟩⟩

/-- Boolean operations on functions modulo eventual equality in the cone filter. -/
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

/-- BPI yields Rado selection over arbitrary sets, without a membership-hierarchy
assumption. The quotient Boolean algebra identifies predicates which agree on
some cone; its nontriviality is witnessed by that finite cone itself. -/
theorem selection_of_boolean [∀ p : Prop, Decidable p] (bpi : BooleanPrime.{u}) :
    Selection.{u,v} := selection_iff_fine.mpr (fun T =>
      quotient_fine T (@bpi _ (germAlgebra _) (nontrivial_quotient T)))

end RadoSelection

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

namespace RadoSelection

/-- Mathlib's material sets instantiate the rank, separation, power-set and
transitive-bound interface. The abstract equivalence already checks without choice. -/
noncomputable def vonNeumannUniverse : Material ZFSet.{u} Ordinal.{u} where
  rank := ZFSet.rank
  mem z x := z ∈ x
  lower := ZFSet.rank_lt_of_mem
  ext := ZFSet.ext
  empty := ∅
  empty_mem := ZFSet.notMem_empty
  add := insert
  add_mem := fun _ _ _ => ZFSet.mem_insert_iff
  join := (· ∪ ·)
  join_mem := fun _ _ _ => ZFSet.mem_union
  sep := fun s p => ZFSet.sep p s
  sep_mem := fun _ _ _ => ZFSet.mem_sep
  power := ZFSet.powerset
  power_mem := fun _ _ => ZFSet.mem_powerset
  transitive_bound b := ⟨ZFSet.vonNeumann b.rank,
    fun _ hx => ZFSet.subset_vonNeumann_self b hx,
    fun _ hx _ hz => ZFSet.isTransitive_vonNeumann _ _ hx hz⟩

/-- The two original principles specialized to carriers realized by Mathlib
pure sets. Families, their local choices, and the algebra are still arbitrary. -/
theorem pureSet_equivalence :
    vonNeumannUniverse.{u}.SelectionPrinciple ↔ vonNeumannUniverse.{u}.BooleanPrinciple := by
  classical
  exact vonNeumannUniverse.equivalence

end RadoSelection
