module

public import SolvedProblems.RadoModel

@[expose] public section

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
