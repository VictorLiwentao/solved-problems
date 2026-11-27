module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.List.Pairwise
public import Mathlib.Tactic.Push
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace ChainWords

/-- An ascent is weak and a descent is strict. Injective vertex labels make the
two labels distinct on every cover and inside every linear extension. -/
def color {α : Type*} (label : α → ℕ) (x y : α) : Bool := decide (label x ≤ label y)

/-- The adjacent comparison word encodes exactly the descent set of a word. -/
def descWord {α : Type*} (label : α → ℕ) : List α → List Bool
  | x :: y :: l => color label x y :: descWord label (y :: l)
  | _ => []

theorem color_trans {α : Type*} (label : α → ℕ) {x y z : α} {b : Bool}
    (h : color label x y = b) (h' : color label y z = b) : color label x z = b := by
  cases b <;> simp [color] at * <;> omega

theorem color_split {α : Type*} (label : α → ℕ) (x y z : α) :
    color label x y = color label x z ∨ color label y z = color label x z := by
  by_cases h : color label x y = color label y z
  · exact Or.inl (color_trans label rfl h.symm).symm
  · cases h₁ : color label x y <;> cases h₂ : color label y z <;> cases h₃ : color label x z <;> simp_all

theorem desc_take {α : Type*} (label : α → ℕ) (n : ℕ) (l : List α) :
    descWord label (l.take n) = (descWord label l).take (n-1) := by
  induction n generalizing l with
  | zero => simp [descWord]
  | succ n ih =>
    cases n with
    | zero => cases l <;> simp [descWord]
    | succ n =>
      rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
      · simp [descWord]
      · simp [descWord]
      · simpa [descWord] using congrArg (List.cons (color label x y)) (ih (y :: l))

theorem desc_drop {α : Type*} (label : α → ℕ) (n : ℕ) (l : List α) :
    descWord label (l.drop n) = (descWord label l).drop n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp [descWord]
    · simp [descWord]
    · simpa [descWord] using ih (y :: l)

def Run {α : Type*} (label : α → ℕ) (b : Bool) (l : List α) : Prop :=
  l.Pairwise fun x y => color label x y = b

theorem run_iff {α : Type*} (label : α → ℕ) (b : Bool) (l : List α) :
    Run label b l ↔ ∀ s ∈ descWord label l, s = b := by
  induction l with
  | nil => simp [Run, descWord]
  | cons x l ih =>
    rcases l with _ | ⟨y, l⟩
    · simp [Run, descWord]
    · let _ : IsTrans α (fun x y => color label x y = b) := ⟨fun _ _ _ => color_trans label⟩
      change (x :: y :: l).Pairwise (fun x y => color label x y = b) ↔
        ∀ s ∈ color label x y :: descWord label (y :: l), s = b
      rw [List.pairwise_cons_cons_iff_of_trans, List.forall_mem_cons]
      exact and_congr Iff.rfl ih

inductive Cuts {α : Type*} (label : α → ℕ) : List Bool → List α → Prop where
  | nil : Cuts label [] []
  | cons {s l r b} : Run label b l → Cuts label s r → Cuts label (b :: s) (l ++ r)

/-- Block cuts depend only on the length and the descent set. Empty blocks are allowed. -/
theorem cuts_transfer {α β : Type*} {f : α → ℕ} {g : β → ℕ} {s l}
    (hc : Cuts f s l) (r : List β) (hn : l.length = r.length) (hd : descWord f l = descWord g r) :
    Cuts g s r := by
  induction hc generalizing r with
  | nil =>
    have hr : r = [] := List.length_eq_zero_iff.mp hn.symm
    subst r
    exact .nil
  | @cons s l t b hl ht ih =>
    have h₁ : descWord f l = descWord g (r.take l.length) := by
      rw [desc_take, ← hd, ← desc_take]
      simp
    have h₂ : descWord f t = descWord g (r.drop l.length) := by
      rw [desc_drop, ← hd, ← desc_drop]
      simp
    have hl' : Run g b (r.take l.length) := (run_iff ..).2 (h₁ ▸ (run_iff ..).1 hl)
    have ht' : Cuts g s (r.drop l.length) := ih _ (by simp at hn ⊢; omega) h₂
    simpa using Cuts.cons hl' ht'

/-- The descent set is indexed by the size of the poset, as in the homogeneous
fundamental basis. The list visits every vertex exactly once in a linear extension. -/
def IsExtension {α : Type*} [PartialOrder α] (D : Set α) (l : List α) : Prop :=
  l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ D) ∧ l.Pairwise (fun x y => ¬ y < x)

def fundamentalSupport {α : Type*} [PartialOrder α] (label : α → ℕ) : Set (ℕ × List Bool) :=
  {c | ∃ l : List α, IsExtension Set.univ l ∧ c = (l.length, descWord label l)}

/-- Ordered selected covers give exactly a subsequence of cover colors on a
saturated chain. The unselected segments are the intervals between successive covers. -/
def Above {α : Type*} [PartialOrder α] (label : α → ℕ) : List Bool → α → Prop
  | [], _ => True
  | c :: w, x => ∃ a b, x ≤ a ∧ a ⋖ b ∧ color label a b = c ∧ Above label w b

def language {α : Type*} [PartialOrder α] (label : α → ℕ) : Set (List Bool) :=
  {w | ∃ x, Above label w x}

theorem above_mono {α : Type*} [PartialOrder α] (label : α → ℕ) {x y : α} (h : x ≤ y)
    (w : List Bool) : Above label w y → Above label w x := by
  cases w with
  | nil => exact fun _ => trivial
  | cons c w =>
    rintro ⟨a,b,hy,he,hc,hw⟩
    exact ⟨a,b,h.trans hy,he,hc,hw⟩

/-- At least one cover in a comparable interval has the same comparison of labels
as its endpoints. -/
theorem cover_color {α : Type*} [Fintype α] [PartialOrder α] (label : α → ℕ)
    {x y : α} (hlt : x < y) :
    ∃ a b, x ≤ a ∧ a ⋖ b ∧ b ≤ y ∧ color label a b = color label x y := by
  classical
  let _ := Fintype.toLocallyFiniteOrder (α := α)
  induction lt_iff_transGen_covBy.mp hlt with
  | single h => exact ⟨_,_,le_rfl,h,le_rfl,rfl⟩
  | @tail y z path step ih =>
    rcases color_split label x y z with h | h
    · obtain ⟨a,b,ha,he,hb,hc⟩ := ih (lt_iff_transGen_covBy.mpr path)
      exact ⟨a,b,ha,he,hb.trans step.le,hc.trans h⟩
    · exact ⟨y,z,(lt_iff_transGen_covBy.mpr path).le,step,le_rfl,h⟩

end ChainWords

namespace ChainWords

theorem color_rev {α : Type*} {f : α → ℕ} (hf : Function.Injective f) {x y : α} (h : x ≠ y) :
    color f y x = !(color f x y) := by
  have h' := hf.ne h
  cases hx : color f x y <;> cases hy : color f y x <;> simp_all [color] <;> omega

theorem sorted_block {α : Type*} [Fintype α] (f : α → ℕ) (hf : Function.Injective f)
    (S : Set α) (b : Bool) :
    ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ S) ∧ Run f b l := by
  classical
  let _ := LinearOrder.lift' f hf
  let A := S.toFinite.toFinset
  cases b with
  | false =>
    refine ⟨A.sort (· ≥ ·), Finset.sort_nodup .., fun x => ?_, ?_⟩
    · simp [A]
    · exact A.sortedGT_sort.pairwise.imp fun {x y} h => by
        simpa [color] using (show f y < f x from h)
  | true =>
    refine ⟨A.sort, Finset.sort_nodup .., fun x => ?_, ?_⟩
    · simp [A]
    · exact A.sortedLT_sort.pairwise.imp fun {x y} h => by
        simpa [color] using (show f x ≤ f y from h.le)

private theorem compare_mem {α : Type*} {r : α → α → Prop} {l : List α} (hl : l.Pairwise r)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : r a b ∨ r b a := by
  induction hl with
  | nil => simp at ha
  | @cons x l h _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inl (h b ((List.mem_cons.mp hb).resolve_left hne.symm))
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inr (h a ((List.mem_cons.mp ha).resolve_left hne))
      · exact ih ha hb

/-- In an extension cut into runs of the prescribed signs, the complementary
word cannot occur above any vertex of its upper set. -/
theorem cuts_exclude {α : Type*} [PartialOrder α] (f : α → ℕ) {s l} (hc : Cuts f s l)
    {D : Set α} (he : IsExtension D l) (hD : IsUpperSet D) :
    ∀ x ∈ D, ¬ Above f (s.map Bool.not) x := by
  induction hc generalizing D with
  | nil =>
    intro x hx
    exact False.elim (List.not_mem_nil ((he.2.1 x).2 hx))
  | @cons s l r c hrun _ ih =>
    obtain ⟨hnd,mem,hw⟩ := he
    obtain ⟨hw₁,hw₂,cross⟩ := List.pairwise_append.mp hw
    obtain ⟨-,hr,disj⟩ := List.nodup_append.mp hnd
    let E : Set α := {z | z ∈ r}
    have tailUpper : IsUpperSet E := by
      intro a b hab ha
      change a ∈ r at ha
      change b ∈ r
      have hb := (mem b).2 (hD hab ((mem a).1 (List.mem_append_right _ ha)))
      rcases List.mem_append.mp hb with hb | hb
      · exact False.elim ((cross b hb a ha) (lt_of_le_of_ne hab (fun h => disj b hb a ha h.symm)))
      · exact hb
    have tail := ih (D := E) ⟨hr,fun _ => Iff.rfl,hw₂⟩ tailUpper
    intro x hx
    rintro ⟨a,b,hxa,hab,hcol,hw'⟩
    have ha := (mem a).2 (hD hxa hx)
    have hb := (mem b).2 (hD (hxa.trans hab.le) hx)
    rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp ha with ha | ha
      · rcases compare_mem (hw₁.and hrun) ha hb hab.ne with h | h
        · simp [h.2] at hcol
        · exact h.1 hab.lt
      · exact cross b hb a ha hab.lt
    · exact tail b hb hw'

/-- Greedily sort the first lower ideal by its required label direction. The
remaining upper set admits the tail schedule. -/
theorem cuts_of_exclusion {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ)
    (hf : Function.Injective f) (s : List Bool) (D : Set α) (hD : IsUpperSet D)
    (h : ∀ x ∈ D, ¬ Above f (s.map Bool.not) x) :
    ∃ l, IsExtension D l ∧ Cuts f s l := by
  classical
  induction s generalizing D with
  | nil =>
    refine ⟨[], ⟨by simp, fun x => ?_, by simp⟩, .nil⟩
    simpa using (show x ∉ D from fun hx => h x hx trivial)
  | cons c s ih =>
    let I : Set α := {x | x ∈ D ∧ Above f (s.map Bool.not) x}
    let E : Set α := D \ I
    have upper : IsUpperSet E := by
      intro x y hxy hx
      exact ⟨hD hxy hx.1, fun hy => hx.2 ⟨hx.1,above_mono f hxy _ hy.2⟩⟩
    obtain ⟨r,⟨rn,rm,rpw⟩,rcut⟩ := ih E upper fun x hx hb => hx.2 ⟨hx.1,hb⟩
    obtain ⟨l,ln,lm,lpw⟩ := sorted_block f hf I c
    have comparable {x y} (hx : x ∈ I) (hy : y ∈ I) (hlt : x < y) : color f x y = c := by
      obtain ⟨a,b,ha,hab,hb,hcol⟩ := cover_color f hlt
      by_contra hne
      have opp : color f x y = !c := by cases c <;> simp_all
      exact h x hx.1 ⟨a,b,ha,hab,hcol.trans opp,above_mono f hb _ hy.2⟩
    have localOrder : l.Pairwise (fun x y => ¬ y < x) := by
      apply lpw.imp_of_mem
      intro x y hx hy hc hyx
      have hyc := comparable ((lm y).1 hy) ((lm x).1 hx) hyx
      rw [color_rev hf hyx.ne.symm, hc] at hyc
      cases c <;> contradiction
    refine ⟨l ++ r, ⟨List.nodup_append.mpr ⟨ln,rn,?_⟩,?_,List.pairwise_append.mpr ⟨localOrder,rpw,?_⟩⟩,
      .cons lpw rcut⟩
    · intro x hx y hy hxy
      subst y
      exact ((rm x).1 hy).2 ((lm x).1 hx)
    · intro x
      rw [List.mem_append, lm, rm]
      change x ∈ I ∨ x ∈ D ∧ x ∉ I ↔ x ∈ D
      exact ⟨fun h => h.elim (fun hi => hi.1) And.left, fun h => (em (x ∈ I)).imp_right (fun hi => ⟨h,hi⟩)⟩
    · intro x hx y hy hyx
      have hI := (lm x).1 hx
      have hE := (rm y).1 hy
      exact hE.2 ⟨hE.1,above_mono f hyx.le _ hI.2⟩

end ChainWords

namespace ChainWords

private theorem prepend_saturated {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ)
    (w : List Bool) {x y : α} (hxy : x ≤ y)
    (hw : ∃ l : List α, (y :: l).IsChain (· ⋖ ·) ∧ w.Sublist (descWord f (y :: l))) :
    ∃ l : List α, (x :: l).IsChain (· ⋖ ·) ∧ w.Sublist (descWord f (x :: l)) := by
  classical
  let _ := Fintype.toLocallyFiniteOrder (α := α)
  induction le_iff_reflTransGen_covBy.mp hxy with
  | refl => exact hw
  | @tail y z hp he ih =>
    obtain ⟨l,hc,hs⟩ := hw
    apply ih (le_iff_reflTransGen_covBy.mpr hp)
    exact ⟨z :: l, List.isChain_cons_cons.mpr ⟨he,hc⟩, hs.cons _⟩

theorem saturated_iff {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ) (w : List Bool) (x : α) :
    Above f w x ↔ ∃ l : List α, (x :: l).IsChain (· ⋖ ·) ∧ w.Sublist (descWord f (x :: l)) := by
  constructor
  · induction w generalizing x with
    | nil => exact fun _ => ⟨[], by simp, .slnil⟩
    | cons c w ih =>
      rintro ⟨a,b,ha,he,rfl,hw⟩
      obtain ⟨l,hc,hs⟩ := ih b hw
      exact prepend_saturated f _ ha ⟨b :: l,List.isChain_cons_cons.mpr ⟨he,hc⟩,hs.cons_cons _⟩
  · rintro ⟨l,hc,hs⟩
    induction l generalizing x w with
    | nil =>
      change w.Sublist [] at hs
      have := List.sublist_nil.mp hs
      subst w
      trivial
    | cons y l ih =>
      obtain ⟨he,hc⟩ := List.isChain_cons_cons.mp hc
      change w.Sublist (color f x y :: descWord f (y :: l)) at hs
      cases hs with
      | cons _ hs => exact above_mono f he.le _ (ih _ _ hc hs)
      | cons_cons _ hs => exact ⟨x,y,le_rfl,he,rfl,ih _ _ hc hs⟩

/-- The original reverse containment theorem, for arbitrary finite labeled
posets. Each word occurs as a subsequence along an actual saturated chain. -/
theorem support_forces_language {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
    (f : α ↪ ℕ) (g : β ↪ ℕ) (h : fundamentalSupport f ⊆ fundamentalSupport g) :
    language g ⊆ language f := by
  intro w hw
  by_contra hbad
  let s := w.map Bool.not
  have comp : s.map Bool.not = w := by simp [s, List.map_map, Function.comp_def]
  have excluded (x : α) (_ : x ∈ (Set.univ : Set α)) : ¬ Above f (s.map Bool.not) x := by
    rw [comp]
    exact fun hx => hbad ⟨x,hx⟩
  obtain ⟨l,hel,hcut⟩ := cuts_of_exclusion f f.injective s Set.univ (fun _ _ _ _ => Set.mem_univ _) excluded
  obtain ⟨r,her,heq⟩ := h (show (l.length, descWord f l) ∈ fundamentalSupport f from ⟨l,hel,rfl⟩)
  have cut := cuts_transfer hcut r (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  obtain ⟨x,hx⟩ := hw
  apply cuts_exclude g cut her (fun _ _ _ _ => Set.mem_univ _) x (Set.mem_univ _)
  rwa [comp]

def chainLengths (α : Type*) [PartialOrder α] : Set ℕ :=
  {n | ∃ l : List α, l.Pairwise (· < ·) ∧ l.length = n}

/-- Height counts vertices, with height zero for the empty poset. -/
noncomputable def height (α : Type*) [PartialOrder α] : ℕ := sSup (chainLengths α)

private theorem above_chain {α : Type*} [PartialOrder α] (f : α → ℕ) (w : List Bool)
    (x : α) (hw : Above f w x) :
    ∃ l : List α, (x :: l).Pairwise (· < ·) ∧ l.length = w.length := by
  induction w generalizing x with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons c w ih =>
    obtain ⟨a,b,ha,he,_,hw⟩ := hw
    obtain ⟨l,hc,hl⟩ := ih b hw
    have hxb := ha.trans_lt he.lt
    refine ⟨b :: l, List.pairwise_cons.mpr ⟨?_,hc⟩, by simp [hl]⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxb
    · exact hxb.trans ((List.pairwise_cons.mp hc).1 y hy)

private theorem chain_above {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ)
    (l : List α) (x : α) (hc : (x :: l).Pairwise (· < ·)) :
    ∃ w, Above f w x ∧ w.length = l.length := by
  induction l generalizing x with
  | nil => exact ⟨[],trivial,rfl⟩
  | cons y l ih =>
    have hxy := (List.pairwise_cons.mp hc).1 y List.mem_cons_self
    obtain ⟨a,b,ha,he,hb,hc'⟩ := cover_color f hxy
    obtain ⟨w,hw,hl⟩ := ih y (List.pairwise_cons.mp hc).2
    exact ⟨color f x y :: w,⟨a,b,ha,he,hc',above_mono f hb _ hw⟩,by simp [hl]⟩

theorem height_antitone {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
    (f : α ↪ ℕ) (g : β ↪ ℕ) (h : fundamentalSupport f ⊆ fundamentalSupport g) :
    height β ≤ height α := by
  apply csSup_le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro _ ⟨l,hc,rfl⟩
    exact List.Nodup.length_le_card (hc.imp (fun h => ne_of_lt h))
  · exact ⟨0,[],List.Pairwise.nil,rfl⟩
  · rintro _ ⟨_ | ⟨x,l⟩,hc,rfl⟩
    · exact ⟨[],List.Pairwise.nil,rfl⟩
    · obtain ⟨w,hw,hl⟩ := chain_above g l x hc
      obtain ⟨y,hy⟩ := support_forces_language f g h (show w ∈ language g from ⟨x,hw⟩)
      obtain ⟨r,hr,hrl⟩ := above_chain f _ y hy
      exact ⟨y :: r,hr,by simp [hrl,hl]⟩

end ChainWords

namespace ChainWords

/-- A monomial is its multiset of positive-variable indices, shifted to start at
zero. The order of a list of indices has no effect on this coefficient. -/
def IsPPartition {α : Type*} [PartialOrder α] (f t : α → ℕ) : Prop :=
  ∀ ⦃x y⦄, x < y → t x < t y ∨ t x = t y ∧ f x < f y

def Colorings {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ) (v : List ℕ) :=
  {t : α → ℕ // IsPPartition f t ∧ ((Finset.univ : Finset α).toList.map t).Perm v}

noncomputable def monomialCoefficient {α : Type*} [Fintype α] [PartialOrder α]
    (f : α → ℕ) (v : List ℕ) : ℕ := Nat.card (Colorings f v)

def key {α : Type*} (f t : α → ℕ) (x : α) : ℕ ×ₗ ℕ := toLex (t x, f x)

theorem key_injective {α : Type*} {f : α → ℕ} (hf : Function.Injective f) (t : α → ℕ) :
    Function.Injective (key f t) := by
  intro x y h
  exact hf (congrArg Prod.snd (toLex_inj.mp h))

/-- On a finite poset the usual cover inequalities suffice: assignments are
nondecreasing along every cover and strictly increase when the labels descend. -/
theorem partition_iff_covers {α : Type*} [Fintype α] [PartialOrder α] (f : α ↪ ℕ) (t : α → ℕ) :
    IsPPartition f t ↔ ∀ ⦃x y⦄, x ⋖ y → t x ≤ t y ∧ (color f x y = false → t x < t y) := by
  constructor
  · intro hp x y he
    rcases hp he.lt with lt | ⟨eq,hl⟩
    · exact ⟨lt.le,fun _ => lt⟩
    · exact ⟨eq.le,fun h => False.elim ((by simpa [color] using h : f y < f x).asymm hl)⟩
  · classical
    intro hc x y hxy
    let _ := Fintype.toLocallyFiniteOrder (α := α)
    have step {a b : α} (he : a ⋖ b) : key f t a < key f t b := by
      obtain ⟨hle,hs⟩ := hc he
      apply Prod.Lex.toLex_lt_toLex.mpr
      rcases hle.lt_or_eq with lt | eq
      · exact Or.inl lt
      · refine Or.inr ⟨eq,?_⟩
        have ne := f.injective.ne he.ne
        by_contra! hn
        have hdrop := lt_of_le_of_ne hn ne.symm
        exact (hs (by simpa [color] using hdrop)).ne eq
    have hkey : key f t x < key f t y := by
      induction lt_iff_transGen_covBy.mp hxy with
      | single he => exact step he
      | @tail z y hp he ih => exact (ih (lt_iff_transGen_covBy.mpr hp)).trans (step he)
    exact Prod.Lex.toLex_lt_toLex.mp hkey

/-- The allowed equalities of consecutive levels are a word. A false entry opens
a new level, where a descent of the vertex labels may occur. -/
def levels (a : ℕ) : List Bool → List ℕ
  | [] => [a]
  | b :: s => a :: levels (if b then a else a + 1) s

theorem levels_head (a : ℕ) (s : List Bool) : (levels a s).head? = some a := by cases s <;> rfl

theorem levels_length (a : ℕ) (s : List Bool) : (levels a s).length = s.length + 1 := by
  induction s generalizing a with
  | nil => rfl
  | cons b s ih => simp [levels,ih]

theorem levels_sorted (a : ℕ) (s : List Bool) : (levels a s).Pairwise (· ≤ ·) := by
  induction s generalizing a with
  | nil => simp [levels]
  | cons b s ih =>
    let a' := if b then a else a+1
    have ha : a ≤ a' := by cases b <;> simp [a']
    have hhead := levels_head a' s
    generalize hv : levels a' s = v at hhead
    obtain _ | ⟨y,l⟩ := v
    · simp at hhead
    · have hy : y = a' := by simpa using hhead
      have hv' := ih a'
      rw [hv] at hv'
      change (a :: levels a' s).Pairwise _
      rw [hv,List.pairwise_cons_cons_iff_of_trans]
      exact ⟨hy ▸ ha,hv'⟩

def Allows (mask word : List Bool) : Prop :=
  List.Forall₂ (fun m d => m = false ∨ d = true) mask word

theorem keyed_iff {α : Type*} (f t : α → ℕ) (l : List α) (mask : List Bool) (a : ℕ)
    (hv : l.map t = levels a mask) :
    l.Pairwise (fun x y => key f t x ≤ key f t y) ↔ Allows mask (descWord f l) := by
  induction mask generalizing a l with
  | nil =>
    have hl := congrArg List.length hv
    simp [levels] at hl
    rcases l with _ | ⟨x, _ | ⟨y,l⟩⟩ <;> simp_all [Allows,descWord]
  | cons b mask ih =>
    rcases l with _ | ⟨x, _ | ⟨y,l⟩⟩
    · simp [levels] at hv
    · have hl := congrArg List.length hv
      simp [levels_length] at hl
    · let a' := if b then a else a+1
      change t x :: (y :: l).map t = a :: levels a' mask at hv
      obtain ⟨hx,hy⟩ := List.cons.inj hv
      have hhead := congrArg List.head? hy
      rw [levels_head] at hhead
      have hy' : t y = a' := by simpa using hhead
      let _ : IsTrans α (fun x y => key f t x ≤ key f t y) := ⟨fun _ _ _ => le_trans⟩
      rw [List.pairwise_cons_cons_iff_of_trans, ih _ _ hy]
      change (_ ∧ _) ↔ List.Forall₂ _ (b :: mask) (color f x y :: descWord f (y :: l))
      rw [List.forall₂_cons]
      apply and_congr_left'
      cases b <;> simp [key,Prod.Lex.toLex_le_toLex,hx,hy',a',color]

theorem map_exists {α : Type*} (l : List α) (hn : l.Nodup) (v : List ℕ) (h : l.length = v.length) :
    ∃ t : α → ℕ, l.map t = v := by
  classical
  induction l generalizing v with
  | nil =>
    have : v = [] := List.length_eq_zero_iff.mp h.symm
    exact ⟨fun _ => 0, this.symm⟩
  | cons x l ih =>
    rcases v with _ | ⟨y,v⟩
    · simp at h
    · obtain ⟨t,ht⟩ := ih (List.nodup_cons.mp hn).2 v (by simpa using h)
      refine ⟨Function.update t x y, ?_⟩
      simp only [List.map_cons,Function.update_self,List.cons.injEq,true_and]
      rw [← ht]
      apply List.map_inj_left.mpr
      intro z hz
      have hzx : z ≠ x := by rintro rfl; exact (List.nodup_cons.mp hn).1 hz
      exact Function.update_of_ne hzx ..

theorem key_sorted_extension {α : Type*} [PartialOrder α] {f t : α → ℕ} (ht : IsPPartition f t)
    {l : List α} (hkey : l.Pairwise (fun x y => key f t x ≤ key f t y)) :
    l.Pairwise (fun x y => ¬ y < x) := by
  apply hkey.imp
  intro x y hk hyx
  have hs : key f t y < key f t x := Prod.Lex.toLex_lt_toLex.mpr (ht hyx)
  exact hs.not_ge hk

theorem partition_of_key_sorted {α : Type*} [PartialOrder α] {f t : α → ℕ}
    (hf : Function.Injective f) {l : List α} (he : IsExtension Set.univ l)
    (hkey : l.Pairwise (fun x y => key f t x ≤ key f t y)) : IsPPartition f t := by
  intro x y hxy
  have mem (x : α) : x ∈ l := (he.2.1 x).mpr (Set.mem_univ _)
  have all : l.Pairwise (fun a b => a < b → key f t a < key f t b) := by
    apply hkey.imp
    intro a b hk hab
    exact lt_of_le_of_ne hk ((key_injective hf t).ne hab.ne)
  have rev : l.Pairwise (fun a b => b < a → key f t b < key f t a) :=
    he.2.2.imp (fun hn hh => False.elim (hn hh))
  have h := List.Pairwise.forall_of_forall_of_flip (R := fun a b => a < b → key f t a < key f t b)
    (fun _ _ h => False.elim (lt_irrefl _ h)) all rev (mem x) (mem y) hxy
  exact Prod.Lex.toLex_lt_toLex.mp h

end ChainWords

namespace ChainWords

noncomputable def extensions (α : Type*) [Fintype α] [PartialOrder α] (n : ℕ) :
    Finset (List.Vector α n) := by
  classical exact Finset.univ.filter fun l => IsExtension Set.univ l.val

noncomputable def admissible {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ) (s : List Bool) :
    Finset (List.Vector α (s.length+1)) := by
  classical exact (extensions α _).filter fun l => Allows s (descWord f l.val)

theorem mem_extensions {α : Type*} [Fintype α] [PartialOrder α] {n} (l : List.Vector α n) :
    l ∈ extensions α n ↔ IsExtension Set.univ l.val := by classical simp [extensions]

theorem mem_admissible {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ) {s} (l : List.Vector α (s.length+1)) :
    l ∈ admissible f s ↔ IsExtension Set.univ l.val ∧ Allows s (descWord f l.val) := by
  classical simp [admissible,mem_extensions]

theorem perm_univ {α : Type*} [Fintype α] [PartialOrder α] {l : List α} (he : IsExtension Set.univ l) :
    l.Perm (Finset.univ : Finset α).toList := by
  apply (List.perm_ext_iff_of_nodup he.1 (Finset.nodup_toList _)).mpr
  intro x
  simp [he.2.1 x]

private theorem sorted_vertices {α : Type*} [Fintype α] (f : α → ℕ) (hf : Function.Injective f)
    (t : α → ℕ) : ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l) ∧ l.Pairwise (fun x y => key f t x ≤ key f t y) := by
  classical
  let _ := LinearOrder.lift' (key f t) (key_injective hf t)
  exact ⟨Finset.univ.sort, Finset.sort_nodup .., by simp, Finset.pairwise_sort ..⟩

/-- Standardization identifies the order-preserving assignments with any fixed
monomial with the extensions whose descents are permitted at its level changes. -/
theorem fundamental_expansion {α : Type*} [Fintype α] [PartialOrder α] (f : α ↪ ℕ) (s : List Bool) :
    monomialCoefficient f (levels 0 s) = (admissible f s).card := by
  classical
  let C := Colorings f (levels 0 s)
  let E := ↥(admissible f s)
  let R (c : C) (e : E) := e.1.1.map c.1 = levels 0 s
  have toExtension (c : C) : ∃ e : E, R c e := by
    obtain ⟨l,hn,hm,hk⟩ := sorted_vertices f f.injective c.1
    have he : IsExtension Set.univ l := ⟨hn, fun x => by simp [hm x],key_sorted_extension c.2.1 hk⟩
    have hperm := ((perm_univ he).map c.1).trans c.2.2
    have sorted : (l.map c.1).Pairwise (· ≤ ·) := List.pairwise_map.mpr (hk.imp fun h =>
      (Prod.Lex.toLex_le_toLex.mp h).elim (fun h => h.le) (fun h => h.1.le))
    have eq := hperm.eq_of_pairwise' sorted (levels_sorted 0 s)
    have hl : l.length = s.length+1 := by simpa [levels_length] using congrArg List.length eq
    let v : List.Vector α (s.length+1) := ⟨l,hl⟩
    exact ⟨⟨v,(mem_admissible f v).mpr ⟨he,(keyed_iff f c.val l s 0 eq).mp hk⟩⟩,eq⟩
  have toColoring (e : E) : ∃ c : C, R c e := by
    obtain ⟨he,ha⟩ := (mem_admissible f e.val).mp e.property
    obtain ⟨t,ht⟩ := map_exists _ he.1 (levels 0 s) (e.1.2.trans (levels_length 0 s).symm)
    have hk := (keyed_iff f t e.val.val s 0 ht).mpr ha
    refine ⟨⟨t,partition_of_key_sorted f.injective he hk,?_⟩,ht⟩
    rw [← ht]
    exact (perm_univ he).symm.map _
  have uniq (c : C) (e e' : E) (h : R c e) (h' : R c e') : e = e' := by
    obtain ⟨he,ha⟩ := (mem_admissible f e.val).mp e.property
    obtain ⟨he',ha'⟩ := (mem_admissible f e'.val).mp e'.property
    have hk := (keyed_iff f c.val e.val.val s 0 h).mpr ha
    have hk' := (keyed_iff f c.val e'.val.val s 0 h').mpr ha'
    apply Subtype.ext
    apply Subtype.ext
    exact List.Perm.eq_of_pairwise (fun _ _ _ _ hxy hyx => key_injective f.injective c.val (le_antisymm hxy hyx))
      hk hk' ((perm_univ he).trans (perm_univ he').symm)
  let F (c : C) : E := (toExtension c).choose
  have hF (c : C) : R c (F c) := (toExtension c).choose_spec
  have inj : Function.Injective F := by
    intro c d h
    have eq := hF c
    rw [h] at eq
    have maps := List.map_inj_left.mp (eq.trans (hF d).symm)
    exact Subtype.ext (funext fun x => maps x (((mem_admissible f (F d).val).mp (F d).property).1.2.1 x |>.mpr trivial))
  have sur : Function.Surjective F := by
    intro e
    obtain ⟨c,hc⟩ := toColoring e
    exact ⟨c,uniq c (F c) e (hF c) hc⟩
  calc
    monomialCoefficient f (levels 0 s) = Nat.card E := Nat.card_congr (Equiv.ofBijective F ⟨inj,sur⟩)
    _ = _ := by simp [E,Nat.card_eq_fintype_card]

end ChainWords

namespace ChainWords

theorem length_descWord {α : Type*} (f : α → ℕ) (l : List α) :
    (descWord f l).length = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rcases l with _ | ⟨y,l⟩
    · rfl
    · simp [descWord,ih]

private theorem allows_self (s : List Bool) : Allows s s := by
  induction s with
  | nil => exact .nil
  | cons b s ih => exact .cons (by cases b <;> simp) ih

private theorem allows_lt {s d : List Bool} (h : Allows s d) :
    d = s ∨ d.count false < s.count false := by
  induction h with
  | nil => exact Or.inl rfl
  | @cons b c s d h _ ih =>
    have hle : d.count false ≤ s.count false := ih.elim (fun h => h ▸ le_rfl) Nat.le_of_lt
    cases b <;> cases c <;> simp_all

noncomputable def exactCount {α : Type*} [Fintype α] [PartialOrder α]
    (f : α → ℕ) (n : ℕ) (d : List Bool) : ℕ := by
  classical exact ((extensions α n).filter (fun l => descWord f l.val = d)).card

private theorem fiber_sum {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ)
    (n : ℕ) (D : Finset (List Bool)) (hD : ∀ l ∈ extensions α n, descWord f l.val ∈ D)
    (s : List Bool) [DecidablePred (Allows s)] :
    ∑ d ∈ D.filter (Allows s), exactCount f n d =
      ((extensions α n).filter (fun l => Allows s (descWord f l.val))).card := by
  classical
  simp only [exactCount,Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_congr
  intro l hl
  simp [hD l hl]

private theorem equal_exact_counts {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
    (f : α ↪ ℕ) (g : β ↪ ℕ) (h : monomialCoefficient f = monomialCoefficient g)
    (n : ℕ) (D : Finset (List Bool)) (hP : ∀ l ∈ extensions α n, descWord f l.val ∈ D)
    (hQ : ∀ l ∈ extensions β n, descWord g l.val ∈ D) (s : List Bool) (hs : s ∈ D)
    (hlen : s.length+1 = n) : exactCount f n s = exactCount g n s := by
  classical
  have sums := calc
    ∑ d ∈ D.filter (Allows s), exactCount f n d =
        ((extensions α n).filter (fun l => Allows s (descWord f l.val))).card := fiber_sum f n D hP s
    _ = ((extensions β n).filter (fun l => Allows s (descWord g l.val))).card := by
      subst n
      exact (fundamental_expansion f s).symm.trans ((congrFun h _).trans (fundamental_expansion g s))
    _ = ∑ d ∈ D.filter (Allows s), exactCount g n d := (fiber_sum g n D hQ s).symm
  have hmem : s ∈ D.filter (Allows s) := Finset.mem_filter.mpr ⟨hs,allows_self s⟩
  have rest : ∑ d ∈ (D.filter (Allows s)).erase s, exactCount f n d =
      ∑ d ∈ (D.filter (Allows s)).erase s, exactCount g n d := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hne,hd⟩ := Finset.mem_erase.mp hd
    obtain ⟨hd,ha⟩ := Finset.mem_filter.mp hd
    exact equal_exact_counts f g h n D hP hQ d hd (by rw [← ha.length_eq,hlen])
  rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem,rest] at sums
  exact Nat.add_left_cancel sums
termination_by s.count false
decreasing_by exact (allows_lt ha).resolve_left hne

private theorem subset_of_equal_enumerators {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : fundamentalSupport f ⊆ fundamentalSupport g := by
  classical
  intro _ hc
  obtain ⟨l,he,rfl⟩ := hc
  let n := l.length
  let d := descWord f l
  let v : List.Vector α n := ⟨l,rfl⟩
  let D := ((extensions α n).image fun r => descWord f r.val) ∪ ((extensions β n).image fun r => descWord g r.val)
  have hP (r : List.Vector α n) (hr : r ∈ extensions α n) : descWord f r.val ∈ D :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)
  have hQ (r : List.Vector β n) (hr : r ∈ extensions β n) : descWord g r.val ∈ D :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)
  have hv : v ∈ extensions α n := (mem_extensions v).mpr he
  have hl : l ≠ [] := by
    intro hn
    obtain ⟨x⟩ := ‹Nonempty α›
    have hx := (he.2.1 x).mpr (Set.mem_univ _)
    simp [hn] at hx
  have hn : d.length + 1 = n := by
    have hlen := List.length_pos_iff.mpr hl
    dsimp [d,n]
    rw [length_descWord]
    omega
  have eq := equal_exact_counts f g h n D hP hQ d (hP v hv) hn
  have pos : 0 < exactCount f n d := Finset.card_pos.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  rw [eq] at pos
  obtain ⟨r,hr⟩ := Finset.card_pos.mp pos
  obtain ⟨hx,hd⟩ := Finset.mem_filter.mp hr
  exact ⟨r.val,(mem_extensions r).mp hx,Prod.ext r.2.symm hd.symm⟩

private theorem empty_coefficient {α : Type*} [Fintype α] [PartialOrder α] [IsEmpty α] (f : α → ℕ) :
    monomialCoefficient f [] = 1 := by
  classical
  let c : Colorings f [] := ⟨fun _ => 0, fun {x} => isEmptyElim x, by simp⟩
  let _ : Subsingleton (Colorings f []) := ⟨fun a b => Subtype.ext (funext fun x => isEmptyElim x)⟩
  let _ : Unique (Colorings f []) := uniqueOfSubsingleton c
  exact Nat.card_unique

private theorem nonempty_coefficient {α : Type*} [Fintype α] [PartialOrder α] [Nonempty α] (f : α → ℕ) :
    monomialCoefficient f [] = 0 := by
  have empty : IsEmpty (Colorings f []) := ⟨fun c => by
    have h := c.2.2.length_eq
    simp at h⟩
  simp [monomialCoefficient]

private theorem nonempty_of_equal_enumerators {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : Nonempty β := by
  by_contra hn
  have _ := not_nonempty_iff.mp hn
  have hc := congrFun h []
  rw [nonempty_coefficient,empty_coefficient] at hc
  contradiction

private theorem empty_support {α : Type*} [PartialOrder α] [IsEmpty α] (f : α → ℕ) :
    fundamentalSupport f = {(0,[])} := by
  ext c
  constructor
  · rintro ⟨_ | ⟨x,l⟩,he,rfl⟩
    · rfl
    · exact isEmptyElim x
  · rintro rfl
    exact ⟨[],⟨by simp,fun x => isEmptyElim x,by simp⟩,rfl⟩

/-- Equality of the actual monomial coefficients of the partition enumerators
recovers their fundamental supports, including the degree of each descent word. -/
theorem support_of_equal_enumerators {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : fundamentalSupport f = fundamentalSupport g := by
  by_cases ha : Nonempty α
  · have _ := nonempty_of_equal_enumerators f g h
    exact Set.Subset.antisymm (subset_of_equal_enumerators f g h) (subset_of_equal_enumerators g f h.symm)
  · have _ := not_nonempty_iff.mp ha
    have hb : ¬ Nonempty β := fun _ => ha (nonempty_of_equal_enumerators g f h.symm)
    have _ := not_nonempty_iff.mp hb
    exact (empty_support f).trans (empty_support g).symm

/-- McNamara and Ward's equal-height question with height in vertices. -/
theorem equal_enumerators_height {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : height α = height β := by
  have hs := support_of_equal_enumerators f g h
  exact le_antisymm (height_antitone g f hs.ge) (height_antitone f g hs.le)

end ChainWords
