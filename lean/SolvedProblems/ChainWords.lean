module

public import SolvedProblems.ChainWordsSchedules
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Fintype.Card

@[expose] public section

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
