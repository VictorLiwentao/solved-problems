module

public import SolvedProblems.ChainWordsModel

@[expose] public section

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
