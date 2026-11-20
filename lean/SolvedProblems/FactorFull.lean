module

public import SolvedProblems.FactorColors

public section

namespace PackingFactorization

private def support (windows : List (List Nat)) (x : Nat) := ∃ w∈windows, x∈w

private theorem support_split {L R x} : support (L++R) x ↔ support L x ∨ support R x := by
  constructor
  · rintro ⟨w,hw,hx⟩
    rcases List.mem_append.mp hw with l|r
    · exact Or.inl ⟨w,l,hx⟩
    · exact Or.inr ⟨w,r,hx⟩
  · rintro (⟨w,hw,hx⟩|⟨w,hw,hx⟩)
    · exact ⟨w,List.mem_append_left _ hw,hx⟩
    · exact ⟨w,List.mem_append_right _ hw,hx⟩

private theorem project {L R xs} (pack : Packs (L++R) xs) (sel : Nat → Bool)
    (keep : ∀ x, support L x → sel x) (both : ∀ x, support R x → sel x → support L x) :
    Packs L (xs.filter sel) := by
  refine ⟨pack.1.filter _,?_,?_⟩
  · intro x
    simp only [List.mem_filter]
    constructor
    · rintro ⟨mem,ok⟩
      rcases support_split.mp ((pack.2.1 x).mp mem) with left|right
      · exact left
      · exact both _ right ok
    · intro mem
      exact ⟨(pack.2.1 _).mpr (support_split.mpr (Or.inl mem)),keep _ mem⟩
  · intro w hw
    have sub := (pack.2.2 w (List.mem_append_left R hw)).filter sel
    rwa [List.filter_eq_self.mpr (fun x hx => keep x ⟨w,hw,hx⟩)] at sub

private theorem packs_swap {L R xs} (pack : Packs (L++R) xs) : Packs (R++L) xs := by
  refine ⟨pack.1,?_,?_⟩
  · intro x
    exact (pack.2.1 x).trans (support_split.trans (or_comm.trans support_split.symm))
  · intro w hw
    apply pack.2.2
    simpa [or_comm] using hw

private theorem together_nodup (f g : Nat → Bool) (cover : ∀ x, f x ∨ g x) (xs : List Nat)
    (left : (xs.filter f).Nodup) (right : (xs.filter g).Nodup) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have drop (z : Nat→Bool) (h : ((x::xs).filter z).Nodup) : (xs.filter z).Nodup := by
      by_cases hz : z x <;> simp_all
    refine List.nodup_cons.mpr ⟨?_,ih (drop _ left) (drop _ right)⟩
    intro hx
    rcases cover x with h|h
    · have no : x∉xs.filter f := (List.nodup_cons.mp (by simpa [h] using left)).1
      exact no (List.mem_filter.mpr ⟨hx,h⟩)
    · have no : x∉xs.filter g := (List.nodup_cons.mp (by simpa [h] using right)).1
      exact no (List.mem_filter.mpr ⟨hx,h⟩)

private theorem combine {L R xs} {f g : Nat → Bool}
    (cover : ∀ x, f x ∨ g x) (left : Packs L (xs.filter f)) (right : Packs R (xs.filter g)) :
    Packs (L++R) xs := by
  refine ⟨together_nodup _ _ cover _ left.1 right.1,?_,?_⟩
  · intro x
    change x∈xs ↔ support (L++R) x
    rw [support_split]
    constructor
    · intro hx
      rcases cover x with h|h
      · exact Or.inl ((left.2.1 _).mp (List.mem_filter.mpr ⟨hx,h⟩))
      · exact Or.inr ((right.2.1 _).mp (List.mem_filter.mpr ⟨hx,h⟩))
    · rintro (h|h)
      · exact (List.mem_filter.mp ((left.2.1 _).mpr h)).1
      · exact (List.mem_filter.mp ((right.2.1 _).mpr h)).1
  · intro w hw
    rcases List.mem_append.mp hw with h|h
    · exact (left.2.2 w h).trans List.filter_sublist
    · exact (right.2.2 w h).trans List.filter_sublist

theorem projection_iff {K} {p : Pattern K} {m : Overlap p} {u v l t}
    (hl : Packs (orders false m u) l) (hr : Packs (orders true m v) t) (xs : List Nat) :
    Packs (orders false m u ++ orders true m v) xs ↔
      Packs (orders false m u) (PackingFactor.leftList hue xs) ∧
      Packs (orders true m v) (PackingFactor.rightList hue xs) := by
  constructor
  · intro pack
    constructor
    · apply project pack
      · intro x h
        rcases sideTag hl ((hl.2.1 _).mpr h) with e|⟨i,rfl⟩
        · simp_all
        · simp [hue_mark]
      · intro x h ok
        rcases sideTag hr ((hr.2.1 _).mpr h) with e|⟨i,rfl⟩
        · simp_all
        · exact (hl.2.1 _).mp (side_has_mark hl i)
    · apply project (packs_swap pack)
      · intro x h
        rcases sideTag hr ((hr.2.1 _).mpr h) with e|⟨i,rfl⟩
        · simp_all
        · simp [hue_mark]
      · intro x h ok
        rcases sideTag hl ((hl.2.1 _).mpr h) with e|⟨i,rfl⟩
        · simp_all
        · exact (hr.2.1 _).mp (side_has_mark hr i)
  · rintro ⟨a,b⟩; apply combine _ a b
    intro x; rcases hue_cases x with h|h|h <;> simp [h]

end PackingFactorization
