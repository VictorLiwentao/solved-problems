module

public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

@[expose] public section

open List

namespace AtomicGrowth

abbrev Word := List ℕ

/-- Rank within a finite word, using zero-based permutation values. -/
def rankIn (w : Word) (x : ℕ) : ℕ := (w.filter (fun y => decide (y<x))).length
def standard (w : Word) : Word := w.map (rankIn w)

def IsPerm (w : Word) : Prop := w.Perm (List.range w.length)
def Contains (u v : Word) : Prop := ∃ z, z.Sublist v ∧ standard z = u

theorem rank_lt {w : Word} {x y : ℕ} (hx : x ∈ w) (hxy : x<y) : rankIn w x < rankIn w y := by
  have h := (List.length_filter_lt_length_iff_exists (l:=w.filter (fun z => decide (z<y))) (p:=fun z => decide (z<x))).mpr
    ⟨x,by simp [hx,hxy],by simp⟩
  rw [List.filter_filter] at h
  have he : w.filter (fun z => decide (z<x) && decide (z<y)) = w.filter (fun z => decide (z<x)) := by
    apply List.filter_congr
    intro z _
    by_cases hh : z<x
    · simp [hh,hh.trans hxy]
    · simp [hh]
  rwa [he] at h

theorem rank_on {w : Word} {x y : ℕ} (hx : x ∈ w) (hy : y ∈ w) :
    rankIn w x < rankIn w y ↔ x<y := by
  constructor
  · intro h
    rcases lt_trichotomy x y with hh|rfl|hh
    · exact hh
    · exact False.elim (h.false)
    · exact False.elim ((rank_lt hy hh).not_gt h)
  · exact rank_lt hx

@[simp] theorem length_standard (w : Word) : (standard w).length = w.length := by simp [standard]

theorem perm_of_bounded {w : Word} (hd : w.Nodup) (hb : ∀ x ∈ w, x<w.length) : IsPerm w := by
  have hs : w.toFinset ⊆ Finset.range w.length := fun x hx => Finset.mem_range.mpr (hb x (List.mem_toFinset.mp hx))
  have he : w.toFinset = Finset.range w.length := Finset.eq_of_subset_of_card_le hs (by simp [List.toFinset_card_of_nodup hd])
  apply (List.perm_ext_iff_of_nodup hd List.nodup_range).mpr
  intro x
  simpa using (Finset.ext_iff.mp he x)

theorem standard_perm {w : Word} (hd : w.Nodup) : IsPerm (standard w) := by
  apply perm_of_bounded
  · apply hd.map_on
    intro x hx y hy e
    rcases lt_trichotomy x y with hl|hl|hl
    · exact False.elim ((rank_lt hx hl).ne e)
    · exact hl
    · exact False.elim ((rank_lt hy hl).ne e.symm)
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    rw [length_standard]
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨x,hx,by simp⟩

theorem standard_of_perm {w : Word} (hp : IsPerm w) : standard w = w := by
  change w.map _ = w
  conv_rhs => rw [←List.map_id w]
  apply List.map_congr_left
  intro x hx
  have hx' : x < w.length := List.mem_range.mp (hp.mem_iff.mp hx)
  have eqr : ((List.range w.length).filter (fun z => decide (z<x))) = List.range x := by
    have ha : (List.range x).filter (fun z => decide (z<x)) = List.range x :=
      List.filter_eq_self.mpr fun z hz => decide_eq_true (List.mem_range.mp hz)
    have hb : ((List.range (w.length-x)).map (x+·)).filter (fun z => decide (z<x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hz
      simp
    conv_lhs => rw [←Nat.add_sub_of_le hx'.le,List.range_add,List.filter_append,ha,hb,List.append_nil]
  exact (hp.filter (fun z => decide (z<x))).length_eq.trans (eqr ▸ List.length_range)

theorem standard_map {w : Word} (f : ℕ → ℕ)
    (hf : ∀ x ∈ w, ∀ y ∈ w, f x < f y ↔ x<y) : standard (w.map f) = standard w := by
  unfold standard
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply,rankIn,List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro y hy
  simp [hf y hy x hx]

theorem standard_shift (w : Word) (a : ℕ) : standard (w.map (a+·)) = standard w :=
  standard_map _ (by simp)

theorem Contains.trans {u v w : Word} (h : Contains u v) (k : Contains v w) : Contains u w := by
  obtain ⟨a,ha,rfl⟩ := k
  obtain ⟨b,hb,rfl⟩ := h
  obtain ⟨c,hc,rfl⟩ := List.sublist_map_iff.mp hb
  exact ⟨c,hc.trans ha,(standard_map _ (fun x hx y hy => rank_on (hc.subset hx) (hc.subset hy))).symm⟩

theorem Contains.refl {w : Word} (hw : IsPerm w) : Contains w w :=
  ⟨w,List.Sublist.refl _,standard_of_perm hw⟩

def direct (u v : Word) : Word := u ++ v.map (u.length+·)

theorem direct_perm {u v : Word} (hu : IsPerm u) (hv : IsPerm v) : IsPerm (direct u v) := by
  change (u ++ v.map (u.length+·)).Perm (List.range (direct u v).length)
  rw [show (direct u v).length = u.length+v.length by simp [direct],List.range_add]
  simpa [Nat.add_comm] using hu.append (hv.map (u.length+·))

/-- The pattern of separated blocks is the direct sum of their individual patterns. -/
theorem standard_append (u v : Word) (h : ∀ x ∈ u, ∀ y ∈ v, x<y) :
    standard (u++v) = direct (standard u) (standard v) := by
  simp only [standard,direct,List.map_append,List.map_map,List.length_map]
  congr 1
  · apply List.map_congr_left
    intro x hx
    simp only [rankIn,List.filter_append,List.length_append]
    have he : v.filter (fun y => decide (y<x)) = [] := List.filter_eq_nil_iff.mpr fun y hy => by simp [(h x hx y hy).not_gt]
    simp [he]
  · apply List.map_congr_left
    intro y hy
    simp only [rankIn,List.filter_append,List.length_append,Function.comp_apply]
    rw [List.filter_eq_self.mpr (fun x hx => by simp [h x hx y hy])]

end AtomicGrowth
