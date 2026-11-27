module

public import SolvedProblems.DominationModel

@[expose] public section

namespace DominationVC

variable {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V] {S : Finset V}

omit [Fintype V] in
theorem closed_iff_visible (w v : V) : v = w ∨ (incomparability V).Adj w v ↔ Visible w v := by
  constructor
  · rintro (rfl | h)
    · exact ⟨lt_irrefl _, lt_irrefl _⟩
    · exact h.2
  · intro h
    by_cases he : v = w
    · exact .inl he
    · exact .inr ⟨Ne.symm he, h⟩

/-- Realize any prescribed predicate on a shattered set by one closed neighborhood. -/
theorem realize (hs : (closedFamily (incomparability V)).Shatters S) (P : V → Prop) :
    ∃ w, ∀ v ∈ S, Visible w v ↔ P v := by
  classical
  obtain ⟨N, hN, h⟩ := hs (Finset.filter_subset P S)
  unfold closedFamily at hN
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hN
  refine ⟨w, fun v hv => ?_⟩
  have he := Finset.ext_iff.mp h v
  simpa only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hv,
    closed_iff_visible] using he

theorem no_three_chain (hs : (closedFamily (incomparability V)).Shatters S)
    {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x < y) (hyz : y < z) : False := by
  obtain ⟨w, hw⟩ := realize hs (fun q => q ≠ y)
  have hvx := (hw x hx).2 hxy.ne
  have hvz := (hw z hz).2 (Ne.symm hyz.ne)
  have hn : ¬Visible w y := fun hv => (hw y hy).1 hv rfl
  by_cases hwy : w < y
  · exact hvz.1 (hwy.trans hyz)
  · exact hn ⟨hwy, fun hyw => hvx.2 (hxy.trans hyw)⟩

/-- In height at most two, the minimal elements and their complement are antichains.
One side can therefore host any finite index type of at most half the shattered size. -/
theorem large_antichain {I : Type*} [Fintype I] (hs : (closedFamily (incomparability V)).Shatters S)
    (hsize : 2 * Fintype.card I ≤ S.card) :
    ∃ f : I ↪ V, (∀ i, f i ∈ S) ∧ ∀ i j, ¬f i < f j := by
  classical
  let minimal (v : V) := ¬ ∃ w ∈ S, w < v
  have sizes := Finset.card_filter_add_card_filter_not (s := S) minimal
  have side (T : Finset V) (hsub : T ⊆ S) (hc : Fintype.card I ≤ T.card)
      (hanti : ∀ v ∈ T, ∀ w ∈ T, ¬v < w) :
      ∃ f : I ↪ V, (∀ i, f i ∈ S) ∧ ∀ i j, ¬f i < f j := by
    obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hc
    have hx (i : I) : f i ∈ T := hf ⟨i, rfl⟩
    exact ⟨f, fun i => hsub (hx i), fun i j => hanti _ (hx i) _ (hx j)⟩
  by_cases h : Fintype.card I ≤ (S.filter minimal).card
  · apply side (S.filter minimal) (Finset.filter_subset ..) h
    intro x hx y hy hlt
    exact (Finset.mem_filter.mp hy).2 ⟨x, (Finset.mem_filter.mp hx).1, hlt⟩
  · apply side (S.filter fun v => ¬minimal v) (Finset.filter_subset ..) (by omega)
    intro x hx y hy hlt
    have hnm := (Finset.mem_filter.mp hx).2
    obtain ⟨w, hw, hlt'⟩ := not_not.mp hnm
    exact no_three_chain hs hw (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hlt' hlt

end DominationVC
