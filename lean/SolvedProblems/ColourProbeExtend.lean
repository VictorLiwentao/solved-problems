module

public import SolvedProblems.ColourProbeDirections
public import SolvedProblems.ColourProbeCopies
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace ColourProbe

open SimpleGraph

noncomputable def extendWord {V W C : Type*} (d : V ↪ W) (p : V → C) (s : W → C) (w : W) : C := by
  classical exact if h : w ∈ Set.range d then p h.choose else s w

theorem extend_at {V W C : Type*} (d : V ↪ W) (p : V → C) (s : W → C) (v : V) :
    extendWord d p s (d v) = p v := by
  classical
  have hr : d v ∈ Set.range d := Set.mem_range_self _
  simp only [extendWord,dite_eq_left hr]
  exact congrArg p (d.injective hr.choose_spec)

theorem extend_off {V W C : Type*} (d : V ↪ W) (p : V → C) (s : W → C) {w : W} (hw : w ∉ Set.range d) :
    extendWord d p s w = s w := by classical simp [extendWord,hw]

theorem extend_adj_iff {V W C : Type*} (d : V ↪ W) (p q : V → C) (s : W → C) :
    (hamming W C).Adj (extendWord d p s) (extendWord d q s) ↔ (hamming V C).Adj p q := by
  classical
  constructor
  · rintro ⟨w,hw,ho⟩
    by_cases hmem : w ∈ Set.range d
    · obtain ⟨i,rfl⟩ := hmem
      refine ⟨i,by simpa only [extend_at] using hw,fun j hj => ?_⟩
      simpa only [extend_at] using ho (d j) (d.injective.ne hj)
    · exact False.elim (hw (by rw [extend_off d p s hmem,extend_off d q s hmem]))
  · rintro ⟨i,hi,ho⟩
    refine ⟨d i,by simpa only [extend_at] using hi,fun w hw => ?_⟩
    by_cases hmem : w ∈ Set.range d
    · obtain ⟨j,rfl⟩ := hmem
      simpa only [extend_at] using ho j (fun h => hw (congrArg d h))
    · rw [extend_off d p s hmem,extend_off d q s hmem]

theorem extend_proper {V W C : Type*} {G : SimpleGraph V} {K : SimpleGraph W} (d : V ↪ W)
    (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) {p : V → C} (hp : Proper G p)
    (s : W ↪ C) (free : ∀ i w, p i ≠ s w) : Proper K (extendWord d p s) := by
  classical
  intro w w' he
  by_cases h : w ∈ Set.range d <;> by_cases h' : w' ∈ Set.range d
  · obtain ⟨i,rfl⟩ := h
    obtain ⟨j,rfl⟩ := h'
    rw [extend_at,extend_at]
    exact hp (href i j he)
  · obtain ⟨i,rfl⟩ := h
    rw [extend_at,extend_off _ _ _ h']
    exact free i _
  · obtain ⟨j,rfl⟩ := h'
    rw [extend_off _ _ _ h,extend_at]
    exact (free j _).symm
  · rw [extend_off _ _ _ h,extend_off _ _ _ h']
    exact s.injective.ne he.ne

noncomputable def liftEmbedding {U V W C : Type*} {H : SimpleGraph U} {G : SimpleGraph V} {K : SimpleGraph W}
    (d : V ↪ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) (e : H ↪g coloringGraph G C)
    (s : W ↪ C) (free : ∀ u i w, (e u).val i ≠ s w) : H ↪g coloringGraph K C where
  toFun u := ⟨extendWord d (e u).val s,extend_proper d href (e u).property s (free u)⟩
  inj' x y h := by
    apply e.injective
    apply Subtype.ext
    funext i
    simpa only [extend_at] using congrFun (congrArg Subtype.val h) (d i)
  map_rel_iff' := (extend_adj_iff ..).trans e.map_adj_iff

noncomputable def used {U V C : Type*} [Fintype U] [Fintype V] {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g coloringGraph G C) : Finset C := by
  classical exact Finset.univ.image fun p : U × V => (e p.1).val p.2

theorem used_mem {U V C : Type*} [Fintype U] [Fintype V] {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g coloringGraph G C) (u : U) (i : V) : (e u).val i ∈ used e := by
  classical exact Finset.mem_image.mpr ⟨(u,i),Finset.mem_univ _,rfl⟩

noncomputable def reserve {U V W C : Type*} [Fintype U] [Fintype V] [Fintype W] [Fintype C]
    {H : SimpleGraph U} {G : SimpleGraph V} (e : H ↪g coloringGraph G C)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C) :
    (W × Bool) ↪ {c : C // c ∉ used e} := by
  classical
  apply Classical.choice
  apply (Function.Embedding.nonempty_iff_card_le).mpr
  have bound : (used e).card ≤ Fintype.card U * Fintype.card V := by
    unfold used
    exact Finset.card_image_le.trans (by simp)
  rw [Fintype.card_prod,Fintype.card_bool,Fintype.card_subtype_compl]
  simpa using (show Fintype.card W * 2 ≤ Fintype.card C - (used e).card by omega)

end ColourProbe
