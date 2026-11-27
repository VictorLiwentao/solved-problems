module

public import SolvedProblems.ColourProbeExtend

@[expose] public section

namespace ColourProbe

open SimpleGraph

variable {U V W C : Type*} [Fintype U] [Fintype V] [Fintype W] [Fintype C]
  {H : SimpleGraph U} {G : SimpleGraph V} {K : SimpleGraph W}

noncomputable def tag (e : H ↪g coloringGraph G C)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C) (b : Bool) : W ↪ C where
  toFun w := (reserve e hc (w,b)).val
  inj' _ _ h := congrArg Prod.fst ((reserve e hc).injective (Subtype.ext h))

theorem unused (e : H ↪g coloringGraph G C)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C) (b : Bool)
    (u : U) (i : V) (w : W) : (e u).val i ≠ tag e hc b w := by
  intro h
  change (e u).val i = (reserve e hc (w,b)).val at h
  apply (reserve e hc (w,b)).property
  rw [← h]
  exact used_mem e u i

/-- An additional host coordinate strictly increases the number of labeled
embeddings at a sufficiently large palette. Restriction to the old coordinates
recovers the entire embedding, and at the additional coordinate a bit is stored
using colors absent from all its rows. -/
theorem extra_coordinate (d : V ↪ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j)
    (w : W) (hw : w ∉ Set.range d) (u : U)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C)
    (existsEmbedding : Nonempty (H ↪g coloringGraph G C)) :
    Nat.card (H ↪g coloringGraph G C) < Nat.card (H ↪g coloringGraph K C) := by
  classical
  let _ := Fintype.ofFinite (H ↪g coloringGraph G C)
  let _ := Fintype.ofFinite (H ↪g coloringGraph K C)
  let F (p : (H ↪g coloringGraph G C) × Bool) := liftEmbedding d href p.1 (tag p.1 hc p.2) (unused p.1 hc p.2)
  have hinj : Function.Injective F := by
    rintro ⟨f,b⟩ ⟨g,c⟩ he
    have eqAt (u' : U) (w' : W) : extendWord d (f u').val (tag f hc b) w' =
        extendWord d (g u').val (tag g hc c) w' :=
      congrArg (fun (E : H ↪g coloringGraph K C) => (E u').val w') he
    have hfg : f=g := by
      ext u' i
      simpa only [extend_at] using eqAt u' (d i)
    subst g
    have hb : (reserve f hc (w,b)).val = (reserve f hc (w,c)).val := by
      change tag f hc b w = tag f hc c w
      simpa only [extend_off _ _ _ hw] using eqAt u w
    exact Prod.ext rfl (congrArg (fun p : W × Bool => p.2) ((reserve f hc).injective (Subtype.ext hb)))
  have bound := Fintype.card_le_of_injective F hinj
  have pos := Fintype.card_pos (α := H ↪g coloringGraph G C)
  rw [Fintype.card_prod,Fintype.card_bool] at bound
  simp only [Nat.card_eq_fintype_card]
  omega

theorem order_surjective {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (K : SimpleGraph W)
    (d : V ↪ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j)
    (counts : ∀ k, inducedCount (probe G) (coloringGraph G (Fin k)) = inducedCount (probe G) (coloringGraph K (Fin k))) :
    Function.Surjective d := by
  classical
  change ∀ w, ∃ i, d i = w
  by_contra! h
  obtain ⟨w,hw⟩ := h
  let k := Fintype.card (Row G) * Fintype.card V + Fintype.card W * 2 + Fintype.card (Palette V)
  have hc : Fintype.card (Row G)*Fintype.card V + Fintype.card W*2 ≤ Fintype.card (Fin k) := by simp [k]
  have bounds : Fintype.card (Palette V) ≤ Fintype.card (Fin k) := by simp [k]
  let emb := (Function.Embedding.nonempty_iff_card_le.mpr bounds).some
  let own := (relabel G emb).comp (ownEmbedding G)
  have strict := extra_coordinate d href w (fun ⟨i,hi⟩ => hw i hi) (rainbow G) hc ⟨own⟩
  rw [embeddings_count,embeddings_count,counts k] at strict
  exact strict.false

end ColourProbe
