module

public import SolvedProblems.ColourProbeOrder
public import SolvedProblems.ColourProbeTransport
public import SolvedProblems.ColourProbeSize

@[expose] public section

namespace ColourProbe

open SimpleGraph

private theorem preserve_edges {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (K : SimpleGraph W)
    (d : V ≃ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j)
    (counts : ∀ k, inducedCount (probe G) (coloringGraph G (Fin k)) = inducedCount (probe G) (coloringGraph K (Fin k)))
    (i j : V) (hij : G.Adj i j) : K.Adj (d i) (d j) := by
  classical
  by_contra hK
  let k := Fintype.card (Token V)
  let π := (Fintype.equivFin (Token V)).toEmbedding
  let _ := Fintype.ofFinite (probe G ↪g coloringGraph G (Fin k))
  let _ := Fintype.ofFinite (probe G ↪g coloringGraph K (Fin k))
  let F (f : probe G ↪g coloringGraph G (Fin k)) := (keepGraph G K d href).comp f
  have inj : Function.Injective F := by
    intro f g h
    exact DFunLike.ext _ _ fun a => (keepGraph G K d href).injective (congrArg (fun E : probe G ↪g coloringGraph K (Fin k) => E a) h)
  let extra := (relabel K π).comp (merged G K d i j hK)
  have hne (f) : F f ≠ extra := by
    intro same
    have hcol : (extra (rainbow G)).val (d i) = (extra (rainbow G)).val (d j) := congrArg π (merged_at G K d i j hK)
    rw [← same] at hcol
    change (keepGraph G K d href (f (rainbow G))).val (d i) = (keepGraph G K d href (f (rainbow G))).val (d j) at hcol
    exact (f (rainbow G)).property hij (by simpa only [keep_at] using hcol)
  have strict := Fintype.card_lt_of_injective_of_notMem F inj (b := extra) (fun ⟨f,h⟩ => hne f h)
  simp only [← Nat.card_eq_fintype_card,embeddings_count,counts k] at strict
  exact strict.false

/-- A single target-dependent induced-copy count distinguishes a graph from
every nonisomorphic finite simple graph, including hosts of different orders. -/
theorem reconstruct {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (K : SimpleGraph W)
    (counts : ∀ k, inducedCount (probe G) (coloringGraph G (Fin k)) =
      inducedCount (probe G) (coloringGraph K (Fin k))) : Nonempty (G ≃g K) := by
  classical
  let q := Fintype.card (Palette V)
  let π := (Fintype.equivFin (Palette V)).toEmbedding
  let own := (relabel G π).comp (ownEmbedding G)
  have pos := count_pos_of_embedding own
  rw [counts q] at pos
  obtain ⟨e⟩ := nonempty_of_count_pos pos
  have small : Fintype.card (Fin q) < 2 * Fintype.card (Option V) := by
    simp [q,Fintype.card_option,Fintype.card_sum]
    omega
  let d : V ↪ W := ⟨direction e,direction_injective e⟩
  have href (i j) (h : K.Adj (d i) (d j)) := reflect_edges e small h
  let iso := Equiv.ofBijective d ⟨d.injective,order_surjective G K d href counts⟩
  exact ⟨⟨iso,fun {i j} => ⟨href i j,preserve_edges G K iso href counts i j⟩⟩⟩

/-- The connected probe is one specific graph for each target. Its stated size
bound also covers the one-vertex probe for the empty target. -/
theorem one_colouring_probe {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ (U : Type) (_ : Fintype U) (H : SimpleGraph U), H.Connected ∧
      Fintype.card U ≤ 1 + Fintype.card V*(Fintype.card V+1) + (Fintype.card V).choose 2*(Fintype.card V+1)^2 ∧
      ∀ (W : Type) [Fintype W] (K : SimpleGraph W),
        (∀ k, inducedCount H (coloringGraph G (Fin k)) = inducedCount H (coloringGraph K (Fin k))) →
        Nonempty (G ≃g K) := by
  exact ⟨Row G,inferInstance,probe G,connected G,card_bound G,fun _ _ K => reconstruct G K⟩

end ColourProbe
