module

public import SolvedProblems.ShortestPathModel

@[expose] public section

namespace ShortestPathWL

open SimpleGraph
open JointForest (homCount)

universe u

/-- The host restriction is universal when `connectedOnly` is false. -/
def InScope {V : Type*} (connectedOnly : Bool) (G : SimpleGraph V) : Prop := connectedOnly = true → G.Connected

def CountablePattern {T : Type u} (connectedOnly : Bool) (F : SimpleGraph T) : Prop :=
  ∀ (V W : Type u) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    InScope connectedOnly G → InScope connectedOnly H → Equivalent G H → homCount F G = homCount F H

/-- SPD-WL counts exactly the forests, both on all finite hosts and on connected
hosts. The negative witnesses can always be connected and of diameter two. -/
theorem classification {T : Type u} [Fintype T] (F : SimpleGraph T) (connectedOnly : Bool) :
    CountablePattern connectedOnly F ↔ F.IsAcyclic := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨V, finite, G, H, hg, hh, _, _, he, hl⟩ := JointForest.cyclic_witness F hn
    exact (Nat.ne_of_lt hl) (h V V G H (fun _ => hg) (fun _ => hh) (forget_resistance G H hg hh he)).symm
  · intro hf V W _ _ G H _ _ he
    exact forests F G H hf he

/-- No ordinary homomorphism-count family represents shortest-path refinement,
with or without restricting to connected hosts. -/
theorem no_hom_family (connectedOnly : Bool) (family : (U : Type) → [Fintype U] → SimpleGraph U → Prop) :
    ¬ (∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      InScope connectedOnly G → InScope connectedOnly H → (Equivalent G H ↔
        ∀ (U : Type) [Fintype U] (F : SimpleGraph U), family U F → homCount F G = homCount F H)) := by
  intro h
  have forest (U : Type) [Fintype U] (F : SimpleGraph U) (hf : family U F) : F.IsAcyclic := by
    apply (classification F connectedOnly).mp
    intro V W _ _ G H hg hh he
    exact (h V W G H hg hh).mp he U F hf
  apply cubic_distinction
  apply (h (Fin 8) (Fin 8) JointForest.cube JointForest.chorded (fun _ => JointForest.cube_connected)
    (fun _ => JointForest.chorded_connected)).mpr
  intro U _ F hf
  exact JointForest.cubic_forests F (forest U F hf)

end ShortestPathWL
