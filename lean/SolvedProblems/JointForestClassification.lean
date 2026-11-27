module

public import SolvedProblems.JointForest
public import SolvedProblems.JointForestCovariance

@[expose] public section

namespace JointForest

open SimpleGraph

universe u

/-- Some pair attains two, and every pair is within two edges. -/
def DiameterTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ x y, G.dist x y ≤ 2) ∧ ∃ x y, G.dist x y = 2

/-- For each cyclic pattern the expanded signed cones give connected
diameter-two witnesses, equivalent at every joint round, with different
ordinary homomorphism counts. -/
theorem cyclic_witness {T : Type u} [Fintype T] (F : SimpleGraph T) (hF : ¬F.IsAcyclic) :
    ∃ (V : Type u) (finite : Fintype V) (G H : SimpleGraph V), letI := finite
      G.Connected ∧ H.Connected ∧ DiameterTwo G ∧ DiameterTwo H ∧
      Equivalent (jointLabels G) (jointLabels H) ∧ homCount F H < homCount F G := by
  classical
  let : LinearOrder T := LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective
  let r := Fintype.card T + 3
  let m := continuant (r+1)
  have hr : 0 < r := by dsimp [r]; omega
  obtain ⟨d,hcount⟩ := cone_twist_loss F hF m r (by dsimp [r]; omega)
  let B := expanded T m r
  let G := cone (signedLift B (signing false d))
  let H := cone (signedLift B (signing true d))
  refine ⟨Option (Base T m r × Bool), inferInstance, G, H, cone_connected _, cone_connected _, ?_, ?_,
    expanded_equivalent hr (rfl : m = continuant (r+1)) d, hcount⟩
  · exact ⟨cone_dist_le_two _, _, _, opposite_sheets_dist B _ (.inl d.val.1)⟩
  · exact ⟨cone_dist_le_two _, _, _, opposite_sheets_dist B _ (.inl d.val.1)⟩

/-- A pattern is countable when any two finite connected hosts equivalent
under the joint distance refinement have the same number of edge-preserving
vertex maps from the pattern. -/
def CountablePattern {T : Type u} (F : SimpleGraph T) : Prop :=
  ∀ (V W : Type u) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    G.Connected → H.Connected → Equivalent (jointLabels G) (jointLabels H) → homCount F G = homCount F H

/-- The manuscript’s classification for all finite simple patterns. -/
theorem classification {T : Type u} [Fintype T] (F : SimpleGraph T) : CountablePattern F ↔ F.IsAcyclic := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨V, finite, G, H, hg, hh, _, _, he, hlt⟩ := cyclic_witness F hn
    exact (Nat.ne_of_lt hlt) (h V V G H hg hh he).symm
  · intro hf V W _ _ G H hg hh he
    exact forests_countable F G H hf hg hh he

/-- No family of ordinary pattern counts characterizes joint GD-WL equivalence
on connected hosts. The arbitrary family may select patterns of every size. -/
theorem no_hom_family (family : (T : Type) → [Fintype T] → SimpleGraph T → Prop) :
    ¬ (∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      G.Connected → H.Connected →
      (Equivalent (jointLabels G) (jointLabels H) ↔
        ∀ (T : Type) [Fintype T] (F : SimpleGraph T), family T F → homCount F G = homCount F H)) := by
  intro h
  have forest (T : Type) [Fintype T] (F : SimpleGraph T) (hf : family T F) : F.IsAcyclic := by
    apply (classification F).mp
    intro V W _ _ G H hg hh he
    exact (h V W G H hg hh).mp he T F hf
  apply cubic_distinguished
  apply (h (Fin 8) (Fin 8) cube chorded cube_connected chorded_connected).mpr
  intro T _ F hf
  exact cubic_forests F (forest T F hf)

end JointForest
