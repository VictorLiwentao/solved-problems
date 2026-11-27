module

public import SolvedProblems.JointForestCubic
public import SolvedProblems.JointForestCone

@[expose] public section

namespace JointForest

open SimpleGraph

/-- Every finite forest has the same homomorphism count in two connected hosts
with equal joint shortest-path/resistance color histograms in every round. -/
theorem forests_countable {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (F : SimpleGraph U) (G : SimpleGraph V) (H : SimpleGraph W) (hF : F.IsAcyclic)
    (hG : G.Connected) (hH : H.Connected) (h : Equivalent (jointLabels G) (jointLabels H)) :
    homCount F G = homCount F H := by
  rw [← partition_one, ← partition_one]
  exact weighted_invariance (recognizes_joint G hG) (recognizes_joint H hH) h
    (Fintype.card U) U F le_rfl hF 0 (fun _ _ => 1)

universe u

/-- Forest counts alone do not characterize the joint transformer, already on
the cube and the antipodally chorded eight-cycle from the manuscript. -/
theorem forest_pair : cube.Connected ∧ chorded.Connected ∧
    (∀ {U : Type u} [Fintype U] (F : SimpleGraph U), F.IsAcyclic → homCount F cube = homCount F chorded) ∧
    ¬ Equivalent (jointLabels cube) (jointLabels chorded) :=
  ⟨cube_connected, chorded_connected, cubic_forests, cubic_distinguished⟩

end JointForest
