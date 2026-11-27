module

public import SolvedProblems.DominationUpper
public import Mathlib.Order.Minimal

@[expose] public section

namespace DominationVC

/-- A dominating set covers each vertex by equality or adjacency. -/
def Dominates {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, v = w ∨ G.Adj v w

/-- A hypergraph transversal hits every hyperedge. -/
def Hits {V : Type*} (edges : Finset (Finset V)) (D : Finset V) : Prop :=
  ∀ E ∈ edges, ∃ w ∈ D, w ∈ E

/-- Keep only inclusion-minimal hyperedges. -/
noncomputable def clean {V : Type*} (edges : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact edges.filter (Minimal (· ∈ edges))

theorem hits_clean {V : Type*} (edges : Finset (Finset V)) (D : Finset V) :
    Hits (clean edges) D ↔ Hits edges D := by
  classical
  constructor
  · intro h E he
    obtain ⟨F, hsub, hmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ edges) E he
    obtain ⟨v,hv,hF⟩ := h F (Finset.mem_filter.mpr ⟨hmin.1,hmin⟩)
    exact ⟨v,hv,hsub hF⟩
  · exact fun h E he => h E (Finset.mem_filter.mp he).1

theorem dominates_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V) :
    Dominates G D ↔ Hits (closedFamily G) D := by
  classical
  constructor
  · intro h E hE
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨w, hw, hvis⟩ := h v
    exact ⟨w, hw, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvis.elim (fun he => Or.inl he.symm) Or.inr⟩⟩
  · intro h v
    let E := Finset.univ.filter fun w => w = v ∨ G.Adj v w
    have he : E ∈ closedFamily G := Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
    obtain ⟨w, hw, hv⟩ := h E he
    exact ⟨w,hw,(Finset.mem_filter.mp hv).2.elim (fun e => Or.inl e.symm) Or.inr⟩

/-- The reduction used by the enumeration theorem. It needs no orientation as
input, outputs at most n hyperedges and preserves the actual inclusion-minimal
solutions. On the promised class its output has the explicit dimension bound. -/
theorem domination_reduction {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b : ℕ} (P : Fin a → Fin b → Prop) (avoids : ¬Nonempty (twoCliques P ↪g incomparability V)) :
    let H := clean (closedFamily (incomparability V))
    H.card ≤ Fintype.card V ∧ H.vcDim < threshold a b ∧
      ∀ D : Finset V, Minimal (Dominates (incomparability V)) D ↔ Minimal (Hits H) D := by
  classical
  dsimp only
  have sub : clean (closedFamily (incomparability V)) ⊆ closedFamily (incomparability V) := Finset.filter_subset ..
  refine ⟨(Finset.card_le_card sub).trans ?_, (Finset.vcDim_mono sub).trans_lt (vc_bound P avoids), ?_⟩
  · exact (Finset.card_image_le.trans (Finset.card_univ.le))
  · intro D
    have he : Dominates (incomparability V) = Hits (clean (closedFamily (incomparability V))) := by
      funext X
      exact propext ((dominates_iff _ _).trans (hits_clean _ _).symm)
    rw [he]

end DominationVC
