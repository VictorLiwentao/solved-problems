module

public import SolvedProblems.WeakFruchtEmbedding
public import SolvedProblems.WeakFruchtLabels

public section

namespace WeakFrucht

/-- The new direction of the draft, in the pointwise group-action formulation.
Ordinary two-valued propositional logic is explicit. The construction uses
Frucht at the one group of eventual translations associated to the target. -/
theorem action_frucht_implies_cwf [d : ∀ p : Prop, Decidable p] (ft : ActionFrucht.{u})
    {V : Type u} (D : V → V → Prop) (o : V) (acc : AccessibleFrom D o) (extD : Extensional D) :
    Nonempty (Representation.{u,u} D o) :=
  rigid_embeddings_imply_cwf (fun p => match d p with | .isTrue h => Or.inl h | .isFalse h => Or.inr h)
    (embedding_of_actions ft) D o acc extD

/-- Frucht's theorem for full automorphism groups of simple graphs implies
CWFAFA₂ for all extensional accessible pointed directed graphs. -/
theorem frucht_implies_cwf (ft : Frucht.{u}) {V : Type u} (D : V → V → Prop) (o : V)
    (acc : AccessibleFrom D o) (extD : Extensional D) : Nonempty (Representation.{u,u} D o) := by
  classical
  exact action_frucht_implies_cwf (actions_of_frucht ft) D o acc extD

end WeakFrucht
