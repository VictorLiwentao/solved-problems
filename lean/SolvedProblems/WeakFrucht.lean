module

public import SolvedProblems.WeakFruchtRestore

public section

namespace WeakFrucht

/-- From a single uniform supply of distinct connected graph labels on finite
records, the expansion and restoration give the required decoration of every
extensional accessible pointed digraph. -/
theorem reusable_labels_suffice (em : ∀ p : Prop, p ∨ ¬p)
    (supply : ∀ I : Type u, ∃ Q : Type u, Nonempty (Labels I Q))
    {V : Type u} (D : V → V → Prop) (o : V) (acc : AccessibleFrom D o) (extD : Extensional D) :
    Nonempty (Representation.{u,u} D o) := by
  apply from_leafless em _ D o acc extD
  intro I E i _ leafless
  obtain ⟨Q,⟨labels⟩⟩ := supply I
  exact leafless_representation i E leafless labels

end WeakFrucht
