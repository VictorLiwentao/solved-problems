module

public import SolvedProblems.DominationEmbedding
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace DominationVC

/-- A shattered set with at least twice the two-block/two-marker budget forces
an induced copy of every prescribed co-bipartite graph of the given side sizes. -/
theorem shattering {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b : ℕ} (P : Fin a → Fin b → Prop) (S : Finset V)
    (hs : (closedFamily (incomparability V)).Shatters S) (hsize : threshold a b ≤ S.card) :
    Nonempty (twoCliques P ↪g incomparability V) := by
  classical
  let m := max 1 (Nat.clog 2 (b^2))
  have hbits : Fintype.card (Index b) ≤ Fintype.card (Fin m → Bool) := by
    simpa only [Index, Fintype.card_prod, Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool,
      ← sq] using (Nat.clog_le_iff_le_pow (b := 2) (by decide)).1 (le_max_right 1 (Nat.clog 2 (b^2)))
  obtain ⟨code⟩ := Function.Embedding.nonempty_of_card_le hbits
  obtain ⟨array⟩ := array_exists hs (m := m) hsize P code
  exact array.induced_copy (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..))

/-- The VC dimension of closed neighborhoods is below the explicit threshold
in every finite incomparability graph avoiding a fixed induced co-bipartite graph. -/
theorem vc_bound {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b : ℕ} (P : Fin a → Fin b → Prop) (avoids : ¬ Nonempty (twoCliques P ↪g incomparability V)) :
    (closedFamily (incomparability V)).vcDim < threshold a b := by
  classical
  have pos : 0 < threshold a b := by unfold threshold; omega
  apply lt_of_le_of_lt (b := threshold a b - 1) _ (by omega)
  apply Finset.sup_le
  intro s hs
  have hsmall : ¬threshold a b ≤ s.card := fun h => avoids (shattering P s (Finset.mem_shatterer.mp hs) h)
  omega

end DominationVC
