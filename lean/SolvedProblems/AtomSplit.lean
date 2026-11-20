module

public import SolvedProblems.AtomSplitModel
import SolvedProblems.AtomSplitBlocks
import SolvedProblems.AtomSplitOrbit

public section

namespace AtomSplit
open Set Equiv

private theorem supported_compl {k} {block : ℕ → Fin k} {X : Type u}
    {act : stabilizer block →* Perm X} {Y : Set X} (h : Supported act Y) : Supported act Yᶜ := by
  obtain ⟨Q,hQ⟩ := h
  exact ⟨Q,fun g h x => not_congr (hQ g h x)⟩

private theorem moving_block_splits {k} {block : ℕ → Fin k} {X : Type u}
    (act : stabilizer block →* Perm X) (hs : LocallySupported act)
    (B : Set ℕ) (bi : B.Infinite) (hB : Inside B ≤ stabilizer block)
    (g : Inside B) (moves : localAction act hB g ≠ 1) :
    ∃ Y : Set X, Supported act Y ∧ Supported act Yᶜ ∧ Y.Infinite ∧ Yᶜ.Infinite := by
  classical
  obtain ⟨U,ub,ui,rest⟩ := split_region bi
  let hU := (inside_mono ub).trans hB
  have nontriv : ∃ u : Inside U, localAction act hU u ≠ 1 := by
    by_contra! all
    apply moves
    apply normal_generation ub ui rest (localAction act hB).ker inferInstance _ g
    intro v hv
    exact all ⟨v.val,hv⟩
  obtain ⟨u,hu⟩ := nontriv
  have moved : ∃ x : X, localAction act hU u x ≠ x := by
    by_contra! all
    exact hu (Equiv.ext all)
  obtain ⟨x,hx⟩ := moved
  let O := orbit act U x
  have supported : Supported act O := orbit_supported act hs U x
  have oi : O.Infinite := by
    intro fin
    exact hx (finite_fixed ui (localAction act hU) (local_pts hs hU)
      fin (orbit_stable act x hU) u x (mem_orbit_self act U x))
  refine ⟨O,supported,supported_compl supported,oi,?_⟩
  intro small
  obtain ⟨Q,hQ⟩ := hs x
  obtain ⟨D,ds,di,cell⟩ := homogeneous rest Q
  have db : D ⊆ B := ds.trans sdiff_subset
  have dis : Disjoint U D := Set.disjoint_left.mpr fun y hy hd => (ds hd).2 hy
  let hD := (inside_mono db).trans hB
  have pointwise (v : Inside D) : ∀ y ∈ O, localAction act hD v y = y := by
    exact orbit_fixed_disjoint act dis v.property
      (hQ (Subgroup.inclusion hD v) (cell _ v.property))
  have invariant (v : Inside D) (y : X) : localAction act hD v y ∈ Oᶜ ↔ y ∈ Oᶜ := by
    apply not_congr
    constructor
    · intro hy
      have eq := (localAction act hD v).injective (pointwise v _ hy)
      exact eq ▸ hy
    · intro hy; rw [pointwise v _ hy]; exact hy
  have other := finite_fixed di (localAction act hD) (local_pts hs hD) small invariant
  have triv (v : Inside D) : localAction act hD v = 1 := by
    apply Equiv.ext; intro y
    by_cases hy : y ∈ O
    · exact pointwise v y hy
    · exact other v y hy
  apply moves
  apply normal_generation db di (ui.mono fun y hy => ⟨ub hy,Set.disjoint_left.mp dis hy⟩)
    (localAction act hB).ker inferInstance _ g
  intro v hv
  exact triv ⟨v.val,hv⟩

/-- Every infinite set of arbitrary rank in Bruce's finite partition model splits
into two infinite supported subsets. The carrier is the external set of its elements. -/
theorem everyInfiniteSetSplits {k : ℕ} (block : ℕ → Fin k) {X : Type u} [Infinite X]
    (act : stabilizer block →* Equiv.Perm X) (hs : LocallySupported act) :
    ∃ Y : Set X, Supported act Y ∧ Supported act Yᶜ ∧ Y.Infinite ∧ Yᶜ.Infinite
    := by
  classical
  rcases pointwise_or_moving act with ⟨Q,all⟩|⟨i,inf,g,inBlock,moved⟩
  · obtain ⟨Y,_,yi,yc⟩ := split_region (Set.infinite_univ (α := X))
    have supported : Supported act Y := ⟨Q,fun g hg x => by rw [all g hg]; rfl⟩
    exact ⟨Y,supported,supported_compl supported,yi,yc.mono (fun _ h => h.2)⟩
  · exact moving_block_splits act hs _ inf (inside_in_stabilizer (fun _ h => h))
      ⟨g.val,inBlock⟩ moved

end AtomSplit
