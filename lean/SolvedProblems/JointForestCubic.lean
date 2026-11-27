module

public import SolvedProblems.JointForestRefinement

@[expose] public section

namespace JointForest

open SimpleGraph

/-- In binary coordinates, cube neighbors differ in exactly one digit. -/
def cubeSide (u v : Fin 8) : Bool :=
  let diff := u.val ^^^ v.val
  diff == 1 || diff == 2 || diff == 4

def cube : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun u v => cubeSide u v = true)

/-- The eight-cycle with additional opposite-vertex edges. -/
def chordSide (u v : Fin 8) : Bool := u+1 == v || u+4 == v

def chorded : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun u v => chordSide u v = true)

instance : DecidableRel cube.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun u v => cubeSide u v = true)).Adj)

instance : DecidableRel chorded.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun u v => chordSide u v = true)).Adj)

/-- Coarse labels recognize equality and adjacency, ignoring all other distances. -/
def coarse {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℕ × ℚ := (if u = v then 0 else if G.Adj u v then 1 else 2, 0)

theorem recognizes_coarse {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Recognizes G (coarse G) := by
  constructor <;> intro u v <;> unfold coarse <;> by_cases h : u = v
  · subst v; simp
  · split_ifs <;> simp_all
  · subst v; simp
  · split_ifs <;> simp_all

/-- In both cubic graphs each row contains one diagonal, three neighbors and
four nonneighbors. The finite computation compares all 64 pairs of rows. -/
theorem coarse_rows (u v : Fin 8) :
    Finset.univ.val.map (coarse cube u) = Finset.univ.val.map (coarse chorded v) := by
  decide +revert

theorem coarse_equivalent : Equivalent (coarse cube) (coarse chorded) := by
  have hu (n : ℕ) : ∃ c : Color n,
      (∀ u, color (coarse cube) n u = c) ∧ (∀ v, color (coarse chorded) n v = c) := by
    induction n with
    | zero => exact ⟨(), fun _ => rfl, fun _ => rfl⟩
    | succ n ih =>
      obtain ⟨c, hc, hd⟩ := ih
      let encode (p : ℕ × ℚ) := (p.1, p.2, c)
      have hr (u v : Fin 8) : color (coarse cube) (n+1) u = color (coarse chorded) (n+1) v := by
        have h := congrArg (Multiset.map encode) (coarse_rows u v)
        change (_ : Multiset (ℕ × ℚ × Color n)) = _
        simpa only [color, hc, hd, Multiset.map_map, Function.comp_def, encode] using h
      exact ⟨_, fun u => hr u 0, fun v => (hr 0 v).symm.trans (hr 0 0)⟩
  intro n
  obtain ⟨c, hc, hd⟩ := hu n
  simp only [hc, hd]

/-- The two explicit cubic graphs agree on every ordinary forest count. -/
theorem cubic_forests {U : Type*} [Fintype U] (F : SimpleGraph U) (hF : F.IsAcyclic) :
    homCount F cube = homCount F chorded := by
  rw [← partition_one, ← partition_one]
  exact weighted_invariance (recognizes_coarse _) (recognizes_coarse _) coarse_equivalent
    (Fintype.card U) U F le_rfl hF 0 (fun _ _ => 1)

theorem cube_connected : cube.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable cube).mpr
  refine ⟨0, fun u => ?_⟩
  have paths : ∀ i : Fin 8, 0 = i ∨ cube.Adj 0 i ∨
      (∃ j, cube.Adj 0 j ∧ cube.Adj j i) ∨ ∃ j k, cube.Adj 0 j ∧ cube.Adj j k ∧ cube.Adj k i := by decide
  rcases paths u with rfl | h | ⟨j,h,h'⟩ | ⟨j,k,h,h',h''⟩
  · exact .refl _
  · exact h.reachable
  · exact h.reachable.trans h'.reachable
  · exact h.reachable.trans (h'.reachable.trans h''.reachable)

theorem chorded_two_step (u v : Fin 8) :
    u = v ∨ chorded.Adj u v ∨ ∃ j, chorded.Adj u j ∧ chorded.Adj j v := by decide +revert

theorem chorded_connected : chorded.Connected where
  preconnected u v := by
    rcases chorded_two_step u v with rfl | h | ⟨j,h,h'⟩
    · exact .refl _
    · exact h.reachable
    · exact h.reachable.trans h'.reachable

theorem chorded_diameter (u v : Fin 8) : chorded.dist u v ≤ 2 := by
  rcases chorded_two_step u v with rfl | h | ⟨j,h,h'⟩
  · simp
  · simp [chorded.dist_eq_one_iff_adj.mpr h]
  · simpa using SimpleGraph.dist_le (.cons h (.cons h' .nil))

theorem cube_opposites : 2 < cube.dist 0 7 := by
  have hnone : ∀ j, ¬(cube.Adj 0 j ∧ cube.Adj 7 j) := by decide
  have h : 2 < cube.edist 0 7 := cube.two_lt_edist_iff.mpr ⟨by decide, by decide, by
    ext j
    simpa only [SimpleGraph.mem_commonNeighbors, Set.mem_empty_iff_false, iff_false] using hnone j⟩
  rw [← (cube_connected 0 7).coe_dist_eq_edist] at h
  exact_mod_cast h

/-- The model separates these graphs in its very first joint round. -/
theorem cubic_distinguished : ¬ Equivalent (jointLabels cube) (jointLabels chorded) := by
  intro he
  have houter := Multiset.mem_map_of_mem (color (jointLabels cube) 1) (Finset.mem_univ_val (0 : Fin 8))
  rw [he 1] at houter
  obtain ⟨v, _, hv⟩ := Multiset.mem_map.mp houter
  let mark : ℕ × ℚ × Color 0 := (cube.dist 0 7, resistance cube 0 7, ())
  have hmark : mark ∈ (color (jointLabels cube) 1 0 : Multiset (ℕ × ℚ × Color 0)) :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ_val (7 : Fin 8))
  rw [← hv] at hmark
  obtain ⟨w, _, hw⟩ := Multiset.mem_map.mp hmark
  have hd : chorded.dist v w = cube.dist 0 7 := congrArg Prod.fst hw
  exact (not_lt_of_ge (hd ▸ chorded_diameter v w)) cube_opposites

end JointForest
