module

public import SolvedProblems.ResistanceMetricCheck

@[expose] public section

namespace ResistanceLifts

theorem route (t : Bool) (z : Terminal) (x : Vertex) :
    ∃ p : (graph t).Walk x (terminal z), p.length = distanceTo t x z := by
  by_cases h : x = terminal z
  · subst x
    exact ⟨.nil, ((distance_valid t z _).1.mpr rfl).symm⟩
  · obtain ⟨y, hy, hd⟩ := (distance_valid t z x).2.2 h
    change distanceTo t y z + 1 = distanceTo t x z at hd
    have ha : (graph t).Adj x y := hy
    obtain ⟨p, hp⟩ := route t z y
    exact ⟨.cons ha p, by simpa only [SimpleGraph.Walk.length_cons, hp] using hd⟩
termination_by distanceTo t x z
decreasing_by omega

theorem connected (t : Bool) : (graph t).Connected := by
  apply ((graph t).connected_iff_exists_forall_reachable).mpr
  refine ⟨terminal (0,false), fun w => ?_⟩
  obtain ⟨p, _⟩ := route t (0,false) w
  exact p.reachable.symm

theorem distance_to_terminal (t : Bool) (x : Vertex) (z : Terminal) :
    (graph t).dist x (terminal z) = distanceTo t x z := by
  obtain ⟨p,hp⟩ := route t z x
  apply le_antisymm (hp ▸ SimpleGraph.dist_le p)
  obtain ⟨w,hw⟩ := (connected t).exists_walk_length_eq_dist x (terminal z)
  rw [← hw]
  have bound {a b : Vertex} (q : (graph t).Walk a b) :
      distanceTo t a z ≤ q.length + distanceTo t b z := by
    induction q with
    | nil => simp
    | cons h _ ih =>
      have hs := (distance_valid t z _).2.1 _ h
      dsimp only at hs
      simp only [SimpleGraph.Walk.length_cons]
      omega
  simpa only [(distance_valid t z _).1.mpr rfl, Nat.add_zero] using bound w

/-- With the twisted direct side, the terminal offsets 0,0,1 extend by alternating
parity along each of the even-length paths. -/
def bipartition (x : Vertex) : Fin 2 :=
  let a := ends true x
  if xor x.2 (xor (a.left.1.val == 2) (a.pos % 2 == 1)) then 1 else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem bipartition_valid : ∀ x : Vertex, ∀ y ∈ neighbors true x,
    bipartition x ≠ bipartition y := by decide +kernel

theorem twisted_bipartite : (graph true).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk bipartition fun h => bipartition_valid _ _ h⟩

theorem untwisted_triangle : ∃ a b c, (graph false).Adj a b ∧ (graph false).Adj b c ∧
    (graph false).Adj c a := by
  refine ⟨(base 0,false),(base 1,false),(base 2,false),?_⟩
  decide

end ResistanceLifts
