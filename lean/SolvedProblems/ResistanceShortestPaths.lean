module

public import SolvedProblems.ResistanceDistances
public import SolvedProblems.ResistanceSoundness

@[expose] public section

namespace ResistanceLifts

/-- The first signature determines the degree by counting the distance-one entries. -/
def seenDegree (c : Color ℕ Unit 1) : ℕ := c.2.countP (fun k => k.1 = 1)

/-- The second signature counts nearby vertices that had terminal degree at round one. -/
def seenTerminals (c : Color ℕ Unit 2) : ℕ :=
  c.2.countP (fun k => k.1 ≤ 3 ∧ seenDegree k.2 = 10)

theorem count_histogram {V A : Type*} [Fintype V] (f : V → A) (p : A → Prop)
    [DecidablePred p] : (histogram f).countP p = (Finset.univ.filter (fun v => p (f v))).card := by
  rw [histogram, Multiset.countP_map]
  rfl

theorem seen_degree (G : SimpleGraph Vertex) [DecidableRel G.Adj] (x : Vertex) :
    seenDegree (refine G.dist (fun _ => ()) 1 x) = G.degree x := by
  unfold seenDegree
  change (histogram (V := Vertex) _).countP _ = _
  rw [count_histogram, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply congrArg Finset.card
  ext v
  simp [SimpleGraph.dist_eq_one_iff_adj]

def terminalIndex (v : Vertex) : Terminal := (Fin.ofNat 3 v.1.val, v.2)

def nearCount (t : Bool) (x : Vertex) : ℕ :=
  (Finset.univ.filter (fun y : Vertex => distanceTo t x (terminalIndex y) ≤ 3 ∧ y.1.val < 3)).card

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem terminal_checks :
    (∀ y : Vertex, y.1.val < 3 → terminal (terminalIndex y) = y) ∧
    (∀ t y, (neighbors t y).length = 10 ↔ y.1.val < 3) ∧
    (∀ t x, x.1.val < 3 → nearCount t x = if t then 6 else 3) := by decide +kernel

theorem seen_terminals (t : Bool) (x : Vertex) :
    seenTerminals (refine (graph t).dist (fun _ => ()) 2 x) = nearCount t x := by
  unfold seenTerminals
  change (histogram (V := Vertex) _).countP _ = _
  rw [count_histogram]
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, seen_degree, degree_eq_length,
    terminal_checks.2.1]
  by_cases h : y.1.val < 3
  · have hd := distance_to_terminal t x (terminalIndex y)
    rw [terminal_checks.1 y h] at hd
    simp [hd, h]
  · simp [h]

theorem shortest_paths_differ :
    histogram (refine (graph false).dist (fun _ => ()) 2) ≠
      histogram (refine (graph true).dist (fun _ => ()) 2) := by
  let x : Vertex := (base 0,false)
  have hx : x.1.val < 3 := by decide
  intro h
  have hm : refine (graph false).dist (fun _ => ()) 2 x ∈
      histogram (refine (graph true).dist (fun _ => ()) 2) := by
    rw [← h]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val x)
  obtain ⟨y, _, heq⟩ := Multiset.mem_map.mp hm
  have hdegrees := congrArg (fun c : Color ℕ Unit 2 => seenDegree c.1) heq
  change seenDegree (refine (graph true).dist _ 1 y) = seenDegree (refine (graph false).dist _ 1 x) at hdegrees
  rw [seen_degree, seen_degree, degree_eq_length, degree_eq_length] at hdegrees
  have hy : y.1.val < 3 := (terminal_checks.2.1 true y).mp
    (hdegrees.trans ((terminal_checks.2.1 false x).mpr hx))
  have hc := congrArg seenTerminals heq
  rw [seen_terminals, seen_terminals, terminal_checks.2.2 true y hy, terminal_checks.2.2 false x hx] at hc
  contradiction

end ResistanceLifts
