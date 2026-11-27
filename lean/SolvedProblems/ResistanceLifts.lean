module

public import SolvedProblems.ResistanceCertificates
public import SolvedProblems.ResistanceRefinement
public import SolvedProblems.ResistanceShortestPaths
public import SolvedProblems.ResistanceSpectrum

@[expose] public section

namespace ResistanceLifts

/-- A counterexample to both implications in Zhang, Luo, Wang and He, Section 6.
The 78-vertex graphs are connected and simple. Starting with any fiber labeling,
all resistance-refinement colors agree, even between opposite sheets. With
constant starting features, round two of shortest-path refinement distinguishes
the graphs. Their ordinary Laplacian characteristic polynomials differ as well. -/
theorem separation : ∃ G H : SimpleGraph Vertex,
    G.Connected ∧ H.Connected ∧ H.IsBipartite ∧
    (∃ x y z, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x) ∧
    (∀ (A : Type) (features : Fin 39 → A) (depth : ℕ) (v : Fin 39) (e s : Bool),
      refine (resistance G) (fun x => features x.1) depth (v,e) =
      refine (resistance H) (fun x => features x.1) depth (v,s)) ∧
    histogram (refine G.dist (fun _ => ()) 2) ≠ histogram (refine H.dist (fun _ => ()) 2) ∧
    laplacianPolynomial G ≠ laplacianPolynomial H := by
  refine ⟨graph false, graph true, connected false, connected true, twisted_bipartite,
    untwisted_triangle, ?_, shortest_paths_differ, spectra_differ⟩
  intro A features depth v e s
  have pairs : ∀ t a b e, ∃ f : Bool, ∀ u : Bool,
      resistance (graph t) (a,e) (b,u) = resistance (graph false) (a,false) (b,xor u f) := by
    intro t a b e
    obtain ⟨f, hf⟩ := green_pairs t a b e
    refine ⟨f, fun u => ?_⟩
    rw [resistance_from_columns (green_columns t) (connected t),
      resistance_from_columns (green_columns false) (connected false), hf u]
  exact (refine_of_fiber_pairs _ pairs features depth false v e).trans
    (refine_of_fiber_pairs _ pairs features depth true v s).symm

end ResistanceLifts
