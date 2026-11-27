module

public import SolvedProblems.JointForestClassification

@[expose] public section

namespace ShortestPathWL

open JointForest SimpleGraph

/-- Injective coding of the extended graph distance in the existing multiset
refinement. Only infinity carries the second-coordinate tag one. -/
noncomputable def distanceCode (d : ℕ∞) : ℕ × ℚ := if d = ⊤ then (2,1) else (d.toNat,0)

theorem distanceCode_injective : Function.Injective distanceCode := by
  intro d e h
  by_cases hd : d = ⊤ <;> by_cases he : e = ⊤ <;> simp [distanceCode, hd, he] at h ⊢
  exact (ENat.natCast_toNat hd).symm.trans ((congrArg Nat.cast h).trans (ENat.natCast_toNat he))

noncomputable def labels {V : Type*} (G : SimpleGraph V) (u v : V) : ℕ × ℚ := distanceCode (G.edist u v)

/-- All synchronized rounds of SPD-WL, including distances to vertices in
other connected components. -/
def Equivalent {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  JointForest.Equivalent (labels G) (labels H)

theorem labels_reachable {V : Type*} (G : SimpleGraph V) {u v : V} (h : G.Reachable u v) :
    labels G u v = (G.dist u v, 0) := by
  simp [labels, distanceCode, (G.edist_ne_top_iff_reachable).mpr h, SimpleGraph.dist]

theorem recognizes {V : Type*} (G : SimpleGraph V) : Recognizes G (labels G) := by
  constructor <;> intro u v <;> by_cases h : G.Reachable u v
  · simpa [labels_reachable G h] using h.dist_eq_zero_iff
  · have he : G.edist u v = ⊤ := G.edist_eq_top_of_not_reachable h
    have hn : u ≠ v := fun e => h (e ▸ SimpleGraph.Reachable.refl _)
    simp [labels,distanceCode, he,hn]
  · simp [labels_reachable G h]
  · have he : G.edist u v = ⊤ := G.edist_eq_top_of_not_reachable h
    have hn : ¬G.Adj u v := fun a => h a.reachable
    simp [labels,distanceCode, he,hn]

/-- Apply a deterministic map to the pair labels in every layer of a color. -/
def projectColor (f : ℕ × ℚ → ℕ × ℚ) : (n : ℕ) → Color n → Color n
  | 0, _ => ()
  | n+1, c => c.map fun (i,r,d) => ((f (i,r)).1, (f (i,r)).2, projectColor f n d)

theorem project_color {V : Type*} [Fintype V] (f : ℕ × ℚ → ℕ × ℚ) (a : V → V → ℕ × ℚ) (n : ℕ) (u : V) :
    projectColor f n (color a n u) = color (fun x y => f (a x y)) n u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => simp only [projectColor, color, Multiset.map_map, Function.comp_def, ih]

theorem project_equiv {V W : Type*} [Fintype V] [Fintype W] (f : ℕ × ℚ → ℕ × ℚ)
    {a : V → V → ℕ × ℚ} {b : W → W → ℕ × ℚ} (he : JointForest.Equivalent a b) :
    JointForest.Equivalent (fun x y => f (a x y)) (fun x y => f (b x y)) := by
  intro n
  have h := congrArg (Multiset.map (projectColor f n)) (he n)
  simpa only [Multiset.map_map, Function.comp_def, project_color] using h

theorem forget_resistance {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (hg : G.Connected) (hh : H.Connected) (he : JointForest.Equivalent (jointLabels G) (jointLabels H)) :
    Equivalent G H := by
  let f (z : ℕ × ℚ) : ℕ × ℚ := (z.1,0)
  have h1 : (fun x y => f (jointLabels G x y)) = labels G :=
    funext fun x => funext fun y => (labels_reachable G (hg x y)).symm
  have h2 : (fun x y => f (jointLabels H x y)) = labels H :=
    funext fun x => funext fun y => (labels_reachable H (hh x y)).symm
  change JointForest.Equivalent (labels G) (labels H)
  simpa only [h1,h2] using (project_equiv f he)

/-- A finite acyclic pattern remains countable for hosts of any connectivity. -/
theorem forests {T V W : Type*} [Fintype T] [Fintype V] [Fintype W] (F : SimpleGraph T)
    (G : SimpleGraph V) (H : SimpleGraph W) (hf : F.IsAcyclic) (he : Equivalent G H) :
    homCount F G = homCount F H := by
  rw [← partition_one, ← partition_one]
  exact weighted_invariance (recognizes G) (recognizes H) he (Fintype.card T) T F le_rfl hf 0 (fun _ _ => 1)

/-- Shortest-path colors distinguish the two cubic graphs by a distance-three
message in round one. -/
theorem cubic_distinction : ¬ Equivalent cube chorded := by
  intro h
  have ho := Multiset.mem_map_of_mem (color (labels cube) 1) (Finset.mem_univ_val (0 : Fin 8))
  rw [h 1] at ho
  obtain ⟨v,_,hv⟩ := Multiset.mem_map.mp ho
  let mark : ℕ × ℚ × Color 0 := ((labels cube 0 7).1, (labels cube 0 7).2, ())
  have hm : mark ∈ color (labels cube) 1 0 := Multiset.mem_map_of_mem _ (Finset.mem_univ_val (7 : Fin 8))
  rw [← hv] at hm
  obtain ⟨w,_,hw⟩ := Multiset.mem_map.mp hm
  have he : (labels chorded v w).1 = (labels cube 0 7).1 := congrArg (fun p : ℕ × ℚ × Color 0 => p.1) hw
  rw [labels_reachable chorded (chorded_connected v w), labels_reachable cube (cube_connected 0 7)] at he
  change chorded.dist v w = cube.dist 0 7 at he
  exact (not_lt_of_ge (he ▸ chorded_diameter v w)) cube_opposites

end ShortestPathWL
