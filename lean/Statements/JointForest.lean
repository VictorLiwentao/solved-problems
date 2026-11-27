module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace JointForest

open SimpleGraph

/-- The unit-resistor effective resistance. Ground `v`, inject one unit at `u`,
and read the voltage at `u` from the inverse grounded Laplacian. The theorems
using this encoding assume that the graph is connected. -/
noncomputable def resistance {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : ℚ := by
  classical
  exact if h : u = v then 0 else
    ((G.lapMatrix ℚ).submatrix (Subtype.val : {w // w ≠ v} → V) (Subtype.val : {w // w ≠ v} → V))⁻¹ ⟨u,h⟩ ⟨u,h⟩

/-- Every color records the multiset itself, an injective choice of encoding. -/
abbrev Color : ℕ → Type
  | 0 => Unit
  | n + 1 => Multiset (ℕ × ℚ × Color n)

/-- Joint distance refinement, parameterized by its two pair labels. -/
noncomputable def color {V : Type*} [Fintype V] (labels : V → V → ℕ × ℚ) :
    (n : ℕ) → V → Color n
  | 0, _ => ()
  | n + 1, u => Finset.univ.val.map fun v =>
      ((labels u v).1, (labels u v).2, color labels n v)

noncomputable def jointLabels {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : ℕ × ℚ :=
  (G.dist u v, resistance G u v)

/-- Hosts agree if their vertex-color histograms agree at every finite round. -/
def Equivalent {V W : Type*} [Fintype V] [Fintype W]
    (a : V → V → ℕ × ℚ) (b : W → W → ℕ × ℚ) : Prop :=
  ∀ n, Finset.univ.val.map (color a n) = Finset.univ.val.map (color b n)

/-- Ordinary, unnormalized homomorphism counts, including repeated images. -/
noncomputable def homCount {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V) : ℕ :=
  Nat.card (F →g G)

end JointForest

namespace JointForest

open SimpleGraph SimpleGraph.Walk

attribute [local instance] Classical.propDecidable

/-- A vertex at one end of a longest path has at most one neighbor. In an
edgeless forest any other vertex can play the role of `p`. -/
theorem exists_leaf {U : Type*} [Fintype U] [Nontrivial U] (F : SimpleGraph U)
    (hF : F.IsAcyclic) : ∃ l p : U, p ≠ l ∧ ∀ q, F.Adj l q → q = p := by
  classical
  obtain ⟨l, r, t, ht, hmax⟩ := exists_isPath_forall_isPath_length_le_length F
  by_cases h : t.Nil
  · obtain ⟨p, hp⟩ := exists_ne l
    refine ⟨l, p, hp, fun q hq => ?_⟩
    have := hmax _ _ hq.toWalk hq.isPath_toWalk
    simp [SimpleGraph.Walk.length_eq_zero_iff.mpr h] at this
  · refine ⟨l, t.snd, (t.adj_snd h).ne.symm, fun q hq => ?_⟩
    apply hF.eq_snd_of_adj_start ht hq
    have hn : ¬(t.cons hq.symm).IsPath := by
      intro hc
      simpa using hmax _ _ _ hc
    grind [ht.cons]

/-- Whether an unconstrained vertex map preserves all edges. -/
def Preserves {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V) (f : U → V) : Prop :=
  ∀ ⦃i j⦄, F.Adj i j → G.Adj (f i) (f j)

/-- Weighted count, with one local weight for each vertex of the pattern. -/
noncomputable def weightTerm {U V : Type*} [Fintype U] (F : SimpleGraph U) (G : SimpleGraph V)
    (w : U → V → ℕ) (f : U → V) : ℕ := by
  classical
  exact if Preserves F G f then ∏ i, w i (f i) else 0

noncomputable def partition {U V : Type*} [Fintype U] [Fintype V] (F : SimpleGraph U)
    (G : SimpleGraph V) (w : U → V → ℕ) : ℕ := by
  classical
  exact ∑ f : U → V, weightTerm F G w f

/-- Deleting the leaf leaves the restriction of the assignment and at most one
new edge constraint involving its value. -/
theorem preserves_remove {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V)
    {l p : U} (hn : ∀ q, F.Adj l q → q = p) (f : U → V) :
    Preserves F G f ↔
      Preserves (F.comap (Subtype.val : {q // q ≠ l} → U)) G (fun q => f q.1) ∧
      (F.Adj l p → G.Adj (f l) (f p)) := by
  refine ⟨fun h => ⟨fun _ _ he => h he, fun he => h he⟩, ?_⟩
  rintro ⟨hr, he⟩ i j hij
  by_cases hi : i = l
  · subst i
    cases hn j hij
    exact he hij
  by_cases hj : j = l
  · subst j
    cases hn i hij.symm
    exact (he hij.symm).symm
  · exact hr (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij

/-- The contribution of the removed leaf to the weight of its parent. -/
noncomputable def leafSum {U V : Type*} [Fintype V] (F : SimpleGraph U) (G : SimpleGraph V)
    (w : U → V → ℕ) (l p : U) (v : V) : ℕ := by
  classical
  exact ∑ u, if F.Adj l p → G.Adj u v then w l u else 0

noncomputable def deleteWeights {U V : Type*} [Fintype V] (F : SimpleGraph U) (G : SimpleGraph V)
    (w : U → V → ℕ) (l p : U) (q : {i : U // i ≠ l}) (v : V) : ℕ := by
  classical
  exact w q v * (if q.val = p then leafSum F G w l p v else 1)

theorem factor_term {U V : Type*} [Fintype U] (F : SimpleGraph U) (G : SimpleGraph V)
    {l p : U} (hn : ∀ q, F.Adj l q → q = p) (w : U → V → ℕ) (f : U → V) :
    weightTerm F G w f = weightTerm (F.comap (Subtype.val : {q // q ≠ l} → U)) G (fun q => w q.val)
      (fun q => f q.val) * (if F.Adj l p → G.Adj (f l) (f p) then w l (f l) else 0) := by
  classical
  unfold weightTerm
  rw [preserves_remove F G hn, Fintype.prod_eq_mul_prod_subtype_ne (fun i => w i (f i)) l]
  split_ifs <;> simp_all [Nat.mul_comm]

theorem delete_weights_term {U V : Type*} [Fintype U] [Fintype V] (F : SimpleGraph U)
    (G : SimpleGraph V) (w : U → V → ℕ) {l p : U} (hp : p ≠ l) (g : {q // q ≠ l} → V) :
    weightTerm (F.comap (Subtype.val : {q // q ≠ l} → U)) G (deleteWeights F G w l p) g =
      weightTerm (F.comap (Subtype.val : {q // q ≠ l} → U)) G (fun q => w q.val) g * leafSum F G w l p (g ⟨p,hp⟩) := by
  classical
  unfold weightTerm deleteWeights
  split_ifs with h
  · rw [Finset.prod_mul_distrib]
    congr 1
    let parent : {q // q ≠ l} := ⟨p,hp⟩
    simpa only [Subtype.ext_iff, parent] using
      Fintype.prod_ite_eq' parent (fun q => leafSum F G w l p (g q))
  · simp

/-- Sum out the leaf. This identity also covers an isolated vertex, in which
case every host vertex contributes regardless of the chosen parent. -/
theorem partition_delete {U V : Type*} [Fintype U] [Fintype V] (F : SimpleGraph U)
    (G : SimpleGraph V) (w : U → V → ℕ) {l p : U} (hp : p ≠ l)
    (hn : ∀ q, F.Adj l q → q = p) :
    partition F G w = partition (F.comap (Subtype.val : {q // q ≠ l} → U)) G (deleteWeights F G w l p) := by
  classical
  let e := (Equiv.funSplitAt l V).trans (Equiv.prodComm ..)
  unfold partition
  rw [← e.symm.sum_comp (weightTerm F G w), Fintype.sum_prod_type]
  apply Finset.sum_congr (Finset.ext (fun _ => by simp))
  intro g _
  rw [delete_weights_term F G w hp, leafSum, Finset.mul_sum]
  apply Finset.sum_congr (Finset.ext (fun _ => by simp))
  intro u _
  let f := e.symm (g,u)
  have h1 : (fun q : {q // q ≠ l} => f q.val) = g := congrArg Prod.fst (e.apply_symm_apply (g,u))
  have h2 : f l = u := congrArg Prod.snd (e.apply_symm_apply (g,u))
  have h3 : f p = g ⟨p,hp⟩ := congrFun h1 ⟨p,hp⟩
  change weightTerm F G w f = _
  rw [factor_term F G hn, h1, h2, h3]

end JointForest

namespace JointForest

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Zero marks the diagonal and one marks neighbors in the first coordinate. -/
structure Recognizes {V : Type*} (G : SimpleGraph V) (a : V → V → ℕ × ℚ) : Prop where
  zero : ∀ u v, (a u v).1 = 0 ↔ u = v
  one : ∀ u v, (a u v).1 = 1 ↔ G.Adj u v

theorem recognizes_joint {V : Type*} [Fintype V] (G : SimpleGraph V) (h : G.Connected) :
    Recognizes G (jointLabels G) := ⟨fun _ _ => h.dist_eq_zero_iff, fun _ _ => G.dist_eq_one_iff_adj⟩

/-- Read a sum of old-color weights at vertices with the chosen distance labels. -/
noncomputable def readSum {n : ℕ} (ok : ℕ → Prop) (w : Color n → ℕ) (c : Color (n+1)) : ℕ :=
  (c.map fun t => if ok t.1 then w t.2.2 else 0).sum

theorem read_color {V : Type*} [Fintype V] (a : V → V → ℕ × ℚ) (v : V) (n : ℕ)
    (ok : ℕ → Prop) (w : Color n → ℕ) :
    readSum ok w (color a (n+1) v) = ∑ u, if ok (a v u).1 then w (color a n u) else 0 := by
  simp only [readSum, color, Multiset.map_map, Finset.sum, Function.comp_def]

theorem read_self {V : Type*} [Fintype V] {G : SimpleGraph V} {a : V → V → ℕ × ℚ}
    (ha : Recognizes G a) (v : V) (n : ℕ) (w : Color n → ℕ) :
    readSum (· = 0) w (color a (n+1) v) = w (color a n v) := by
  rw [read_color]
  simp [ha.zero]

/-- Transform the old vertex weights once in a way common to both hosts. -/
noncomputable def nextWeights {U : Type*} (F : SimpleGraph U) {n : ℕ} (w : U → Color n → ℕ)
    (l p : U) (q : {i // i ≠ l}) (c : Color (n+1)) : ℕ :=
  readSum (· = 0) (w q.val) c *
    (if q.val = p then readSum (fun d => F.Adj l p → d = 1) (w l) c else 1)

theorem nextWeights_apply {U V : Type*} [Fintype V] (F : SimpleGraph U) (G : SimpleGraph V)
    {a : V → V → ℕ × ℚ} (ha : Recognizes G a) {n : ℕ} (w : U → Color n → ℕ)
    (l p : U) (q : {i // i ≠ l}) (v : V) :
    nextWeights F w l p q (color a (n+1) v) =
    deleteWeights F G (fun i x => w i (color a n x)) l p q v := by
  unfold nextWeights deleteWeights
  rw [read_self ha]
  split_ifs
  · rw [read_color]
    simp only [leafSum, ha.one, G.adj_comm v]
  · rfl

theorem sum_colors {V W : Type*} [Fintype V] [Fintype W] {a : V → V → ℕ × ℚ}
    {b : W → W → ℕ × ℚ} (he : Equivalent a b) (n : ℕ) (w : Color n → ℕ) :
    ∑ v, w (color a n v) = ∑ u, w (color b n u) := by
  have h := congrArg (fun s : Multiset (Color n) => (s.map w).sum) (he n)
  simpa only [Multiset.map_map, Finset.sum, Function.comp_def] using h

theorem empty_partition {U V : Type*} [IsEmpty U] [Fintype U] [Fintype V] (F : SimpleGraph U)
    (G : SimpleGraph V) (w : U → V → ℕ) : partition F G w = 1 := by
  classical
  have h (f : U → V) : Preserves F G f := fun i => isEmptyElim i
  simp [partition, weightTerm, h]

theorem singleton_partition {U V : Type*} [Unique U] [Fintype U] [Fintype V] (F : SimpleGraph U)
    (G : SimpleGraph V) (w : U → V → ℕ) : partition F G w = ∑ v, w default v := by
  classical
  have h (f : U → V) : Preserves F G f := by
    intro i j hij
    exact (hij.ne (Subsingleton.elim ..)).elim
  simp only [partition, weightTerm, ite_eq_left (h _), Fintype.prod_unique]
  rw [← (Equiv.funUnique U V).sum_comp (w default)]
  exact Finset.sum_congr (Finset.ext (fun _ => by simp)) (fun _ _ => rfl)

universe u

/-- Successive eliminations consume at most one round per pattern vertex. -/
theorem weighted_invariance {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {a : V → V → ℕ × ℚ} {b : W → W → ℕ × ℚ}
    (ha : Recognizes G a) (hb : Recognizes H b) (he : Equivalent a b) :
    ∀ (m : ℕ) (U : Type u) [Fintype U] (F : SimpleGraph U), Fintype.card U ≤ m →
      F.IsAcyclic → ∀ (n : ℕ) (w : U → Color n → ℕ),
      partition F G (fun i x => w i (color a n x)) = partition F H (fun i x => w i (color b n x)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro U _ F hm _ n w
    have : IsEmpty U := Fintype.card_eq_zero_iff.mp (by omega)
    rw [empty_partition, empty_partition]
  | succ m ih =>
    intro U _ F hm hF n w
    cases subsingleton_or_nontrivial U with
    | inl hs =>
      cases isEmpty_or_nonempty U with
      | inl h => rw [empty_partition, empty_partition]
      | inr h =>
        let : Unique U := { default := Classical.choice h, uniq := fun _ => Subsingleton.elim .. }
        rw [singleton_partition, singleton_partition]
        exact sum_colors he n (w default)
    | inr ht =>
      obtain ⟨l, p, hp, hn⟩ := exists_leaf F hF
      rw [partition_delete F G _ hp hn, partition_delete F H _ hp hn]
      have hc : Fintype.card {q : U // q ≠ l} < Fintype.card U := Fintype.card_subtype_lt (x := l) (by simp)
      have hsub := hF.of_comap (Function.Embedding.subtype (· ≠ l))
      have h := ih _ (F.comap (Subtype.val : {q // q ≠ l} → U)) (by omega) hsub (n+1) (nextWeights F w l p)
      simpa only [nextWeights_apply F G ha, nextWeights_apply F H hb] using h

/-- Constant unit weights count graph homomorphisms themselves. -/
theorem partition_one {U V : Type*} [Fintype U] [Fintype V] (F : SimpleGraph U) (G : SimpleGraph V) :
    partition F G (fun _ _ => 1) = homCount F G := by
  classical
  let e : (F →g G) ≃ {f : U → V // Preserves F G f} :=
    { toFun := fun h => ⟨h, fun _ _ => h.map_rel'⟩
      invFun := fun f => ⟨f.val, fun h => f.property h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [homCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [partition, weightTerm, Finset.sum_boole]

end JointForest

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

namespace JointForest

open SimpleGraph

/-- Add one loopless vertex adjacent to every old vertex. -/
def cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | some u, some v => G.Adj u v
    | _, _ => True
  symm := ⟨fun u v => by cases u <;> cases v <;> first | exact fun h => h | exact fun h => G.symm.symm _ _ h⟩
  loopless := ⟨fun u => by cases u <;> simp⟩

/-- Candidate preimages of the cone vertex. -/
abbrev Independent {U : Type*} (F : SimpleGraph U) :=
  {s : Set U // ∀ u ∈ s, ∀ v ∈ s, ¬ F.Adj u v}

/-- Remove the specified preimage of the hub from the pattern. -/
def outside {U : Type*} (F : SimpleGraph U) (s : Independent F) :
    SimpleGraph {u // u ∉ s.val} := F.comap Subtype.val

def hubSet {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} (f : F →g cone G) : Independent F :=
  ⟨{u | f u = none}, fun u (hu : f u = none) v (hv : f v = none) huv => by
    have h := f.map_adj huv
    rw [hu, hv] at h
    exact h⟩

abbrev HubFiber {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V) (s : Independent F) :=
  {f : F →g cone G // hubSet f = s}

theorem in_hub_iff {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) (x : U) : x ∈ s.val ↔ f.val x = none := by
  exact Iff.of_eq (congrArg (fun t : Independent F => x ∈ t.val) f.property.symm)

def rimVal {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) (x : {u // u ∉ s.val}) : V :=
  (f.val x.val).get (Option.isSome_iff_ne_none.mpr fun h => x.property ((in_hub_iff f _).mpr h))

theorem some_rimVal {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) (x : {u // u ∉ s.val}) : some (rimVal f x) = f.val x.val := Option.some_get _

def restrictHub {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) : outside F s →g G where
  toFun := rimVal f
  map_rel' := fun {x y} h => by
    have hh := f.val.map_adj (show F.Adj x.val y.val from h)
    rw [← some_rimVal f x, ← some_rimVal f y] at hh
    exact hh

noncomputable def extendHub {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : outside F s →g G) : F →g cone G := by
  classical
  refine ⟨fun x => if h : x ∈ s.val then none else some (f ⟨x,h⟩), ?_⟩
  intro x y hxy
  split_ifs with hx hy hy
  · exact (s.property x hx y hy hxy).elim
  · trivial
  · trivial
  · exact f.map_adj hxy

theorem extend_hubSet {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : outside F s →g G) : hubSet (extendHub f) = s := by
  classical
  apply Subtype.ext
  ext x
  change (if h : x ∈ s.val then none else some (f ⟨x,h⟩)) = none ↔ _
  split <;> simp_all

/-- Specifying precisely the preimage of the hub leaves an arbitrary rim
homomorphism on the induced complement. -/
noncomputable def hubEquiv {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V) (s : Independent F) :
    HubFiber F G s ≃ (outside F s →g G) where
  toFun := restrictHub
  invFun f := ⟨extendHub f, extend_hubSet f⟩
  left_inv f := by
    classical
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    by_cases h : x ∈ s.val
    · simpa [extendHub, h] using ((in_hub_iff f x).mp h).symm
    · simpa [extendHub, restrictHub, h] using some_rimVal f ⟨x,h⟩
  right_inv r := by
    classical
    apply DFunLike.ext
    intro x
    apply Option.some.inj
    exact (some_rimVal (⟨extendHub r, extend_hubSet r⟩ : HubFiber F G s) x).trans (by simp [extendHub, x.property])

attribute [local instance] Classical.propDecidable

/-- Exact cone homomorphism identity for all finite simple patterns and hosts,
including the empty pattern and empty rim. -/
theorem cone_hom_count {U V : Type*} [Fintype U] [Fintype V] (F : SimpleGraph U) (G : SimpleGraph V) :
    homCount F (cone G) = ∑ s : Independent F, homCount (outside F s) G := by
  classical
  let e := Equiv.sigmaFiberEquiv (hubSet (F := F) (G := G))
  rw [homCount, ← Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun s _ => Nat.card_congr (hubEquiv F G s))

end JointForest

namespace JointForest

open SimpleGraph

/-- Every finite forest has the same homomorphism count in two connected hosts
with equal joint shortest-path/resistance color histograms in every round. -/
theorem forests_countable {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (F : SimpleGraph U) (G : SimpleGraph V) (H : SimpleGraph W) (hF : F.IsAcyclic)
    (hG : G.Connected) (hH : H.Connected) (h : Equivalent (jointLabels G) (jointLabels H)) :
    homCount F G = homCount F H := by
  rw [← partition_one, ← partition_one]
  exact weighted_invariance (recognizes_joint G hG) (recognizes_joint H hH) h
    (Fintype.card U) U F le_rfl hF 0 (fun _ _ => 1)

universe u

/-- Forest counts alone do not characterize the joint transformer, already on
the cube and the antipodally chorded eight-cycle from the manuscript. -/
theorem forest_pair : cube.Connected ∧ chorded.Connected ∧
    (∀ {U : Type u} [Fintype U] (F : SimpleGraph U), F.IsAcyclic → homCount F cube = homCount F chorded) ∧
    ¬ Equivalent (jointLabels cube) (jointLabels chorded) :=
  ⟨cube_connected, chorded_connected, cubic_forests, cubic_distinguished⟩

end JointForest
