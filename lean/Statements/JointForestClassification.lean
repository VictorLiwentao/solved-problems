module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.BigOperators.Field

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

namespace JointForest

/-- `continuant (r+1)` is the determinant of the tridiagonal path-interior
matrix of size `r`, with diagonal 3 and consecutive entries −1. -/
def continuant : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => 3 * continuant (n+1) - continuant n

theorem continuant_increasing (i : ℕ) : continuant i < continuant (i+1) := by
  induction i with
  | zero => decide
  | succ i ih => rw [continuant]; omega

abbrev ratCont (i : ℕ) : ℚ := continuant i

@[simp] theorem ratCont_zero : ratCont 0 = 0 := rfl
@[simp] theorem ratCont_one : ratCont 1 = 1 := rfl

theorem ratCont_pos {i : ℕ} (h : 0 < i) : 0 < ratCont i := by
  cases i with
  | zero => omega
  | succ i => exact_mod_cast Nat.zero_lt_of_lt (continuant_increasing i)

theorem ratCont_rec (i : ℕ) : ratCont (i+2) = 3 * ratCont (i+1) - ratCont i := by
  have hn := continuant_increasing i
  change ((3 * continuant (i+1) - continuant i : ℕ) : ℚ) = _
  simp only [ratCont, Nat.cast_sub (by omega : continuant i ≤ 3 * continuant (i+1)),
    Nat.cast_mul, Nat.cast_ofNat]

/-- Discrete Wronskian, used at the vertex carrying the unit current. -/
theorem ratCont_join (a b : ℕ) : ratCont (a+1) * ratCont (b+1) - ratCont a * ratCont b = ratCont (a+b+1) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    have h := ih (b+1)
    rw [ratCont_rec b] at h
    rw [ratCont_rec a]
    rw [show a+1+b+1 = a+(b+1)+1 by omega]
    linear_combination h

/-- Green entry at internal positions `i,j` of a length-`s` path with both
endpoints held at zero. We number the endpoints 0 and `s`. -/
def pathGreen (s i j : ℕ) : ℚ := ratCont (min i j) * ratCont (s - max i j) / ratCont s

theorem pathGreen_symm (s i j : ℕ) : pathGreen s i j = pathGreen s j i := by
  simp only [pathGreen, min_comm i j, max_comm i j]

@[simp] theorem pathGreen_zero (s j : ℕ) : pathGreen s 0 j = 0 := by simp [pathGreen]

@[simp] theorem pathGreen_end (s j : ℕ) : pathGreen s s j = 0 := by
  simp [pathGreen, Nat.sub_eq_zero_of_le (le_max_left s j)]

theorem pathGreen_left {s i j : ℕ} (h : i ≤ j) : pathGreen s i j = ratCont i * ratCont (s-j) / ratCont s := by
  simp [pathGreen, min_eq_left h, max_eq_right h]

theorem pathGreen_right {s i j : ℕ} (h : j ≤ i) : pathGreen s i j = ratCont j * ratCont (s-i) / ratCont s := by
  rw [pathGreen_symm, pathGreen_left h]

theorem ratCont_at {j : ℕ} (hj : 0 < j) : 3 * ratCont j - ratCont (j-1) = ratCont (j+1) := by
  cases j with
  | zero => omega
  | succ j => exact (ratCont_rec j).symm

/-- Applying the interior path operator gives a Kronecker delta. -/
theorem pathGreen_current {s i j : ℕ} (hi : 0 < i) (his : i < s) (hj : 0 < j) (hjs : j < s) :
    3 * pathGreen s i j - pathGreen s (i-1) j - pathGreen s (i+1) j = if i = j then 1 else 0 := by
  have hn := (ratCont_pos (by omega : 0 < s)).ne'
  rcases lt_trichotomy i j with hl | rfl | hr
  · rw [pathGreen_left hl.le, pathGreen_left (by omega : i-1 ≤ j), pathGreen_left (by omega : i+1 ≤ j),
      ite_eq_right hl.ne]
    have h := ratCont_at hi
    field_simp
    linear_combination (ratCont (s-j)) * h
  · rw [pathGreen_left le_rfl, pathGreen_left (by omega : i-1 ≤ i), pathGreen_right (by omega : i ≤ i+1),
      ite_eq_left rfl]
    have h := ratCont_at hi
    have h' := ratCont_join i (s-i-1)
    rw [show s-i-1+1 = s-i by omega, show i+(s-i-1)+1 = s by omega] at h'
    rw [show s-(i+1) = s-i-1 by omega]
    field_simp
    linear_combination (ratCont (s-i)) * h + h'
  · rw [pathGreen_right hr.le, pathGreen_right (by omega : j ≤ i-1), pathGreen_right (by omega : j ≤ i+1),
      ite_eq_right (Ne.symm hr.ne)]
    rw [show s-(i-1) = s-i+1 by omega, show s-(i+1) = s-i-1 by omega]
    have h := ratCont_at (by omega : 0 < s-i)
    field_simp
    linear_combination (ratCont j) * h

/-- The corner inverse entry contributed by a single long path. -/
theorem pathGreen_corner {s : ℕ} (hs : 2 ≤ s) : pathGreen s 1 (s-1) = 1 / ratCont s := by
  rw [pathGreen_left (by omega : 1 ≤ s-1), show s-(s-1) = 1 by omega]
  simp

end JointForest

namespace JointForest

open SimpleGraph

/-- A Boolean sign is relevant only on an edge. The value `true` exchanges sheets. -/
structure Signing (V : Type*) where
  neg : V → V → Bool
  symm : ∀ x y, neg x y = neg y x

def signedLift {V : Type*} (B : SimpleGraph V) (s : Signing V) : SimpleGraph (V × Bool) where
  Adj u v := B.Adj u.1 v.1 ∧ (u.2 ^^ v.2) = s.neg u.1 v.1
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Bool.xor_comm, ← s.symm]; exact h.2⟩⟩
  loopless := ⟨fun u h => B.loopless.irrefl u.1 h.1⟩

/-- Sheet labels extending one specified map into the base. -/
abbrev Sheets {U V : Type*} {K : SimpleGraph U} {B : SimpleGraph V} (s : Signing V) (f : K →g B) :=
  {c : U → Bool // ∀ ⦃u v⦄, K.Adj u v → (c u ^^ c v) = s.neg (f u) (f v)}

def liftData {U V : Type*} (K : SimpleGraph U) (B : SimpleGraph V) (s : Signing V) :
    (K →g signedLift B s) ≃ Σ f : K →g B, Sheets s f where
  toFun h := ⟨⟨fun i => (h i).1, fun he => (h.map_adj he).1⟩,
    ⟨fun i => (h i).2, fun _ _ he => (h.map_adj he).2⟩⟩
  invFun x := ⟨fun i => (x.1 i, x.2.val i), fun h => ⟨x.1.map_adj h, x.2.property h⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem constant_on_walk {U : Type*} {K : SimpleGraph U} {c : U → Bool}
    (h : ∀ ⦃i j⦄, K.Adj i j → c i = c j) {i j : U} (p : K.Walk i j) : c i = c j := by
  induction p with
  | nil => rfl
  | cons e _ ih => exact (h e).trans ih

theorem xor_shift (a b t : Bool) : ((a ^^ t) ^^ (b ^^ t)) = (a ^^ b) := by decide +revert

theorem xor_differences (a b x y : Bool) : (a ^^ b) = (x ^^ y) → (a ^^ x) = (b ^^ y) := by
  decide +revert

theorem xor_recover (a b : Bool) : (a ^^ (a ^^ b)) = b := by decide +revert

/-- Once there is one lift, every other lift differs by one independent sheet
choice on each connected component of the pattern. -/
def sheetsEquiv {U V : Type*} {K : SimpleGraph U} {B : SimpleGraph V} {s : Signing V}
    {f : K →g B} (base : Sheets s f) : (K.ConnectedComponent → Bool) ≃ Sheets s f where
  toFun t := ⟨fun i => base.val i ^^ t (K.connectedComponentMk i), fun i j e => by
    dsimp only
    rw [SimpleGraph.ConnectedComponent.sound e.reachable, xor_shift, base.property e]⟩
  invFun d := ConnectedComponent.lift (fun i => base.val i ^^ d.val i) (fun _ _ p _ =>
    constant_on_walk (fun {i j} e => xor_differences _ _ _ _ ((base.property e).trans (d.property e).symm)) p)
  left_inv t := by
    funext c
    induction c using ConnectedComponent.ind with
    | h i => exact xor_recover ..
  right_inv d := by
    apply Subtype.ext
    funext i
    exact xor_recover ..

/-- The number of lifts of every base map is either zero or exactly two to the
number of connected components, including the unique lift of the empty pattern. -/
theorem sheet_count {U V : Type*} [Finite U] {K : SimpleGraph U} {B : SimpleGraph V}
    (s : Signing V) (f : K →g B) : Nat.card (Sheets s f) =
    (by classical exact if Nonempty (Sheets s f) then 2 ^ Nat.card K.ConnectedComponent else 0) := by
  classical
  split_ifs with hn
  · obtain ⟨c⟩ := hn
    rw [← Nat.card_congr (sheetsEquiv c), Nat.card_fun]
    simp
  · have : IsEmpty (Sheets s f) := not_nonempty_iff.mp hn
    simp

attribute [local instance] Fintype.ofFinite

theorem lift_hom_sum {U V : Type*} [Finite U] [Finite V] (K : SimpleGraph U) (B : SimpleGraph V)
    (s : Signing V) : homCount K (signedLift B s) = ∑ f : K →g B, Nat.card (Sheets s f) := by
  rw [homCount, Nat.card_congr (liftData K B s), Nat.card_sigma]

theorem lift_hom_le {U V : Type*} [Finite U] [Finite V] (K : SimpleGraph U) (B : SimpleGraph V)
    (s t : Signing V) (h : ∀ f : K →g B, Nonempty (Sheets s f)) :
    homCount K (signedLift B t) ≤ homCount K (signedLift B s) := by
  classical
  rw [lift_hom_sum, lift_hom_sum]
  apply Finset.sum_le_sum
  intro f _
  rw [sheet_count, sheet_count]
  split_ifs <;> simp_all

theorem lift_hom_lt {U V : Type*} [Finite U] [Finite V] (K : SimpleGraph U) (B : SimpleGraph V)
    (s t : Signing V) (h : ∀ f : K →g B, Nonempty (Sheets s f)) (f₀ : K →g B)
    (hn : ¬ Nonempty (Sheets t f₀)) : homCount K (signedLift B t) < homCount K (signedLift B s) := by
  classical
  rw [lift_hom_sum, lift_hom_sum]
  apply Finset.sum_lt_sum
  · intro f _
    rw [sheet_count, sheet_count]
    split_ifs <;> simp_all
  · refine ⟨f₀, by simp, ?_⟩
    rw [sheet_count, sheet_count]
    simp [h f₀, hn]

end JointForest

namespace JointForest

open SimpleGraph

/-- Orient every side of the complete template using an external vertex order. -/
abbrev Side (T : Type*) [LT T] := {p : T × T // p.1 < p.2}

abbrev Interior (T : Type*) [LT T] (m r : ℕ) := Side T × Fin m × Fin r
abbrev Base (T : Type*) [LT T] (m r : ℕ) := Sum T (Interior T m r)

/-- Each side keeps its direct edge and receives `m` paths, each with `r`
interior vertices numbered from zero. The resulting path length is `r+1`. -/
def step {T : Type*} [LinearOrder T] {m r : ℕ} : Base T m r → Base T m r → Prop
  | .inl u, .inl v => u < v
  | .inl u, .inr (e,_,j) => (u = e.val.1 ∧ j.val = 0) ∨ (u = e.val.2 ∧ j.val+1 = r)
  | .inr _, .inl _ => False
  | .inr (e,i,j), .inr (d,k,z) => e = d ∧ i = k ∧ j.val+1 = z.val

def expanded (T : Type*) [LinearOrder T] (m r : ℕ) : SimpleGraph (Base T m r) :=
  SimpleGraph.fromRel step

/-- The negative edge is the right terminal edge of each long path. The twist
changes every right-terminal incidence on one side, including its direct edge. -/
def signBit {T : Type*} [LinearOrder T] {m r : ℕ} (twist : Bool) (d : Side T) :
    Base T m r → Base T m r → Bool
  | .inl u, .inl v => twist && decide (s(u,v) = s(d.val.1,d.val.2))
  | .inl u, .inr (e,_,_) | .inr (e,_,_), .inl u => decide (u = e.val.2) && !(twist && decide (e = d))
  | .inr _, .inr _ => false

def signing {T : Type*} [LinearOrder T] {m r : ℕ} (twist : Bool) (d : Side T) : Signing (Base T m r) where
  neg := signBit twist d
  symm u v := by
    cases u with
    | inl u =>
      cases v with
      | inl v => simp only [signBit, Sym2.eq_swap (a := u) (b := v)]
      | inr v => rfl
    | inr u => cases v <;> rfl

/-- A map from fewer than `r` vertices misses a vertex on each long path. -/
theorem missing_position {K T : Type*} [Fintype K] [LinearOrder T] {m r : ℕ}
    (h : Fintype.card K < r) (f : K → Base T m r) (e : Side T) (i : Fin m) :
    ∃ j : Fin r, ∀ x, f x ≠ .inr (e,i,j) := by
  classical
  by_contra! hn
  choose g hg using hn
  have hi : Function.Injective g := by
    intro j k he
    have hval := (hg j).symm.trans ((congrArg f he).trans (hg k))
    simpa using hval
  have hc := Fintype.card_le_of_injective g hi
  simp only [Fintype.card_fin] at hc
  omega

/-- Gauge across the missing interior position. All terminals have zero phase. -/
def phase {T : Type*} [LinearOrder T] {m r : ℕ} (cut : Side T → Fin m → Fin r) : Base T m r → Bool
  | .inl _ => false
  | .inr (e,i,j) => decide ((cut e i).val < j.val)

def avoids {T : Type*} [LinearOrder T] {m r : ℕ} (cut : Side T → Fin m → Fin r) : Base T m r → Prop
  | .inl _ => True
  | .inr (e,i,j) => j ≠ cut e i

theorem phase_step {T : Type*} [LinearOrder T] {m r : ℕ} (cut : Side T → Fin m → Fin r) (d : Side T)
    {u v : Base T m r} (hu : avoids cut u) (hv : avoids cut v) (he : step u v) :
    (phase cut u ^^ phase cut v) = signBit false d u v := by
  cases u with
  | inl u =>
    cases v with
    | inl v => rfl
    | inr v =>
      obtain ⟨e,i,j⟩ := v
      change j ≠ cut e i at hv
      obtain ⟨rfl, hj⟩ | ⟨rfl, hj⟩ := he
      · simp [phase, signBit, hj, ne_of_lt e.property]
      · have hne : j.val ≠ (cut e i).val := fun h => hv (Fin.ext h)
        have hc : (cut e i).val < j.val := by have := (cut e i).isLt; omega
        simp [phase, signBit, hc]
  | inr u =>
    obtain ⟨e,i,j⟩ := u
    cases v with
    | inl v => exact False.elim he
    | inr v =>
      obtain ⟨d',k,z⟩ := v
      rcases he with ⟨rfl, rfl, hz⟩
      have hn : z.val ≠ (cut e i).val := fun h => hv (Fin.ext h)
      have eq : (cut e i).val < j.val ↔ (cut e i).val < z.val := by
        have hn' : j.val ≠ (cut e i).val := fun h => hu (Fin.ext h)
        omega
      simp [phase, signBit, eq]

theorem positive_lift {K T : Type*} [Fintype K] [LinearOrder T] {m r : ℕ} {F : SimpleGraph K}
    (h : Fintype.card K < r) (d : Side T) (f : F →g expanded T m r) : Nonempty (Sheets (signing false d) f) := by
  classical
  choose cut hc using missing_position h f
  have ha (x : K) : avoids cut (f x) := by
    cases hf : f x with
    | inl _ => trivial
    | inr v =>
      obtain ⟨e,i,j⟩ := v
      change j ≠ cut e i
      rintro rfl
      exact hc e i x hf
  refine ⟨⟨fun x => phase cut (f x), fun i j he => ?_⟩⟩
  rcases (f.map_adj he).2 with hstep | hstep
  · exact phase_step cut d (ha i) (ha j) hstep
  · rw [Bool.xor_comm, (signing false d).symm]
    exact phase_step cut d (ha j) (ha i) hstep

/-- Direct template edges give a canonical homomorphism from the pattern. -/
def templateHom {T : Type*} [LinearOrder T] (F : SimpleGraph T) (m r : ℕ) : F →g expanded T m r where
  toFun := .inl
  map_rel' := fun h => ⟨fun e => h.ne (Sum.inl.inj e), lt_or_gt_of_ne h.ne⟩

/-- The direct copy of a cycle through the distinguished edge cannot lift. -/
theorem twisted_no_lift {T : Type*} [LinearOrder T] (F : SimpleGraph T) (m r : ℕ) (d : Side T)
    (hadj : F.Adj d.val.1 d.val.2) (hpath : (F.deleteEdges {s(d.val.1,d.val.2)}).Reachable d.val.1 d.val.2) :
    ¬ Nonempty (Sheets (signing true d) (templateHom F m r)) := by
  rintro ⟨c⟩
  have heq {i j : T} (he : (F.deleteEdges {s(d.val.1,d.val.2)}).Adj i j) : c.val i = c.val j := by
    obtain ⟨hh, hn⟩ := SimpleGraph.deleteEdges_adj.mp he
    have hin := c.property hh
    have hneq : s(i,j) ≠ s(d.val.1,d.val.2) := hn
    change (c.val i ^^ c.val j) = (true && decide (s(i,j) = s(d.val.1,d.val.2))) at hin
    have decode : ∀ a b : Bool, (a ^^ b) = false → a = b := by decide
    exact decode _ _ (by simpa only [decide_eq_false hneq, Bool.true_and] using hin)
  obtain ⟨w⟩ := hpath
  have hx := constant_on_walk (c := c.val) (fun _ _ h => heq h) w
  have ht := c.property hadj
  change (c.val d.val.1 ^^ c.val d.val.2) = (true && decide (s(d.val.1,d.val.2) = s(d.val.1,d.val.2))) at ht
  simp [hx] at ht

/-- Every cyclic pattern admits a choice of a twisted template side whose
endpoints remain connected after deleting that side. -/
theorem cyclic_side {T : Type*} [LinearOrder T] (F : SimpleGraph T) (h : ¬F.IsAcyclic) :
    ∃ d : Side T, F.Adj d.val.1 d.val.2 ∧
      (F.deleteEdges {s(d.val.1,d.val.2)}).Reachable d.val.1 d.val.2 := by
  classical
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at h
  push Not at h
  obtain ⟨i,j,he,hn⟩ := h
  have hw : (F.deleteEdges {s(i,j)}).Reachable i j := not_not.mp hn
  rcases lt_or_gt_of_ne he.ne with hij | hji
  · exact ⟨⟨(i,j),hij⟩, he, hw⟩
  · refine ⟨⟨(j,i),hji⟩, he.symm, ?_⟩
    simpa only [Sym2.eq_swap (a := j) (b := i)] using hw.symm

end JointForest

namespace JointForest

open SimpleGraph Matrix

attribute [local instance] Classical.propDecidable

/-- Net current leaving a vertex in the unit-resistor graph. -/
noncomputable def current {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) (x : V) : ℚ :=
  ∑ y, if G.Adj x y then p x - p y else 0

noncomputable def pulse {V : Type*} (x a : V) : ℚ := if x = a then 1 else 0

theorem lap_current {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) (x : V) :
    ((G.lapMatrix ℚ) *ᵥ p) x = current G p x := by
  rw [G.lapMatrix_mulVec_apply', G.neighborFinset_eq_filter, Finset.sum_filter]
  rfl

theorem current_sub {V : Type*} [Fintype V] (G : SimpleGraph V) (p q : V → ℚ) (x : V) :
    current G (fun y => p y - q y) x = current G p x - current G q x := by
  rw [← lap_current, ← lap_current, ← lap_current]
  exact congrFun (Matrix.mulVec_sub (G.lapMatrix ℚ) p q) x

theorem current_offset {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) (c : ℚ) (x : V) :
    current G (fun y => p y - c) x = current G p x := by
  simp [current, sub_sub_sub_cancel_right]

theorem current_zero {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) :
    current G (fun _ => 0) x = 0 := by simp [current]

theorem current_sum {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) :
    ∑ x, current G p x = 0 := by
  let z (x y : V) : ℚ := if G.Adj x y then p x - p y else 0
  have h (x y : V) : z y x = -z x y := by
    dsimp [z]
    rw [G.adj_comm y]
    split <;> ring
  have e : (∑ x, ∑ y, z x y) = -(∑ x, ∑ y, z x y) := by
    calc _ = ∑ x, ∑ y, z y x := Finset.sum_comm
         _ = ∑ x, ∑ y, -(z x y) := by apply Finset.sum_congr rfl; intro x _; exact Finset.sum_congr rfl (fun _ _ => h ..)
         _ = _ := by simp
  change (∑ x, ∑ y, z x y) = 0
  linarith

/-- A full set of unit-current responses gives a right inverse to the grounded
Laplacian at `b`. Thus the computed voltage drop is the resistance defined by
the matrix inverse, independent of the arbitrary additive voltage constants. -/
theorem resistance_of_responses {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V)
    (P : V → V → ℚ) (hP : ∀ s x, x ≠ b → current G (P s) x = pulse x s) :
    resistance G a b = P a a - P a b := by
  classical
  by_cases hab : a = b
  · subst a; simp [resistance]
  let A : Matrix {x // x ≠ b} {x // x ≠ b} ℚ := (G.lapMatrix ℚ).submatrix Subtype.val Subtype.val
  let B : Matrix {x // x ≠ b} {x // x ≠ b} ℚ := fun i j => P j.val i.val - P j.val b
  have hAB : A * B = 1 := by
    ext i j
    have h0 := hP j.val i.val i.property
    rw [← current_offset G (P j.val) (P j.val b), ← lap_current] at h0
    change ∑ x : V, (G.lapMatrix ℚ) i.val x * (P j.val x - P j.val b) = _ at h0
    rw [Fintype.sum_eq_add_sum_subtype_ne _ b] at h0
    simp only [sub_self, mul_zero, zero_add] at h0
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [A, B, Matrix.submatrix_apply, pulse, Subtype.ext_iff] using h0
  have h := Matrix.inv_eq_right_inv hAB
  rw [resistance, dite_eq_right hab]
  exact congrArg (fun M : Matrix {x // x ≠ b} {x // x ≠ b} ℚ => M ⟨a,hab⟩ ⟨a,hab⟩) h

/-- Every column may share an arbitrary common return-current distribution.
Subtract its `b`-column to drive a unit of current from `a` to `b`. -/
theorem resistance_of_green {V : Type*} [Fintype V] (G : SimpleGraph V) (P : V → V → ℚ)
    (sink : V → ℚ) (hP : ∀ s x, current G (P s) x = pulse x s - sink x) (a b : V) :
    resistance G a b = (P a a - P b a) - (P a b - P b b) := by
  apply resistance_of_responses G a b (fun s x => P s x - P b x)
  intro s x hx
  rw [current_sub, hP, hP]
  simp [pulse, hx]

/-- Ground the cone apex at zero. -/
def coneGreen {V : Type*} (C : V → V → ℚ) : Option V → Option V → ℚ
  | some a, some b => C a b
  | _, _ => 0

theorem rim_current {V : Type*} [Fintype V] (A : SimpleGraph V) (p : V → ℚ) (x : V) :
    current (cone A) (Option.elim' 0 p) (some x) = p x + current A p x := by
  rw [current, Fintype.sum_option]
  simp only [cone, Option.elim'_none, Option.elim'_some, ite_true, sub_zero]
  rfl

/-- Full cone resistance from any solution to its grounded rim equation.
The apex equation follows by conservation of current. -/
theorem cone_resistance_of_green {V : Type*} [Fintype V] (A : SimpleGraph V) (C : V → V → ℚ)
    (hC : ∀ s x, C s x + current A (C s) x = pulse x s) (a b : Option V) :
    resistance (cone A) a b = (coneGreen C a a - coneGreen C b a) - (coneGreen C a b - coneGreen C b b) := by
  apply resistance_of_green (cone A) (coneGreen C) (fun x => pulse x none)
  intro s x
  cases s with
  | none =>
    change current (cone A) (fun z => coneGreen C none z) x = _
    have h : coneGreen C none = (fun _ => 0) := by funext z; cases z <;> rfl
    rw [h, current_zero, sub_self]
  | some s =>
    have he (y : V) : current (cone A) (coneGreen C (some s)) (some y) = pulse y s := by
      have h : coneGreen C (some s) = Option.elim' 0 (C s) := by funext z; cases z <;> rfl
      rw [h, rim_current, hC]
    cases x with
    | some y => simpa [pulse] using he y
    | none =>
      have h := current_sum (cone A) (coneGreen C (some s))
      rw [Fintype.sum_option] at h
      simp only [he, pulse, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
      simp [pulse]; linarith

end JointForest

namespace JointForest

open SimpleGraph Matrix

attribute [local instance] Classical.propDecidable

/-- The two real (here rational-valued) characters of the deck involution use
the sheet factors +1 and −1. -/
def polarity (b : Bool) : ℚ := if b then -1 else 1

@[simp] theorem polarity_false : polarity false = 1 := rfl
@[simp] theorem polarity_true : polarity true = -1 := rfl

@[simp] theorem polarity_square (b : Bool) : polarity b * polarity b = 1 := by cases b <;> norm_num [polarity]

theorem polarity_xor (a b : Bool) : polarity (a ^^ b) = polarity a * polarity b := by
  cases a <;> cases b <;> norm_num [polarity]

/-- The grounded, signed base operator is the identity plus the signed Laplacian. -/
noncomputable def signedShift {V : Type*} [Fintype V] (B : SimpleGraph V) (s : Signing V) (p : V → ℚ) (x : V) : ℚ :=
  p x + ∑ y, if B.Adj x y then p x - polarity (s.neg x y) * p y else 0

theorem max_principle {V : Type*} [Fintype V] (B : SimpleGraph V) (p : V → ℚ)
    (h : ∀ x, p x + current B p x = 0) (x : V) : p x ≤ 0 := by
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ p ⟨x, Finset.mem_univ x⟩
  have hc : 0 ≤ current B p v := by
    apply Finset.sum_nonneg
    intro y _
    split <;> first | exact sub_nonneg.mpr (hv y (Finset.mem_univ y)) | rfl
  linarith [h v, hv x (Finset.mem_univ x)]

/-- Every finite unsigned base graph has a grounded response. The maximum
principle gives injectivity even when the base is disconnected. -/
theorem unsigned_green_exists {V : Type*} [Fintype V] (B : SimpleGraph V) :
    ∃ P : V → V → ℚ, ∀ s x, P s x + current B (P s) x = pulse x s := by
  classical
  let L : (V → ℚ) →ₗ[ℚ] (V → ℚ) := LinearMap.id + (B.lapMatrix ℚ).mulVecLin
  have hL (p : V → ℚ) (x : V) : L p x = p x + current B p x := by
    change p x + ((B.lapMatrix ℚ) *ᵥ p) x = _
    rw [lap_current]
  have hinj : Function.Injective L := by
    intro p q h
    funext x
    have hsub (p q : V → ℚ) (h : L p = L q) (x : V) : p x - q x ≤ 0 := by
      apply max_principle B (fun y => p y - q y) _ x
      intro y
      rw [current_sub]
      have he := congrFun h y
      rw [hL, hL] at he
      linarith
    linarith [hsub p q h x, hsub q p h.symm x]
  have hsur := LinearMap.surjective_of_injective hinj
  choose P hp using (fun s : V => hsur (fun x => pulse x s))
  exact ⟨P, fun s x => (hL _ _).symm.trans (congrFun (hp s) x)⟩

def sheetGreen {V : Type*} (P Q : V → V → ℚ) (a x : V × Bool) : ℚ :=
  (P a.1 x.1 + polarity a.2 * polarity x.2 * Q a.1 x.1) / 2

theorem current_pair {V : Type*} [Fintype V] (B : SimpleGraph V) (s : Signing V)
    (P Q : V → V → ℚ) (a x : V × Bool) :
    sheetGreen P Q a x + current (signedLift B s) (sheetGreen P Q a) x =
      ((P a.1 x.1 + current B (P a.1) x.1) + polarity a.2 * polarity x.2 * signedShift B s (Q a.1) x.1) / 2 := by
  classical
  obtain ⟨x,xe⟩ := x
  obtain ⟨a,ae⟩ := a
  have row (y : V) : (∑ e : Bool, if (signedLift B s).Adj (x,xe) (y,e)
      then sheetGreen P Q (a,ae) (x,xe) - sheetGreen P Q (a,ae) (y,e) else 0) =
    ((if B.Adj x y then P a x - P a y else 0) + polarity ae * polarity xe *
      (if B.Adj x y then Q a x - polarity (s.neg x y) * Q a y else 0)) / 2 := by
    rw [Fintype.sum_bool]
    cases ae <;> cases xe <;> cases h : s.neg x y <;> by_cases he : B.Adj x y <;>
      simp [signedLift, sheetGreen, h, he] <;> ring
  unfold current signedShift
  rw [Fintype.sum_prod_type]
  simp only [row, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold sheetGreen
  dsimp only
  ring

theorem sheetGreen_solve {V : Type*} [Fintype V] (B : SimpleGraph V) (s : Signing V)
    (P Q : V → V → ℚ) (hP : ∀ a x, P a x + current B (P a) x = pulse x a)
    (hQ : ∀ a x, signedShift B s (Q a) x = pulse x a) (a x : V × Bool) :
    sheetGreen P Q a x + current (signedLift B s) (sheetGreen P Q a) x = pulse x a := by
  rw [current_pair, hP, hQ]
  obtain ⟨a,ae⟩ := a
  obtain ⟨x,xe⟩ := x
  cases ae <;> cases xe <;> by_cases h : x = a <;> simp [pulse, h]

end JointForest

namespace JointForest

open SimpleGraph

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Each unordered pair has exactly one increasing representation. -/
theorem side_endpoints (a b : Side T) : s(a.val.1,a.val.2) = s(b.val.1,b.val.2) ↔ a = b := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have h₁ := a.property
      rw [h.1, h.2] at h₁
      exact (lt_asymm h₁ b.property).elim
  · rintro rfl; rfl

/-- Direct sign on this side (right-terminal path signs are its negatives). -/
def sideSign (tw : Bool) (d e : Side T) : ℚ := polarity (tw && decide (e = d))

theorem right_sign (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inr (e,i,j)) (.inl e.val.2)) = -sideSign tw d e := by
  simp [signing, signBit, sideSign]; cases tw <;> by_cases e = d <;> simp [*, polarity]

theorem direct_sign (tw : Bool) (d e : Side T) :
    polarity ((signing (m := m) (r := r) tw d).neg (.inl e.val.1) (.inl e.val.2)) = sideSign tw d e := by
  simp only [signing, signBit, side_endpoints, sideSign]

def previous (e : Side T) (i : Fin m) (j : Fin r) : Base T m r :=
  if hj : j.val = 0 then .inl e.val.1 else .inr (e,i,⟨j.val-1,by have := j.isLt; omega⟩)

def following (e : Side T) (i : Fin m) (j : Fin r) : Base T m r :=
  if hj : j.val+1 < r then .inr (e,i,⟨j.val+1,hj⟩) else .inl e.val.2

theorem previous_ne_following (e : Side T) (i : Fin m) (j : Fin r) : previous e i j ≠ following e i j := by
  unfold previous following
  split <;> split <;> simp_all [ne_of_lt e.property, Fin.ext_iff]

theorem previous_adj (e : Side T) (i : Fin m) (j : Fin r) :
    (expanded T m r).Adj (.inr (e,i,j)) (previous e i j) := by
  unfold previous
  split <;> rename_i h
  · exact ⟨by simp, Or.inr (Or.inl ⟨rfl,h⟩)⟩
  · refine ⟨by simp [Fin.ext_iff]; omega, Or.inr ⟨rfl,rfl,?_⟩⟩
    change j.val-1+1 = j.val
    omega

theorem following_adj (e : Side T) (i : Fin m) (j : Fin r) :
    (expanded T m r).Adj (.inr (e,i,j)) (following e i j) := by
  unfold following
  split <;> rename_i h
  · exact ⟨by simp [Fin.ext_iff], Or.inl ⟨rfl,rfl,rfl⟩⟩
  · refine ⟨by simp, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    have := j.isLt; omega

theorem inner_neighbors (e : Side T) (i : Fin m) (j : Fin r) {z : Base T m r}
    (h : (expanded T m r).Adj (.inr (e,i,j)) z) : z = previous e i j ∨ z = following e i j := by
  cases z with
  | inl v =>
    rcases h.2 with hs | hs
    · exact False.elim hs
    · rcases hs with ⟨rfl,hj⟩ | ⟨rfl,hj⟩
      · exact Or.inl (by simp [previous,hj])
      · exact Or.inr (by simp [following,hj])
  | inr z =>
    obtain ⟨d,k,l⟩ := z
    rcases h.2 with hs | hs
    · rcases hs with ⟨rfl,rfl,hj⟩
      have hl := l.isLt
      exact Or.inr (by simp [following, hj, hl])
    · rcases hs with ⟨rfl,rfl,hj⟩
      have hp : j.val ≠ 0 := by omega
      exact Or.inl (by simp [previous, hp, Fin.ext_iff]; omega)

theorem previous_sign (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inr (e,i,j)) (previous e i j)) = 1 := by
  unfold previous
  split <;> simp [signing, signBit, ne_of_lt e.property]

theorem following_sign (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inr (e,i,j)) (following e i j)) =
      if j.val+1 < r then 1 else -sideSign tw d e := by
  unfold following
  split <;> rename_i h
  · simp [signing, signBit]
  · simp only [right_sign]

/-- The entire shifted signed row at an interior vertex consists of its two
path neighbors. Only the far terminal edge can carry a negative sign. -/
theorem interior_row [Fintype T] (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r)
    (p : Base T m r → ℚ) : signedShift (expanded T m r) (signing tw d) p (.inr (e,i,j)) =
    3*p (.inr (e,i,j)) - p (previous e i j) -
      (if j.val+1 < r then 1 else -sideSign tw d e) * p (following e i j) := by
  classical
  let x : Base T m r := .inr (e,i,j)
  let a := previous e i j
  let b := following e i j
  let f (v : Base T m r) := p x - polarity ((signing tw d).neg x v) * p v
  have hne : a ≠ b := previous_ne_following e i j
  have hh (v : Base T m r) : (if (expanded T m r).Adj x v then f v else 0) =
      (if v = a then f v else 0) + (if v = b then f v else 0) := by
    by_cases ha : v = a
    · subst v; simp [hne, show (expanded T m r).Adj x a from previous_adj ..]
    by_cases hb : v = b
    · subst v; simp [ha, show (expanded T m r).Adj x b from following_adj ..]
    have hn : ¬ (expanded T m r).Adj x v := fun h => (inner_neighbors e i j h).elim ha hb
    simp [ha,hb,hn]
  change p x + (∑ v, if (expanded T m r).Adj x v then f v else 0) = _
  simp_rw [hh]
  simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq', f, x, a, b, previous_sign, following_sign]
  ring

end JointForest

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Local inverse on a single path with zero boundary values. A source in any
other path (or at a terminal) contributes zero. -/
def localGreen (a : Base T m r) (e : Side T) (i : Fin m) (k : ℕ) : ℚ :=
  match a with
  | .inl _ => 0
  | .inr (d,n,j) => if e = d ∧ i = n then pathGreen (r+1) k (j.val+1) else 0

/-- Linear response along a path between prescribed terminal voltages, with
the sign of the far terminal and the internal point-source response. -/
def lineValue (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (k : ℕ) : ℚ :=
  (ratCont (r+1-k) * z e.val.1 - sideSign tw d e * ratCont k * z e.val.2) / ratCont (r+1) +
    localGreen a e i k

def extension (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) : Base T m r → ℚ
  | .inl x => z x
  | .inr (e,i,j) => lineValue tw d z a e i (j.val+1)

@[simp] theorem localGreen_zero (a : Base T m r) (e : Side T) (i : Fin m) :
    localGreen a e i 0 = 0 := by cases a <;> simp [localGreen]

@[simp] theorem localGreen_end (a : Base T m r) (e : Side T) (i : Fin m) :
    localGreen a e i (r+1) = 0 := by cases a <;> simp [localGreen]

@[simp] theorem lineValue_zero (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i 0 = z e.val.1 := by
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp [lineValue, hn]

@[simp] theorem lineValue_end (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i (r+1) = -sideSign tw d e * z e.val.2 := by
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp [lineValue]
  field_simp

theorem line_previous (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    extension tw d z a (previous e i j) = lineValue tw d z a e i j.val := by
  unfold previous
  split <;> rename_i h
  · rw [h, lineValue_zero]; rfl
  · change lineValue _ _ _ _ _ _ (j.val-1+1) = _
    rw [show j.val-1+1 = j.val by omega]

theorem line_following (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    (if j.val+1 < r then 1 else -sideSign tw d e) * extension tw d z a (following e i j) =
    lineValue tw d z a e i (j.val+2) := by
  by_cases h : j.val+1 < r
  · simp [h, following, extension]
  · have he := j.isLt
    rw [show j.val+2 = r+1 by omega, lineValue_end]
    simp [h, following, extension]

theorem localGreen_current (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    3 * localGreen a e i (j.val+1) - localGreen a e i j.val - localGreen a e i (j.val+2) =
    pulse (.inr (e,i,j)) a := by
  cases a with
  | inl u => simp [localGreen, pulse]
  | inr a =>
    obtain ⟨e',i',k⟩ := a
    by_cases he : e = e'
    · subst e'
      by_cases hi : i = i'
      · subst i'
        have h := pathGreen_current (s := r+1) (i := j.val+1) (j := k.val+1)
          (by omega) (by have := j.isLt; omega) (by omega) (by have := k.isLt; omega)
        simpa [localGreen, pulse, Fin.ext_iff] using h
      · simp [hi, localGreen, pulse]
    · simp [he, localGreen, pulse]

theorem line_current (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) (j : Fin r) :
    3 * lineValue tw d z a e i (j.val+1) - lineValue tw d z a e i j.val - lineValue tw d z a e i (j.val+2) =
    pulse (.inr (e,i,j)) a := by
  have hr := j.isLt
  have h1 := ratCont_rec j.val
  have h2 := ratCont_at (by omega : 0 < r-j.val)
  have l0 : r+1-j.val = r-j.val+1 := by omega
  have l1 : r+1-(j.val+1) = r-j.val := by omega
  have l2 : r+1-(j.val+2) = r-j.val-1 := by omega
  simp only [lineValue, l0,l1,l2, ← h2, h1]
  have h := localGreen_current a e i j
  linear_combination h

theorem extension_inner_eq [Fintype T] (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T)
    (i : Fin m) (j : Fin r) : signedShift (expanded T m r) (signing tw d) (extension tw d z a) (.inr (e,i,j)) =
    pulse (.inr (e,i,j)) a := by
  rw [interior_row, line_previous, line_following]
  exact line_current ..

end JointForest

namespace JointForest

open SimpleGraph

variable {T : Type*} [LinearOrder T] [Fintype T] {m r : ℕ}

instance decideStep : DecidableRel (@step T _ m r) := fun x y => by
  cases x with
  | inl x => cases y <;> unfold step <;> infer_instance
  | inr x => cases y <;> unfold step <;> infer_instance

instance : DecidableRel (expanded T m r).Adj := fun u v => by
  letI : Decidable (step u v) := decideStep u v
  letI : Decidable (step v u) := decideStep v u
  exact inferInstanceAs (Decidable (u ≠ v ∧ (step u v ∨ step v u)))

/-- Summing the incidences of all sides at `u` counts each other terminal once. -/
theorem incident_sum (u : T) (f : T → ℚ) :
    (∑ e : Side T, ((if e.val.1 = u then f e.val.2 else 0) + (if e.val.2 = u then f e.val.1 else 0))) =
    ∑ v, if u ≠ v then f v else 0 := by
  let l (p : T × T) := if p.1 = u then (if u < p.2 then f p.2 else 0) else 0
  let r (p : T × T) := if p.2 = u then (if p.1 < u then f p.1 else 0) else 0
  have h (p : Side T) : (if p.val.1 = u then f p.val.2 else 0) + (if p.val.2 = u then f p.val.1 else 0) = l p + r p := by
    have hp := p.property
    dsimp [l,r]
    split_ifs <;> simp_all
  have hz : (∑ p : {p : T × T // ¬ p.1 < p.2}, (l p + r p)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hp := p.property
    dsimp [l,r]; split_ifs <;> simp_all
  have ht := Fintype.sum_subtype_add_sum_subtype (fun p : T × T => p.1 < p.2) (fun p => l p + r p)
  rw [hz, add_zero] at ht
  simp_rw [h]
  rw [ht, Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm (f := fun x y => l (x,y))]
  simp only [l,r, Fintype.sum_ite_eq']
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rcases lt_trichotomy u v with h | rfl | h <;> simp [*, ne_of_gt, ne_of_lt, not_lt_of_gt]

def firstPos (hr : 0 < r) : Fin r := ⟨0,hr⟩
def lastPos (hr : 0 < r) : Fin r := ⟨r-1,by omega⟩

omit [Fintype T] in
theorem terminal_adj (u v : T) : (expanded T m r).Adj (.inl u) (.inl v) ↔ u ≠ v := by
  change (_ ∧ (u < v ∨ v < u)) ↔ _
  exact ⟨fun h e => h.1 (congrArg Sum.inl e), fun h => ⟨fun h' => h (Sum.inl.inj h'), lt_or_gt_of_ne h⟩⟩

omit [Fintype T] in
theorem terminal_inner_adj (u : T) (e : Side T) (i : Fin m) (j : Fin r) (hr : 0 < r) :
    (expanded T m r).Adj (.inl u) (.inr (e,i,j)) ↔
      (e.val.1 = u ∧ j = firstPos hr) ∨ (e.val.2 = u ∧ j = lastPos hr) := by
  have h : j.val+1 = r ↔ j.val = r-1 := by omega
  simp [expanded, step, firstPos, lastPos, Fin.ext_iff, eq_comm (a := u), h]

omit [Fintype T] in
/-- Sum over one path bundle at its two endpoints. The distinguished positions
are present whenever the number of internal vertices is positive. -/
theorem incident_path_sum (u : T) (e : Side T) (hr : 0 < r) (f : Base T m r → ℚ) :
    (∑ i : Fin m, ∑ j : Fin r, if (expanded T m r).Adj (.inl u) (.inr (e,i,j)) then f (.inr (e,i,j)) else 0) =
    (if e.val.1 = u then ∑ i, f (.inr (e,i,firstPos hr)) else 0) +
    (if e.val.2 = u then ∑ i, f (.inr (e,i,lastPos hr)) else 0) := by
  have hne := ne_of_lt e.property
  by_cases hl : e.val.1 = u <;> by_cases hr' : e.val.2 = u <;>
    first | exact (hne (hl.trans hr'.symm)).elim | simp [terminal_inner_adj _ _ _ _ hr, hl, hr']

/-- Exact neighbor enumeration at a terminal, including the direct edge and
both kinds of incident long-path bundles. -/
theorem terminal_neighbor_sum (u : T) (hr : 0 < r) (f : Base T m r → ℚ) :
    (∑ z, if (expanded T m r).Adj (.inl u) z then f z else 0) =
    ∑ e : Side T,
      ((if e.val.1 = u then f (.inl e.val.2) + ∑ i, f (.inr (e,i,firstPos hr)) else 0) +
      (if e.val.2 = u then f (.inl e.val.1) + ∑ i, f (.inr (e,i,lastPos hr)) else 0)) := by
  rw [Fintype.sum_sum_type]
  simp_rw [terminal_adj, Fintype.sum_prod_type]
  rw [← incident_sum u (fun v => f (.inl v))]
  simp_rw [incident_path_sum u _ hr f]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

end JointForest

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Terminal self-conductance left after eliminating one whole side. -/
def gain (r : ℕ) : ℚ := 1 + ratCont (r+1) - ratCont r

theorem gain_pos (r : ℕ) : 0 < gain r := by
  have h : ratCont r < ratCont (r+1) := by exact_mod_cast continuant_increasing r
  unfold gain; linarith

def leftRatio (j : Fin r) : ℚ := ratCont (r-j.val) / ratCont (r+1)
def rightRatio (j : Fin r) : ℚ := ratCont (j.val+1) / ratCont (r+1)

theorem first_green (j : Fin r) : pathGreen (r+1) 1 (j.val+1) = leftRatio j := by
  rw [pathGreen_left (by omega : 1 ≤ j.val+1)]
  simp [leftRatio]

theorem last_green (j : Fin r) : pathGreen (r+1) r (j.val+1) = rightRatio j := by
  rw [pathGreen_right (by have := j.isLt; omega : j.val+1 ≤ r)]
  simp [rightRatio]

theorem line_first (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i 1 = (ratCont r * z e.val.1 - sideSign tw d e * z e.val.2) / ratCont (r+1) + localGreen a e i 1 := by simp [lineValue]

theorem line_last (tw : Bool) (d : Side T) (z : T → ℚ) (a : Base T m r) (e : Side T) (i : Fin m) :
    lineValue tw d z a e i r = (z e.val.1 - sideSign tw d e * ratCont r * z e.val.2) / ratCont (r+1) + localGreen a e i r := by simp [lineValue]

theorem sideSign_square (tw : Bool) (d e : Side T) : sideSign tw d e * sideSign tw d e = 1 := polarity_square _

/-- The off-diagonal response of the parallel paths is exactly the negative of
the response of the direct signed edge at both ends. -/
theorem left_bundle (hm : m = continuant (r+1)) (tw : Bool) (d e : Side T) (z : T → ℚ) (a : Base T m r) :
    z e.val.1 - sideSign tw d e * z e.val.2 + (∑ i : Fin m, (z e.val.1 - lineValue tw d z a e i 1)) =
    gain r * z e.val.1 - ∑ i : Fin m, localGreen a e i 1 := by
  have hm' : (m : ℚ) = ratCont (r+1) := congrArg Nat.cast hm
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp only [line_first, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm', gain]
  field_simp
  ring

theorem right_bundle (hm : m = continuant (r+1)) (tw : Bool) (d e : Side T) (z : T → ℚ) (a : Base T m r) :
    z e.val.2 - sideSign tw d e * z e.val.1 + (∑ i : Fin m, (z e.val.2 + sideSign tw d e * lineValue tw d z a e i r)) =
    gain r * z e.val.2 + sideSign tw d e * ∑ i : Fin m, localGreen a e i r := by
  have hm' : (m : ℚ) = ratCont (r+1) := congrArg Nat.cast hm
  have hn := (ratCont_pos (Nat.zero_lt_succ r)).ne'
  simp only [line_last, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm', gain]
  field_simp
  cases tw <;> by_cases he : e = d <;> simp [sideSign, polarity, he] <;> ring

/-- Coefficient of terminal `u` in the conditional mean at source `a`. -/
def boundaryWeight (tw : Bool) (d : Side T) (a : Base T m r) (u : T) : ℚ :=
  match a with
  | .inl v => if u = v then 1 else 0
  | .inr (e,_,j) => (if e.val.1 = u then leftRatio j else 0) -
                      (if e.val.2 = u then sideSign tw d e * rightRatio j else 0)

noncomputable def leftLeak (a : Base T m r) (e : Side T) : ℚ := ∑ i : Fin m, localGreen a e i 1
noncomputable def rightLeak (a : Base T m r) (e : Side T) : ℚ := ∑ i : Fin m, localGreen a e i r

theorem leftLeak_inner (e e' : Side T) (i : Fin m) (j : Fin r) :
    leftLeak (.inr (e',i,j)) e = if e = e' then leftRatio j else 0 := by
  by_cases h : e = e' <;> simp [leftLeak, localGreen,h, first_green]

theorem rightLeak_inner (e e' : Side T) (i : Fin m) (j : Fin r) :
    rightLeak (.inr (e',i,j)) e = if e = e' then rightRatio j else 0 := by
  by_cases h : e = e' <;> simp [rightLeak, localGreen,h, last_green]

theorem sum_leaks [Fintype T] (tw : Bool) (d : Side T) (a : Base T m r) (u : T) :
    (∑ e : Side T, ((if e.val.1 = u then leftLeak a e else 0) -
      (if e.val.2 = u then sideSign tw d e * rightLeak a e else 0))) = boundaryWeight tw d a u - pulse (.inl u) a := by
  classical
  cases a with
  | inl v => simp [leftLeak, rightLeak, localGreen, boundaryWeight, pulse]
  | inr a =>
    obtain ⟨e',i',j'⟩ := a
    have h (e : Side T) : (if e.val.1 = u then leftLeak (.inr (e',i',j')) e else 0) -
        (if e.val.2 = u then sideSign tw d e * rightLeak (.inr (e',i',j')) e else 0) =
        if e = e' then boundaryWeight tw d (.inr (e',i',j')) u else 0 := by
      by_cases he : e = e' <;> simp [he, leftLeak_inner, rightLeak_inner, boundaryWeight]
    simp_rw [h]
    simp [pulse]

end JointForest

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

theorem left_contact (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inl e.val.1) (.inr (e,i,j))) = 1 := by
  simp [signing, signBit, ne_of_lt e.property]

theorem right_contact (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inl e.val.2) (.inr (e,i,j))) = -sideSign tw d e := by
  rw [(signing tw d).symm]; exact right_sign ..

theorem direct_reverse (tw : Bool) (d e : Side T) :
    polarity ((signing (m := m) (r := r) tw d).neg (.inl e.val.2) (.inl e.val.1)) = sideSign tw d e := by
  rw [(signing tw d).symm]; exact direct_sign ..

/-- The diagonal of the terminal Schur complement is positive and independent
of all signs. Each other terminal contributes the conductance of one side. -/
noncomputable def terminalD [Fintype T] (r : ℕ) (u : T) : ℚ := 1 + ∑ v : T, if u ≠ v then gain r else 0

theorem terminalD_pos [Fintype T] (r : ℕ) (u : T) : 0 < terminalD r u := by
  have h : 0 ≤ ∑ v : T, if u ≠ v then gain r else 0 := by
    apply Finset.sum_nonneg; intro x _; split <;> first | exact (gain_pos r).le | rfl
  unfold terminalD; linarith

/-- Compute the terminal row of the shifted signed Laplacian after extending
arbitrary boundary data and a single interior or terminal source. -/
theorem terminal_current [Fintype T] (hr : 0 < r) (hm : m = continuant (r+1)) (tw : Bool) (d : Side T)
    (z : T → ℚ) (a : Base T m r) (u : T) :
    signedShift (expanded T m r) (signing tw d) (extension tw d z a) (.inl u) =
    terminalD r u * z u - (boundaryWeight tw d a u - pulse (.inl u) a) := by
  classical
  let p := extension tw d z a
  let f (v : Base T m r) := z u - polarity ((signing tw d).neg (.inl u) v) * p v
  have hL (e : Side T) (h : e.val.1 = u) : f (.inl e.val.2) + (∑ i, f (.inr (e,i,firstPos hr))) =
      gain r * z u - leftLeak a e := by
    subst u
    simp only [f, p, extension, direct_sign, left_contact, one_mul, firstPos, Nat.zero_add, leftLeak]
    exact left_bundle hm tw d e z a
  have hR (e : Side T) (h : e.val.2 = u) : f (.inl e.val.1) + (∑ i, f (.inr (e,i,lastPos hr))) =
      gain r * z u + sideSign tw d e * rightLeak a e := by
    subst u
    simp only [f, p, extension, direct_reverse, right_contact, neg_mul, sub_neg_eq_add, lastPos,
      show r-1+1 = r by omega, rightLeak]
    exact right_bundle hm tw d e z a
  have terms (e : Side T) : (if e.val.1 = u then f (.inl e.val.2) + ∑ i, f (.inr (e,i,firstPos hr)) else 0) +
      (if e.val.2 = u then f (.inl e.val.1) + ∑ i, f (.inr (e,i,lastPos hr)) else 0) =
      ((if e.val.1 = u then gain r else 0) + (if e.val.2 = u then gain r else 0)) * z u -
      ((if e.val.1 = u then leftLeak a e else 0) - (if e.val.2 = u then sideSign tw d e * rightLeak a e else 0)) := by
    split_ifs with hl ht ht
    · exact (ne_of_lt e.property (hl.trans ht.symm)).elim
    · rw [hL e hl]; ring
    · rw [hR e ht]; ring
    · ring
  have row : signedShift (expanded T m r) (signing tw d) (extension tw d z a) (.inl u) =
      z u + (∑ v, if (expanded T m r).Adj (.inl u) v then f v else 0) := by
    unfold signedShift
    apply congrArg (z u + ·)
    apply Finset.sum_congr (Finset.ext (fun _ => by simp))
    intro v _
    by_cases hv : (expanded T m r).Adj (.inl u) v <;> simp [hv, f, p, extension]
  rw [row]
  rw [terminal_neighbor_sum u hr f]
  simp_rw [terms]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, incident_sum u (fun _ => gain r), sum_leaks]
  unfold terminalD
  ring

noncomputable def terminalVoltage [Fintype T] (tw : Bool) (d : Side T) (a : Base T m r) (u : T) : ℚ :=
  boundaryWeight tw d a u / terminalD r u

/-- The signed inverse after eliminating long interiors. -/
noncomputable def signedGreen [Fintype T] (tw : Bool) (d : Side T) (a : Base T m r) : Base T m r → ℚ :=
  extension tw d (terminalVoltage tw d a) a

theorem signedGreen_solve [Fintype T] (hr : 0 < r) (hm : m = continuant (r+1)) (tw : Bool) (d : Side T)
    (a x : Base T m r) : signedShift (expanded T m r) (signing tw d) (signedGreen tw d a) x = pulse x a := by
  cases x with
  | inl u =>
    rw [signedGreen, terminal_current hr hm]
    unfold terminalVoltage
    field_simp [(terminalD_pos r u).ne']
    ring
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    exact extension_inner_eq tw d _ a e i j

end JointForest

namespace JointForest

open SimpleGraph

def emptySide {T : Type*} (F : SimpleGraph T) : Independent F := ⟨∅, by simp⟩

def outsideEmpty {T : Type*} (F : SimpleGraph T) : outside F (emptySide F) ≃g F where
  toFun := Subtype.val
  invFun t := ⟨t, Set.notMem_empty _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem empty_count {T V : Type*} (F : SimpleGraph T) (G : SimpleGraph V) :
    homCount (outside F (emptySide F)) G = homCount F G :=
  Nat.card_congr ((outsideEmpty F).homCongr (SimpleGraph.Iso.refl : G ≃g G))

/-- For every cyclic pattern a suitable twist strictly decreases its actual
homomorphism count into the cone, for every number of parallel long paths and
more interior positions than vertices of the pattern. -/
theorem cone_twist_loss {T : Type*} [LinearOrder T] [Fintype T] (F : SimpleGraph T)
    (hF : ¬F.IsAcyclic) (m r : ℕ) (hr : Fintype.card T < r) :
    ∃ d : Side T, homCount F (cone (signedLift (expanded T m r) (signing true d))) <
      homCount F (cone (signedLift (expanded T m r) (signing false d))) := by
  classical
  obtain ⟨d, hd, hw⟩ := cyclic_side F hF
  refine ⟨d, ?_⟩
  rw [cone_hom_count, cone_hom_count]
  apply Finset.sum_lt_sum
  · intro s _
    apply lift_hom_le
    apply positive_lift
    exact lt_of_le_of_lt (Fintype.card_subtype_le _) hr
  · refine ⟨emptySide F, by simp, ?_⟩
    rw [empty_count, empty_count]
    exact lift_hom_lt F _ _ _ (positive_lift hr d) (templateHom F m r) (twisted_no_lift F m r d hd hw)

theorem cone_connected {V : Type*} (G : SimpleGraph V) : (cone G).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, fun x => ?_⟩
  cases x with
  | none => exact .refl _
  | some u => exact SimpleGraph.Adj.reachable (show (cone G).Adj none (some u) from trivial)

theorem cone_dist_le_two {V : Type*} (G : SimpleGraph V) (x y : Option V) : (cone G).dist x y ≤ 2 := by
  cases x with
  | none =>
    cases y with
    | none => simp
    | some v => simp [(cone G).dist_eq_one_iff_adj.mpr (show (cone G).Adj none (some v) from trivial)]
  | some u =>
    cases y with
    | none => simp [(cone G).dist_eq_one_iff_adj.mpr (show (cone G).Adj (some u) none from trivial)]
    | some v =>
      let w : (cone G).Walk (some u) (some v) := .cons (v := none) trivial (.cons (v := some v) trivial .nil)
      exact SimpleGraph.dist_le w

/-- Opposite sheets of the same base vertex are precisely two steps apart. -/
theorem opposite_sheets_dist {T : Type*} (B : SimpleGraph T) (s : Signing T) (u : T) :
    (cone (signedLift B s)).dist (some (u,false)) (some (u,true)) = 2 := by
  let G := cone (signedLift B s)
  let x : Option (T × Bool) := some (u,false)
  let y : Option (T × Bool) := some (u,true)
  have hle := cone_dist_le_two (signedLift B s) x y
  have hz : G.dist x y ≠ 0 := fun h => by have := (cone_connected _).dist_eq_zero_iff.mp h; simp [x, y] at this
  have ho : G.dist x y ≠ 1 := fun h => B.loopless.irrefl u (G.dist_eq_one_iff_adj.mp h).1
  change G.dist x y = 2
  change G.dist x y ≤ 2 at hle
  omega

end JointForest

namespace JointForest

open SimpleGraph

/-- A pairwise sheet exchange can vary with the ordered pair, while retaining
both resistance and adjacency on that same exchange. -/
structure Alignment {V : Type*} (B : SimpleGraph V) (s t : Signing V) (S T : V → V → ℚ) where
  flip : V → V → Bool
  diag : ∀ u, flip u u = false
  symm : ∀ u v, flip u v = flip v u
  edge : ∀ u v, B.Adj u v → t.neg u v = (s.neg u v ^^ flip u v)
  green : ∀ u v, T u v = polarity (flip u v) * S u v

/-- The new apex forces every proper nonedge to have distance two. -/
theorem cone_distance {V : Type*} (G : SimpleGraph V) (x y : Option V) : (cone G).dist x y =
    (by classical exact if x = y then 0 else if (cone G).Adj x y then 1 else 2) := by
  classical
  split_ifs with he ha
  · exact (cone_connected G).dist_eq_zero_iff.mpr he
  · exact (cone G).dist_eq_one_iff_adj.mpr ha
  · have hz := (cone_connected G).dist_eq_zero_iff.not.mpr he
    have ho := (cone G).dist_eq_one_iff_adj.not.mpr ha
    have hle := cone_dist_le_two G x y
    omega

theorem sheetGreen_aligned {V : Type*} {B : SimpleGraph V} {s t : Signing V} {S T : V → V → ℚ}
    (al : Alignment B s t S T) (P : V → V → ℚ) (u v : V) (a b c d : Bool)
    (h : (a ^^ b) = ((c ^^ d) ^^ al.flip u v)) :
    sheetGreen P S (u,a) (v,b) = sheetGreen P T (u,c) (v,d) := by
  have hq := congrArg polarity h
  simp only [polarity_xor] at hq
  simp only [sheetGreen, al.green u v, hq]
  ring

def forgetSheet {V : Type*} : Option (V × Bool) → Option V := Option.map Prod.fst

/-- Match the target sheets in each fiber independently. -/
def flipSheets {V : Type*} (k : V → Bool) : Option (V × Bool) ≃ Option (V × Bool) :=
  let bit (v : V) : Bool ≃ Bool :=
    { toFun := fun b => b ^^ k v
      invFun := fun b => b ^^ k v
      left_inv := fun b => by cases b <;> cases k v <;> rfl
      right_inv := fun b => by cases b <;> cases k v <;> rfl }
  (Equiv.prodShear (Equiv.refl V) bit).optionCongr

@[simp] theorem flipSheets_none {V : Type*} (k : V → Bool) : flipSheets k none = none := rfl

@[simp] theorem flipSheets_some {V : Type*} (k : V → Bool) (u : V) (e : Bool) :
    flipSheets k (some (u,e)) = some (u,e ^^ k u) := rfl

theorem flipSheets_forget {V : Type*} (k : V → Bool) (x : Option (V × Bool)) :
    forgetSheet (flipSheets k x) = forgetSheet x := by cases x <;> rfl

theorem fiber_equivalent {V : Type*} [Fintype V] (a b : Option (V × Bool) → Option (V × Bool) → ℕ × ℚ)
    (rows : ∀ x x', forgetSheet x = forgetSheet x' → ∃ k : V → Bool,
      ∀ y, a x y = b x' (flipSheets k y)) : Equivalent a b := by
  have hc (n : ℕ) : ∀ x x', forgetSheet x = forgetSheet x' → color a n x = color b n x' := by
    induction n with
    | zero => exact fun _ _ _ => rfl
    | succ n ih =>
      intro x x' hx
      obtain ⟨k, hk⟩ := rows x x' hx
      let e := flipSheets k
      have h (y : Option (V × Bool)) : ((a x y).1, (a x y).2, color a n y) =
        ((b x' (e y)).1, (b x' (e y)).2, color b n (e y)) := by
        rw [hk, ih y (e y) (flipSheets_forget k y).symm]
      change Finset.univ.val.map (fun y => ((a x y).1, (a x y).2, color a n y)) = _
      simp_rw [h]
      have he := congrArg (Multiset.map (fun y => ((b x' y).1, (b x' y).2, color b n y))) (Multiset.map_univ_val_equiv e)
      simpa only [Multiset.map_map, Function.comp_def, color] using he
  intro n
  simp_rw [show color a n = color b n from funext (fun x => hc n x x rfl)]

/-- An alignment of the signed Green entries lifts to equality of all rounds
of the actual joint shortest-path and unit-resistance refinement on the cones. -/
theorem cones_equivalent {V : Type*} [Fintype V] (B : SimpleGraph V) (s t : Signing V)
    (S T : V → V → ℚ) (hS : ∀ a x, signedShift B s (S a) x = pulse x a)
    (hT : ∀ a x, signedShift B t (T a) x = pulse x a) (al : Alignment B s t S T) :
    Equivalent (jointLabels (cone (signedLift B s))) (jointLabels (cone (signedLift B t))) := by
  classical
  obtain ⟨P,hP⟩ := unsigned_green_exists B
  let gs := sheetGreen P S
  let gt := sheetGreen P T
  have rs := cone_resistance_of_green (signedLift B s) gs (sheetGreen_solve B s P S hP hS)
  have rt := cone_resistance_of_green (signedLift B t) gt (sheetGreen_solve B t P T hP hT)
  have diag (u : V) (a b : Bool) : gs (u,a) (u,a) = gt (u,b) (u,b) :=
    sheetGreen_aligned al P u u a a b b (by simp [al.diag])
  apply fiber_equivalent
  intro x x' hx
  cases x with
  | none =>
    cases x' with
    | some v => cases hx
    | none =>
      refine ⟨fun _ => false, ?_⟩
      intro y
      cases y with
      | none => simp [jointLabels, resistance]
      | some z =>
        obtain ⟨v,e⟩ := z
        simp only [flipSheets_some, Bool.xor_false]
        apply Prod.ext
        · change (cone (signedLift B s)).dist none (some (v,e)) = (cone (signedLift B t)).dist none (some (v,e))
          rw [cone_distance, cone_distance]; simp [cone]
        · change resistance _ none (some (v,e)) = resistance _ none (some (v,e))
          rw [rs, rt]; simpa only [coneGreen, sub_zero, zero_sub, sub_neg_eq_add, zero_add, zero_sub_zero] using diag _ _ _
  | some u =>
    obtain ⟨u, a⟩ := u
    cases x' with
    | none => cases hx
    | some v =>
      obtain ⟨u', b⟩ := v
      have hu : u = u' := Option.some.inj hx
      subst u'
      let k (v : V) := ((a ^^ b) ^^ al.flip u v)
      refine ⟨k, ?_⟩
      intro y
      cases y with
      | none =>
        apply Prod.ext
        · rw [show flipSheets k none = none from rfl]
          change (cone (signedLift B s)).dist _ none = (cone (signedLift B t)).dist _ none
          rw [cone_distance, cone_distance]; simp [cone]
        · change resistance _ (some (u,a)) none = resistance _ (some (u,b)) none
          rw [rs, rt]; simpa only [coneGreen, sub_zero, sub_self] using diag u a b
      | some z =>
        obtain ⟨v,c⟩ := z
        let d := c ^^ k v
        have hab : (a ^^ c) = ((b ^^ d) ^^ al.flip u v) := by
          dsimp [d,k]; cases a <;> cases b <;> cases c <;> cases al.flip u v <;> rfl
        have hba : (c ^^ a) = ((d ^^ b) ^^ al.flip v u) := by
          simpa only [Bool.xor_comm c a, Bool.xor_comm d b, al.symm v u] using hab
        have heq : (some (u,a)) = some (v,c) ↔ (some (u,b)) = some (v,d) := by
          by_cases hu : u = v
          · subst v
            simp only [Option.some.injEq, Prod.mk.injEq, true_and] at *
            dsimp [d,k]; rw [al.diag]; cases a <;> cases b <;> cases c <;> decide
          · simp [hu]
        have hed : (cone (signedLift B s)).Adj (some (u,a)) (some (v,c)) ↔
            (cone (signedLift B t)).Adj (some (u,b)) (some (v,d)) := by
          change (B.Adj u v ∧ (a ^^ c) = _) ↔ (B.Adj u v ∧ (b ^^ d) = _)
          by_cases he : B.Adj u v
          · rw [al.edge u v he, hab]
            simp only [he, true_and]
            cases b <;> cases d <;> cases s.neg u v <;> cases al.flip u v <;> decide
          · simp [he]
        apply Prod.ext
        · change (cone (signedLift B s)).dist (some (u,a)) (some (v,c)) =
            (cone (signedLift B t)).dist (some (u,b)) (some (v,d))
          rw [cone_distance, cone_distance]
          split_ifs <;> simp_all
        · change resistance _ (some (u,a)) (some (v,c)) = resistance _ (some (u,b)) (some (v,d))
          rw [rs, rt]
          simp only [coneGreen]
          have huv : gs (u,a) (v,c) = gt (u,b) (v,d) := sheetGreen_aligned al P u v a c b d hab
          have hvu : gs (v,c) (u,a) = gt (v,d) (u,b) := sheetGreen_aligned al P v u c a d b hba
          rw [diag u a b, diag v c d, huv, hvu]

end JointForest

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Terminal support of a row of the interpolation matrix. -/
def touches (x : Base T m r) (u : T) : Prop :=
  match x with
  | .inl v => u = v
  | .inr (e,_,_) => u = e.val.1 ∨ u = e.val.2

instance (x : Base T m r) (u : T) : Decidable (touches x u) := by
  cases x <;> unfold touches <;> infer_instance

def onSide (d : Side T) : Base T m r → Bool
  | .inl _ => false
  | .inr (e,_,_) => decide (e = d)

def sheetFlip (d : Side T) (x y : Base T m r) : Bool :=
  match x,y with
  | .inl u, .inl v => decide (s(u,v) = s(d.val.1,d.val.2))
  | _,_ => (onSide d x ^^ onSide d y) && decide (touches x d.val.2 ∧ touches y d.val.2)

def terminalFlip (d : Side T) (x : Base T m r) (u : T) : Bool := onSide d x && decide (u = d.val.2)

theorem sheetFlip_diag (d : Side T) (x : Base T m r) : sheetFlip d x x = false := by
  cases x with
  | inl u => simp [sheetFlip]; grind [ne_of_lt d.property]
  | inr x => simp [sheetFlip]

theorem sheetFlip_comm (d : Side T) (x y : Base T m r) : sheetFlip d x y = sheetFlip d y x := by
  cases x <;> cases y <;> simp only [sheetFlip, Bool.xor_comm, and_comm, Sym2.eq_swap]

/-- An object touching both endpoints of the distinguished side must be an
interior on that side: distinct sides share at most one terminal. -/
theorem onSide_of_both (d : Side T) (x : Base T m r) (hl : touches x d.val.1) (hr : touches x d.val.2) :
    onSide d x = true := by
  cases x with
  | inl v => exact (ne_of_lt d.property (hl.trans hr.symm)).elim
  | inr p =>
    obtain ⟨e,i,j⟩ := p
    have h : e = d := by
      apply (side_endpoints e d).mp
      apply Sym2.eq_iff.mpr
      rcases hl with hl | hl <;> rcases hr with hr | hr <;> grind [ne_of_lt d.property]
    simp [onSide, h]

theorem touch_of_onSide (d : Side T) (x : Base T m r) (hx : onSide d x = true) (u : T) :
    touches x u ↔ u = d.val.1 ∨ u = d.val.2 := by
  cases x with
  | inl v => cases hx
  | inr p =>
    obtain ⟨e,i,j⟩ := p
    have he : e = d := by simpa [onSide] using hx
    cases he; rfl

theorem common_terminal_flip (d : Side T) (x y : Base T m r) (u : T)
    (hx : touches x u) (hy : touches y u) :
    (terminalFlip d x u ^^ terminalFlip d y u) = sheetFlip d x y := by
  have local_rule (x y : Base T m r) (hx : touches x u) (hy : touches y u) :
      (terminalFlip d x u ^^ terminalFlip d y u) =
      ((onSide d x ^^ onSide d y) && decide (touches x d.val.2 ∧ touches y d.val.2)) := by
    by_cases hu : u = d.val.2
    · subst u; simp [terminalFlip, hx,hy]
    · have imp (x y : Base T m r) (hx : touches x u) (hy : touches y u) (hs : onSide d x = true)
          (hr : touches y d.val.2) : onSide d y = true := by
        have hl := ((touch_of_onSide d x hs u).mp hx).resolve_right hu
        exact onSide_of_both d y (hl ▸ hy) hr
      by_cases hc : touches x d.val.2 ∧ touches y d.val.2
      · have hxy : onSide d x = onSide d y := by
          cases h1 : onSide d x <;> cases h2 : onSide d y <;>
            first | rfl | exact (by have := imp x y hx hy h1 hc.2; simp_all) |
              exact (by have := imp y x hy hx h2 hc.1; simp_all)
        simp [terminalFlip, hu, hxy]
      · simp [terminalFlip, hu, hc]
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      have h : v = w := (show u = v from hx).symm.trans hy
      rw [← h, sheetFlip_diag]; simp
    | inr y => exact local_rule _ _ hx hy
  | inr x => cases y <;> exact local_rule _ _ hx hy

theorem weight_off (tw : Bool) (d : Side T) (x : Base T m r) (u : T) (h : ¬touches x u) :
    boundaryWeight tw d x u = 0 := by
  cases x with
  | inl v => simpa [boundaryWeight, touches] using h
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    have hl : e.val.1 ≠ u := fun h' => h (Or.inl h'.symm)
    have hr : e.val.2 ≠ u := fun h' => h (Or.inr h'.symm)
    simp [boundaryWeight, hl,hr]

theorem weight_flip (d : Side T) (x : Base T m r) (u : T) :
    boundaryWeight true d x u = polarity (terminalFlip d x u) * boundaryWeight false d x u := by
  cases x with
  | inl v => simp [boundaryWeight, terminalFlip, onSide]
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    by_cases he : e = d
    · subst e
      by_cases hu : u = d.val.2
      · subst u; simp [boundaryWeight, terminalFlip, onSide, sideSign, ne_of_lt d.property]
      · simp [boundaryWeight, terminalFlip, onSide, hu, Ne.symm hu]
    · simp [boundaryWeight, terminalFlip, onSide, sideSign, he]

/-- The same exchange aligns the signed covariance and the lift adjacency at
an incident pair, including the direct distinguished terminal edge. -/
theorem edge_flip (d : Side T) (x y : Base T m r) (h : (expanded T m r).Adj x y) :
    (signing true d).neg x y = ((signing false d).neg x y ^^ sheetFlip d x y) := by
  have ti (u : T) (e : Side T) (i : Fin m) (j : Fin r) :
      (signing true d).neg (.inl u) (.inr (e,i,j)) =
      ((signing false d).neg (.inl u) (.inr (e,i,j)) ^^ sheetFlip d (.inl u) (.inr (e,i,j))) := by
    by_cases he : e = d
    · subst e; by_cases hu : u = d.val.2 <;> simp [signing, signBit, sheetFlip, onSide, touches, hu, eq_comm]
    · simp [signing, signBit, sheetFlip, onSide, touches, he]
  cases x with
  | inl u =>
    cases y with
    | inl v => simp [signing, signBit, sheetFlip]
    | inr p => obtain ⟨e,i,j⟩ := p; exact ti ..
  | inr p =>
    obtain ⟨e,i,j⟩ := p
    cases y with
    | inl v =>
      rw [(signing true d).symm, (signing false d).symm, sheetFlip_comm]; exact ti ..
    | inr p =>
      obtain ⟨e',i',j'⟩ := p
      have he : e = e' := h.2.elim (fun ht => ht.1) (fun ht => ht.1.symm)
      subst e'
      simp [signing, signBit, sheetFlip, onSide]

end JointForest

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- The part of the covariance conditional on all terminal values. It vanishes
unless both arguments are in the same long path. -/
def localPart (a : Base T m r) : Base T m r → ℚ
  | .inl _ => 0
  | .inr (e,i,j) => localGreen a e i (j.val+1)

theorem green_expansion [Fintype T] (tw : Bool) (d : Side T) (a x : Base T m r) :
    signedGreen tw d a x = localPart a x + ∑ u : T,
      boundaryWeight tw d a u * boundaryWeight tw d x u / terminalD r u := by
  let w := boundaryWeight tw d a
  cases x with
  | inl v =>
    have h (u : T) : w u * boundaryWeight tw d (.inl v : Base T m r) u / terminalD r u =
        if u = v then w u / terminalD r u else 0 := by
      by_cases hu : u = v <;> simp [boundaryWeight,hu]
    change w v / terminalD r v = 0 + ∑ u, w u * boundaryWeight tw d (.inl v : Base T m r) u / terminalD r u
    simp_rw [h]
    simp
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    have h (u : T) : w u * boundaryWeight tw d (.inr (e,i,j)) u / terminalD r u =
        (if u = e.val.1 then w u * leftRatio j / terminalD r u else 0) -
        (if u = e.val.2 then w u * (sideSign tw d e * rightRatio j) / terminalD r u else 0) := by
      unfold boundaryWeight
      simp only [eq_comm (a := u) (b := e.val.1), eq_comm (a := u) (b := e.val.2)]
      by_cases hl : e.val.1 = u <;> by_cases hr : e.val.2 = u <;> simp_all <;> ring
    change lineValue tw d (terminalVoltage tw d a) a e i (j.val+1) =
      localGreen a e i (j.val+1) + ∑ u, w u * boundaryWeight tw d (.inr (e,i,j)) u / terminalD r u
    simp_rw [h]
    simp only [Finset.sum_sub_distrib, Fintype.sum_ite_eq', lineValue, terminalVoltage, leftRatio, rightRatio,
      Nat.add_sub_add_right, w]
    ring

theorem localPart_flip (d : Side T) (a x : Base T m r) :
    localPart a x = polarity (sheetFlip d a x) * localPart a x := by
  cases x with
  | inl x => simp [localPart]
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    cases a with
    | inl y => simp [localPart,localGreen]
    | inr y =>
      obtain ⟨e',i',j'⟩ := y
      by_cases h : e = e' <;> simp [localPart, localGreen, h, sheetFlip, onSide]

theorem weight_product_flip (d : Side T) (a x : Base T m r) (u : T) :
    boundaryWeight true d a u * boundaryWeight true d x u = polarity (sheetFlip d a x) *
      (boundaryWeight false d a u * boundaryWeight false d x u) := by
  by_cases ha : touches a u
  · by_cases hx : touches x u
    · rw [weight_flip, weight_flip, ← common_terminal_flip d a x u ha hx, polarity_xor]; ring
    · simp [weight_off _ _ _ _ hx]
  · simp [weight_off _ _ _ _ ha]

theorem green_flip [Fintype T] (d : Side T) (a x : Base T m r) :
    signedGreen true d a x = polarity (sheetFlip d a x) * signedGreen false d a x := by
  rw [green_expansion, green_expansion, mul_add, Finset.mul_sum, ← localPart_flip]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [weight_product_flip]
  ring

/-- Concrete sign changes align both the full grounded Green entries and
adjacency, vertex fiber by vertex fiber. -/
def expandedAlignment [Fintype T] (d : Side T) : Alignment (expanded T m r)
    (signing false d) (signing true d) (signedGreen false d) (signedGreen true d) where
  flip := sheetFlip d
  diag := sheetFlip_diag d
  symm := sheetFlip_comm d
  edge := edge_flip d
  green := green_flip d

theorem expanded_equivalent [Fintype T] (hr : 0 < r) (hm : m = continuant (r+1)) (d : Side T) :
    Equivalent (jointLabels (cone (signedLift (expanded T m r) (signing false d))))
      (jointLabels (cone (signedLift (expanded T m r) (signing true d)))) :=
  cones_equivalent _ _ _ _ _ (signedGreen_solve hr hm false d) (signedGreen_solve hr hm true d) (expandedAlignment d)

end JointForest

namespace JointForest

open SimpleGraph

universe u

/-- Some pair attains two, and every pair is within two edges. -/
def DiameterTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ x y, G.dist x y ≤ 2) ∧ ∃ x y, G.dist x y = 2

/-- For each cyclic pattern the expanded signed cones give connected
diameter-two witnesses, equivalent at every joint round, with different
ordinary homomorphism counts. -/
theorem cyclic_witness {T : Type u} [Fintype T] (F : SimpleGraph T) (hF : ¬F.IsAcyclic) :
    ∃ (V : Type u) (finite : Fintype V) (G H : SimpleGraph V), letI := finite
      G.Connected ∧ H.Connected ∧ DiameterTwo G ∧ DiameterTwo H ∧
      Equivalent (jointLabels G) (jointLabels H) ∧ homCount F H < homCount F G := by
  classical
  let : LinearOrder T := LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective
  let r := Fintype.card T + 3
  let m := continuant (r+1)
  have hr : 0 < r := by dsimp [r]; omega
  obtain ⟨d,hcount⟩ := cone_twist_loss F hF m r (by dsimp [r]; omega)
  let B := expanded T m r
  let G := cone (signedLift B (signing false d))
  let H := cone (signedLift B (signing true d))
  refine ⟨Option (Base T m r × Bool), inferInstance, G, H, cone_connected _, cone_connected _, ?_, ?_,
    expanded_equivalent hr (rfl : m = continuant (r+1)) d, hcount⟩
  · exact ⟨cone_dist_le_two _, _, _, opposite_sheets_dist B _ (.inl d.val.1)⟩
  · exact ⟨cone_dist_le_two _, _, _, opposite_sheets_dist B _ (.inl d.val.1)⟩

/-- A pattern is countable when any two finite connected hosts equivalent
under the joint distance refinement have the same number of edge-preserving
vertex maps from the pattern. -/
def CountablePattern {T : Type u} (F : SimpleGraph T) : Prop :=
  ∀ (V W : Type u) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    G.Connected → H.Connected → Equivalent (jointLabels G) (jointLabels H) → homCount F G = homCount F H

/-- The manuscript’s classification for all finite simple patterns. -/
theorem classification {T : Type u} [Fintype T] (F : SimpleGraph T) : CountablePattern F ↔ F.IsAcyclic := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨V, finite, G, H, hg, hh, _, _, he, hlt⟩ := cyclic_witness F hn
    exact (Nat.ne_of_lt hlt) (h V V G H hg hh he).symm
  · intro hf V W _ _ G H hg hh he
    exact forests_countable F G H hf hg hh he

/-- No family of ordinary pattern counts characterizes joint GD-WL equivalence
on connected hosts. The arbitrary family may select patterns of every size. -/
theorem no_hom_family (family : (T : Type) → [Fintype T] → SimpleGraph T → Prop) :
    ¬ (∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      G.Connected → H.Connected →
      (Equivalent (jointLabels G) (jointLabels H) ↔
        ∀ (T : Type) [Fintype T] (F : SimpleGraph T), family T F → homCount F G = homCount F H)) := by
  intro h
  have forest (T : Type) [Fintype T] (F : SimpleGraph T) (hf : family T F) : F.IsAcyclic := by
    apply (classification F).mp
    intro V W _ _ G H hg hh he
    exact (h V W G H hg hh).mp he T F hf
  apply cubic_distinguished
  apply (h (Fin 8) (Fin 8) cube chorded cube_connected chorded_connected).mpr
  intro T _ F hf
  exact cubic_forests F (forest T F hf)

end JointForest
