module

public import SolvedProblems.JointForestElimination

@[expose] public section

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
