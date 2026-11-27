module

public import SolvedProblems.JointForestModel

@[expose] public section

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
