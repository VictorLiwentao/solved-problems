module

public import SolvedProblems.ResistanceRecovery
public import SolvedProblems.ResistanceVoltage
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Matrix Finset
namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def binaryWeights (G : SimpleGraph V) : Matrix V V ℝ := by
  classical
  exact G.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
private theorem weights_apply (G : SimpleGraph V) (i j : V) [Decidable (G.Adj i j)] :
    binaryWeights G i j = if G.Adj i j then 1 else 0 := by classical simp [binaryWeights,SimpleGraph.adjMatrix_apply]

omit [Fintype V] [DecidableEq V] in
private theorem weights_symm (G : SimpleGraph V) (i j : V) : binaryWeights G i j = binaryWeights G j i := by
  classical
  simp [weights_apply,G.adj_comm]

private theorem weights_support (G : SimpleGraph V) : supportGraph (binaryWeights G) (weights_symm G) = G := by
  classical
  ext i j
  change (i ≠ j ∧ 0 < binaryWeights G i j) ↔ G.Adj i j
  by_cases a : G.Adj i j
  · simp [weights_apply, a, a.ne]
  · simp [weights_apply, a]

private theorem weights_lap (G : SimpleGraph V) [DecidableRel G.Adj] :
    weightedLap (binaryWeights G) = G.lapMatrix ℝ := by
  classical
  unfold weightedLap SimpleGraph.lapMatrix SimpleGraph.degMatrix
  congr 1
  · congr 1
    funext i
    simp_rw [weights_apply, G.degree_eq_sum_if_adj]
  · ext i j
    simp [weights_apply, SimpleGraph.adjMatrix_apply]

theorem unweighted_voltage (G : SimpleGraph V) (c : G.Connected) (i j : V) :
    weightedResistance (binaryWeights G) 1 i j = ResistanceLifts.resistance G i j := by
  classical
  let w := binaryWeights G
  have h := weights_symm G
  have hn (i j : V) : 0 ≤ w i j := by simp [w,weights_apply]; split <;> norm_num
  have hc : (supportGraph w h).Connected := weights_support G ▸ c
  let p := (grounded w 1)⁻¹ *ᵥ demand i j
  have eq : weightedLap w *ᵥ p = demand i j := weighted_kirchhoff w h hn hc one_pos i j
  rw [weighted_voltage w h hn hc one_pos i j p eq]
  apply Eq.symm
  apply ResistanceLifts.resistance_of_potential (c i j)
  change G.lapMatrix ℝ *ᵥ p = _
  rw [← weights_lap, eq]
  ext k
  simp [demand,Pi.single_apply,eq_comm]

private theorem symmetry (G : SimpleGraph V) (c : G.Connected) (i j : V) :
    ResistanceLifts.resistance G i j = ResistanceLifts.resistance G j i := by
  rw [← unweighted_voltage G c, ← unweighted_voltage G c]
  unfold weightedResistance drop
  ring

/-- All known adjacencies and the listed voltage measurements identify at most
one connected, labeled simple graph of the specified order. Pairs in the list
are unordered, and duplicate measurements are permitted. -/
def Identifiable (n : ℕ) (η : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) [Fintype I] (E : I → V × V)
    (y : I → ℝ) (G H : SimpleGraph V), Fintype.card V = n → G.Connected → H.Connected →
    (∀ i j, (∀ q, E q ≠ (i,j) ∧ E q ≠ (j,i)) → (G.Adj i j ↔ H.Adj i j)) →
    (∀ q, |y q - ResistanceLifts.resistance G (E q).1 (E q).2| ≤ η) →
    (∀ q, |y q - ResistanceLifts.resistance H (E q).1 (E q).2| ≤ η) → G = H

/-- Below 1/n² the missing-pair readings determine every missing adjacency. -/
theorem binary_identifiability (n : ℕ) (η : ℝ) (hη : η < 1/(n:ℝ)^2) : Identifiable n η := by
  classical
  intro V _ _ I _ E y G H card g h known gy hy
  let U (i j : V) := ∃ q, E q = (i,j) ∨ E q = (j,i)
  let a (i j : V) := if q : U i j then y q.choose else 0
  have noise (F : SimpleGraph V) (fc : F.Connected) (fy : ∀ q, |y q-ResistanceLifts.resistance F (E q).1 (E q).2| ≤ η)
      (i j : V) (u : U i j) : |weightedResistance (binaryWeights F) 1 i j - a i j| ≤ η := by
    rw [unweighted_voltage F fc, abs_sub_comm]
    change |(if q : U i j then y q.choose else 0) - _| ≤ _
    rw [dite_eq_left u]
    have good := fy u.choose
    rcases u.choose_spec with s|s <;> rw [s] at good
    · exact good
    · simpa only [symmetry F fc j i] using good
  have same := noisy_identifiability (binaryWeights G) (binaryWeights H) 1 1 η U a
    (weights_symm G) (weights_symm H) (by simp [weights_apply]) (by simp [weights_apply])
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by rwa [weights_support]) (by rwa [weights_support]) one_pos
    (by intro i j; rw [weights_apply,weights_apply]; split <;> split <;> norm_num)
    (by intro i j no; have e := known i j (fun q => ⟨fun eq => no ⟨q,Or.inl eq⟩,fun eq => no ⟨q,Or.inr eq⟩⟩)
        simp [weights_apply,e])
    (noise G g gy) (noise H h hy) (by simpa only [card,mul_one] using hη)
  ext i j
  have e := congrFun (congrFun same i) j
  simp only [weights_apply] at e
  by_cases a : G.Adj i j <;> by_cases b : H.Adj i j <;> simp_all

/-- Four ambiguous unknown pairs give the upper bound for every n=k+4. -/
theorem binary_obstruction (k : ℕ) (η : ℝ) (hη : radius k ≤ η) : ¬Identifiable (k+4) η := by
  intro id
  obtain ⟨G,H,g,h,diff,known,y,err⟩ := four_unknown_pairs k
  apply diff
  apply id (Vertex k) Query endpoints (fun q => (y q : ℝ)) G H (by simp [Vertex]; omega) g h known
  · intro q
    exact (err q).1.le.trans hη
  · intro q
    exact (err q).2.le.trans hη

end ResistanceRecovery
