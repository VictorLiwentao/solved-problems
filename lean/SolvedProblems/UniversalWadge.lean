module

public import SolvedProblems.UniversalWadgeClosure
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

namespace UniversalWadge

open Set Filter
open scoped Classical Topology

/-- Additive Borel codes are Borel measurable at every index. -/
theorem additive_borel {X} [TopologicalSpace X] {α S} (h : AdditiveClass X α S) : @MeasurableSet X (borel X) S := by
  let _ : MeasurableSpace X := borel X
  let _ : BorelSpace X := ⟨rfl⟩
  induction h with | basic _ ho => exact ho.measurableSet | unions _ _ _ ih => exact .iUnion ih | lowerCompl _ _ ih => exact ih.compl

theorem low_open {X} [TopologicalSpace X] {α S} (h : AdditiveClass X α S) (le : α≤1) : IsOpen S := by
  induction h with
  | basic _ ho => exact ho
  | unions _ _ _ ih => exact isOpen_iUnion (fun i => ih i le)
  | lowerCompl low h ih => exact False.elim ((not_lt_of_ge (show (1:Ordinal) ≤ _ by simpa using Order.succ_le_of_lt (additive_positive h))) (low.trans_le le))

theorem not_closed (I : Ideal) : ¬IsClosed (cantors I) := by
  intro closed
  let a (m n : ℕ) : Bool := decide (n<m)
  have limit : Tendsto a atTop (𝓝 (fun _ : ℕ => true)) := by
    apply tendsto_pi_nhds.mpr;intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with m hm;simp [a,hm]
  have small (m) : a m∈cantors I := by
    apply I.shrink (t := (Finset.range m:Set ℕ)) _ (I.finite _ (Finset.range m).finite_toSet)
    intro n hn; exact Finset.mem_range.mpr (by simpa [support,a] using hn)
  apply I.proper
  simpa [cantors,support] using closed.mem_of_tendsto limit (.of_forall small)

/-- The ideal convergence locus is an additive subgroup of the circle. -/
def convergenceSubgroup (I : Ideal) (seq : ℕ → ℕ) : AddSubgroup Circle where
  carrier := locus I seq
  zero_mem' := by
    intro ε ep
    simpa [not_lt.mpr ep.le] using I.finite (∅ : Set ℕ) finite_empty
  add_mem' := by
    intro x y hx hy ε ep
    have half : 0 < ε/2 := by linarith
    apply I.shrink _ (I.union (hx _ half) (hy _ half))
    intro n hn
    by_contra! no
    change ¬(ε/2 < ‖seq n • x‖ ∨ ε/2 < ‖seq n • y‖) at no
    push Not at no
    change ε < ‖seq n • (x+y)‖ at hn
    rw [smul_add] at hn
    linarith [norm_add_le (seq n • x) (seq n • y)]
  neg_mem' := by
    intro x hx ε ep
    simpa using hx ε ep

/-- This is the Borel Wadge alternative between two spaces. It is stated explicitly
so the transfer can be used separately from a formalization of Borel determinacy. -/
def WadgeAlternative (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Prop :=
  ∀ (S : Set X) (T : Set Y), @MeasurableSet X (borel X) S → @MeasurableSet Y (borel Y) T →
    Reduces S T ∨ Reduces Tᶜ S

def ExactRank (I : Ideal) (α : Ordinal.{0}) : Prop :=
  MultiplicativeClass Cantor α (cantors I) ∧ ∀ β<α, ¬MultiplicativeClass Cantor β (cantors I)

/-- For every ideal the fixed character subgroup has the same multiplicative upper
rank. Under the Borel Wadge alternative for the domain, exact rank implies hardness. -/
theorem rankTransfer {X : Type} [TopologicalSpace X] [PerfectlyNormalSpace X] (I : Ideal) (α : Ordinal.{0})
    (rank : ExactRank I α) (alternative : WadgeAlternative X Cantor) :
    MultiplicativeClass Circle α (locus I character) ∧
      ∀ S : Set X, MultiplicativeClass X α S → Reduces S (locus I character) := by
  refine ⟨(thresholdRanks I (fun n (x : Circle) => ‖character n • x‖)
    (fun n => (continuous_const_smul (character n)).norm) α).1 rank.1,?_⟩
  have gt : 1<α := by
    by_contra! le;exact not_closed I (isOpen_compl_iff.mp (low_open rank.1 le))
  have hard (β) (low : β<α) (S : Set X) (hS : AdditiveClass X β S) : Reduces S (cantors I) := by
    have borelI := MeasurableSet.of_compl (additive_borel rank.1)
    rcases alternative S (cantors I) (additive_borel hS) borelI with yes | no
    · exact yes
    · obtain ⟨f,cf,e⟩ := no
      have pre := additive_preimage cf hS;rw [e] at pre;exact False.elim (rank.2 β low pre)
  exact fun _ h => lower_classes_suffice I gt hard h

/-- Kwela's character version, with both rank estimates for every continuous sequence
of circle-valued characters on a topological group. -/
theorem characterRanks {G : Type} [TopologicalSpace G] [AddGroup G] (I : Ideal)
    (f : ℕ → ContinuousAddMonoidHom G Circle) (α : Ordinal.{0}) :
    (MultiplicativeClass Cantor α (cantors I) → MultiplicativeClass G α (realLocus I (fun n x => ‖f n x‖))) ∧
    (AdditiveClass Cantor α (cantors I) → MultiplicativeClass G (α+1) (realLocus I (fun n x => ‖f n x‖))) :=
  thresholdRanks I _ (fun n => (f n).continuous.norm) α

end UniversalWadge
