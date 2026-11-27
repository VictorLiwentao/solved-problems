module

public import SolvedProblems.UniversalWadgeCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

namespace UniversalWadge

open Set Filter
open scoped Topology Classical

/-- A proper ideal of subsets of ℕ containing every finite set. -/
structure Ideal where
  family : Set (Set ℕ)
  finite : ∀ s : Set ℕ, s.Finite → s ∈ family
  shrink : ∀ {s t : Set ℕ}, s ⊆ t → t ∈ family → s ∈ family
  union : ∀ {s t : Set ℕ}, s∈family → t∈family → s∪t∈family
  proper : univ ∉ family

def support (a : Cantor) : Set ℕ := {n | a n=true}

def cantors (I : Ideal) : Set Cantor := {a | support a ∈ I.family}

def locus (I : Ideal) (seq : ℕ → ℕ) : Set Circle :=
  {x | ∀ ε : ℝ, 0 < ε → {n | ε < ‖seq n • x‖} ∈ I.family}

theorem ideal_finite_union (I : Ideal) (A : ℕ → Set ℕ) (h : ∀ j,A j∈I.family) (s : Finset ℕ) :
    (⋃ j∈s,A j)∈I.family := by
  induction s using Finset.induction_on with
  | empty => simpa using I.finite ∅ finite_empty
  | insert i s hi ih => simpa using I.union (h i) ih

/-- One explicit continuous code simultaneously reduces the countable power of
every ideal to the ideal-convergence subgroup for the same integer character sequence. -/
theorem productReduction : Continuous code ∧ ∀ (I : Ideal) (a : Tests),
    code a ∈ locus I character ↔ ∀ j,a j ∈ cantors I := by
  refine ⟨code_continuous, fun I a => ⟨?_,?_⟩⟩
  · intro hl j
    let ε := dyad (j+2)/2
    have ep : 0 < ε := div_pos (dyad_pos _) (by norm_num)
    have ex := hl ε ep
    apply I.shrink (t := (Finset.range j : Set ℕ) ∪ {n | ε < ‖character n • code a‖}) _ (I.union (I.finite _ (Finset.range j).finite_toSet) ex)
    intro n hit
    by_cases hn : n<j
    · exact Or.inl (Finset.mem_range.mpr hn)
    · right;change ε < ‖character n • code a‖;rw [norm_character]
      have le := digit_ge (Nat.le_of_not_gt hn) hit
      have t := (tail_range a n).1;dsimp [ε];linarith [dyad_pos (j+2)]
  · intro rows ε ep
    obtain ⟨N,hN⟩ := eventually_atTop.mp (dyad_limit.eventually (gt_mem_nhds (show 0 < ε/2 by linarith)))
    apply I.shrink (t := (Finset.range N : Set ℕ) ∪ ⋃ j∈Finset.range N, support (a j)) _
      (I.union (I.finite _ (Finset.range N).finite_toSet) (ideal_finite_union I _ rows _))
    intro n hit
    by_cases hn : n<N
    · exact Or.inl (Finset.mem_range.mpr hn)
    · right;change ε < ‖character n • code a‖ at hit;rw [norm_character] at hit
      have tl := (tail_range a n).2
      have small := hN (n+1) (by omega)
      obtain ⟨j,hd⟩ := digit_realized a n
      by_cases hj : a j.val n=true
      · have above : ε/2 < dyad (j.val+2) := by rw [hd,bitValue,ite_eq_left hj] at hit;linarith
        have little : j.val<N := by by_contra! h;linarith [hN (j.val+2) (by omega)]
        exact mem_iUnion.mpr ⟨j.val,mem_iUnion.mpr ⟨Finset.mem_range.mpr little,hj⟩⟩
      · rw [hd,bitValue,ite_eq_right hj] at hit;linarith

end UniversalWadge
