module

public import SolvedProblems.EMXModel
public import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Finset.Card

@[expose] public section

namespace EMX

open scoped Classical

/-- Fix one cyclic successor permutation on each finite set. -/
noncomputable def cycle {X : Type} [Fintype X] [DecidableEq X] (U : Finset X) :
    Equiv.Perm X := (U.exists_cycleOn).choose

theorem escapes {X : Type} [Fintype X] [DecidableEq X] {S U : Finset X}
    (hs : S.Nonempty) (sub : S ⊆ U) (gap : (U \ S).Nonempty) :
    ∃ x ∈ S, cycle U x ∈ U \ S := by
  classical
  obtain ⟨a,ha⟩ := hs
  obtain ⟨b,hb⟩ := gap
  obtain ⟨hbU,hbS⟩ := Finset.mem_sdiff.mp hb
  have cyc : (cycle U).IsCycleOn (U : Set X) := U.exists_cycleOn.choose_spec.1
  obtain ⟨n, _, hn⟩ := cyc.exists_pow_eq (sub ha) hbU
  by_contra! h
  have stable (x) (hx : x ∈ S) : cycle U x ∈ S := by
    have inU : cycle U x ∈ U := cyc.apply_mem_iff.mpr (sub hx)
    by_contra out
    exact h x hx (Finset.mem_sdiff.mpr ⟨inU, out⟩)
  have stay (k : ℕ) : (cycle U ^ k) a ∈ S := by
    induction k with
    | zero => simpa using ha
    | succ k ih => simpa [pow_succ', Equiv.Perm.mul_apply] using stable _ ih
  exact hbS (hn ▸ stay n)

/-- Processing the anchors from the end of the list, omit the cyclic successor
among all positions which have not already been omitted. -/
noncomputable def grow {X : Type} [Fintype X] [DecidableEq X] : List X → Finset X
  | [] => ∅
  | x :: w => let omitted := grow w; insert (cycle omittedᶜ x) omitted

theorem encode_holes {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (hs : S.Nonempty)
    (k : ℕ) (hcard : k ≤ Sᶜ.card) :
    ∃ w : List X, w.length = k ∧ (∀ x ∈ w, x ∈ S) ∧
      (grow w).card = k ∧ grow w ⊆ Sᶜ := by
  induction k with
  | zero => exact ⟨[], rfl, by simp, rfl, Finset.empty_subset _⟩
  | succ k ih =>
    obtain ⟨w,hw,hwS,hg,hgS⟩ := ih (Nat.le_of_succ_le hcard)
    have sub : S ⊆ (grow w)ᶜ := by
      intro x hx
      exact Finset.mem_compl.mpr (fun hc => Finset.mem_compl.mp (hgS hc) hx)
    have gap : ((grow w)ᶜ \ S).Nonempty := by
      have card : (grow w).card < Sᶜ.card := by omega
      obtain ⟨x,hx,hg⟩ := Finset.exists_mem_notMem_of_card_lt_card card
      exact ⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hg,Finset.mem_compl.mp hx⟩⟩
    obtain ⟨x,hx,hnext⟩ := escapes hs sub gap
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hnext
    refine ⟨x::w, by simp [hw], ?_, ?_, ?_⟩
    · simpa [hx] using hwS
    · simp [grow, Finset.mem_compl.mp hin, hg]
    · exact Finset.insert_subset (Finset.mem_compl.mpr hout) hgS

end EMX
