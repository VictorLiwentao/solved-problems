module

public import SolvedProblems.EMXUpperDecoder
import SolvedProblems.EMXCounting
import Mathlib.Data.List.OfFn

@[expose] public section

namespace EMX

open scoped Classical

theorem lift_project {j : ℕ} (x : Point) (hj : x.1 = j) : Sigma.mk j (project j x) = x := by
  obtain ⟨k,c⟩ := x
  change k = j at hj
  subst j
  simp [project_mk]

/-- A single decoder at each size bound handles all realizable samples up to
that size, including ordered lists with repetitions. -/
def Within (d m : ℕ) : Prop :=
  ∃ D : Fin 1 → Message Point d → Hyp, ∀ n ≤ m, Reconstructs d 1 n D

theorem logUpper (m : ℕ) : Within (max 1 m.log2) m := by
  let d := max 1 m.log2
  refine ⟨decoder, ?_⟩
  intro n hn xs hx
  by_cases empty : n = 0
  · subst n
    let w : Message Point d := ⟨⟨0, Nat.zero_lt_succ _⟩, Fin.elim0⟩
    exact ⟨0,w,fun i => i.elim0,fun i => i.elim0⟩
  obtain ⟨⟨j,h⟩, hh⟩ := hx
  let S := Finset.univ.image (fun i => project j (xs i))
  have loc (i) : Sigma.mk j (project j (xs i)) = xs i := lift_project _ (in_block (hh i))
  let i₀ : Fin n := ⟨0,Nat.pos_of_ne_zero empty⟩
  have hs : S.Nonempty := ⟨_,Finset.mem_image_of_mem _ (Finset.mem_univ i₀)⟩
  have fit : S ⊆ h.valᶜ := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    have hi := hh i
    rw [← loc i] at hi
    simpa [support] using hi
  obtain ⟨w,inside,size,cover⟩ := choose_anchors S hs ⟨h,fit⟩
  have hwd : w.length ≤ d := by
    rcases size with size | ⟨size,rowCount⟩
    · rw [size]; exact Nat.le_max_left .. 
    · apply (show w.length ≤ m.log2 from ?_).trans (Nat.le_max_right ..)
      rw [size]
      apply (Nat.le_log2 (by omega : m ≠ 0)).mpr
      have cardS : S.card ≤ n := by simpa [S] using
        (Finset.card_image_le (s := Finset.univ) (f := fun i => project j (xs i)))
      exact rowCount.trans (cardS.trans hn)
  let v : Message Point d := ⟨⟨w.length, Nat.lt_succ_of_le hwd⟩, fun i => Sigma.mk j w[i.val]⟩
  have dl : decoder 0 v = restore (w.map (Sigma.mk j)) := by
    exact congrArg restore (List.ofFn_getElem_eq_map w (Sigma.mk j))
  refine ⟨0, v, ?_, ?_⟩
  · intro i
    have hi : w[i.val] ∈ S := inside _ (List.getElem_mem _)
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
    exact ⟨k, (congrArg (Sigma.mk j) hk.symm).trans (loc k)⟩
  · intro i
    rw [dl, ← loc i]
    exact cover _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end EMX
