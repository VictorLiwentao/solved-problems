module

public import SolvedProblems.AtomSplitFinite
import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

namespace AtomSplit
open Set Equiv

variable {k : ℕ} {block : ℕ → Fin k}

private noncomputable def part (g : stabilizer block) (I : Finset (Fin k)) : stabilizer block := by
  let S := {x : ℕ | block x ∈ I}
  have h (x) : g.val x ∈ S ↔ x ∈ S := by change block (g.val x) ∈ I ↔ block x ∈ I; rw [g.property x]
  refine ⟨cutPerm g.val S h,fun x => ?_⟩
  by_cases hx : x ∈ S
  · rw [cutPerm_of_mem _ _ _ hx,g.property x]
  · rw [cutPerm_outside _ _ _ x hx]

private theorem part_in (g : stabilizer block) (I : Finset (Fin k)) (x : ℕ) (hx : block x ∈ I) :
    (part g I).val x = g.val x := cutPerm_of_mem _ _ _ hx

private theorem part_out (g : stabilizer block) (I : Finset (Fin k)) (x : ℕ) (hx : block x ∉ I) :
    (part g I).val x = x := cutPerm_outside _ _ _ _ hx

/-- Select a genuinely moving infinite partition block unless some finite support
already fixes the entire carrier pointwise. The finite blocks can all be rigidified
using the finitely many singleton cuts of their atoms. -/
theorem pointwise_or_moving {X : Type u} (act : stabilizer block →* Perm X) :
    (∃ Q : List (Set ℕ), ∀ g : stabilizer block, Preserves Q g.val → act g = 1) ∨
    ∃ (i : Fin k), {x | block x = i}.Infinite ∧
      ∃ g : stabilizer block, g.val ∈ Inside {x | block x = i} ∧ act g ≠ 1 := by
  classical
  by_cases h : ∃ (i : Fin k), {x | block x = i}.Infinite ∧
      ∃ g : stabilizer block, g.val ∈ Inside {x | block x = i} ∧ act g ≠ 1
  · exact .inr h
  left
  let F (i : Fin k) : Set ℕ := if {x | block x = i}.Finite then {x | block x = i} else ∅
  let E := ⋃ i, F i
  have efin : E.Finite := Set.finite_iUnion fun i => by
    dsimp [F]
    split <;> simp_all
  let Q : List (Set ℕ) := efin.toFinset.toList.map fun a => {a}
  refine ⟨Q,fun g fixes => ?_⟩
  have fixed (x : ℕ) (hx : x ∈ E) : g.val x = x := by
    have mem : ({x} : Set ℕ) ∈ Q := by simp [Q,hx]
    exact (fixes _ mem x).mpr rfl
  have single (i : Fin k) : act (part g {i}) = 1 := by
    by_cases hi : {x | block x = i}.Finite
    · have eq : part g {i} = 1 := by
        apply Subtype.ext; apply Equiv.ext; intro x
        by_cases hx : block x = i
        · rw [part_in g _ x (by simpa using hx)]
          exact fixed x (mem_iUnion.mpr ⟨i,by simpa [F,hi] using hx⟩)
        · exact part_out g _ x (by simpa using hx)
      rw [eq,map_one]
    · by_contra ne
      exact h ⟨i,hi,part g {i},fun x hx => part_out g _ x (by simpa using hx),ne⟩
  have pieces (I : Finset (Fin k)) : act (part g I) = 1 := by
    induction I using Finset.induction_on with
    | empty =>
      have eq : part g ∅ = 1 := Subtype.ext (Equiv.ext fun x => part_out g _ x (by simp))
      rw [eq,map_one]
    | @insert i I hi ih =>
      have eq : part g (insert i I) = part g {i} * part g I := by
        apply Subtype.ext; apply Equiv.ext; intro x
        change (part g _).val x = (part g {i}).val ((part g I).val x)
        by_cases mem : block x ∈ I
        · have ne : block x ≠ i := fun e => hi (e ▸ mem)
          rw [part_in g _ x (Finset.mem_insert_of_mem mem),part_in g I x mem]
          rw [part_out g {i} _ (by simp [g.property x,ne])]
        · rw [part_out g I x mem]
          by_cases eq : block x = i
          · rw [part_in g _ x (by simp [eq]),part_in g _ x (by simp [eq])]
          · rw [part_out g _ x (by simp [eq,mem]),part_out g _ x (by simp [eq])]
      rw [eq,map_mul,single,ih,mul_one]
  have all : part g Finset.univ = g := Subtype.ext (Equiv.ext fun x => part_in g _ x (Finset.mem_univ _))
  exact all ▸ pieces Finset.univ

end AtomSplit
