module

public import SolvedProblems.UncountableGenerationModel
import Mathlib.Data.List.OfFn

@[expose] public section

open Set
namespace UncountableGeneration

/-- Keep the first observed column and exceed the sum of the observed word codes in height. -/
theorem ordinary_generator : Ordinary := by
  let g (l : List ℕ) := Nat.pair (col l.headI) (l.sum + 1)
  have hsum : Primrec (List.sum : List ℕ → ℕ) := by
    have h := Primrec.list_foldr (Primrec.id : Primrec (id : List ℕ → List ℕ))
      (Primrec.const 0) (Primrec.to₂ (Primrec.nat_add.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
    exact h.of_eq fun l ↦ by induction l <;> simp_all
  refine ⟨g, Primrec₂.natPair.comp ((Primrec.fst.comp Primrec.unpair).comp
    Primrec.list_headI) (Primrec.succ.comp hsum), ?_⟩
  intro A _ x hx t
  have hfirst : (History x t).headI = x 0 := by simp [History, List.ofFn_succ]
  have hm : x 0 ∈ Language A := hx ▸ mem_range_self 0
  constructor
  · simpa only [g, Language, mem_ofPred_eq, col, Nat.unpair_pair, hfirst] using hm
  · intro j hj heq
    have hmem : x j ∈ History x t := List.mem_ofFn.mpr ⟨⟨j, by omega⟩, rfl⟩
    have hle : x j ≤ (History x t).sum := List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ hmem
    have hb := Nat.right_le_pair (col (History x t).headI) ((History x t).sum + 1)
    change Nat.pair _ _ = _ at heq
    omega

/-- No sequence lists all nonempty unions of complete columns. -/
theorem uncountably_many_languages :
    ¬ ∃ f : ℕ → Set ℕ, ∀ A : Set ℕ, A.Nonempty → ∃ n, f n = Language A := by
  rintro ⟨f, hall⟩
  let A : Set ℕ := insert 0 {j | ∃ n, j = n+1 ∧ Nat.pair (n+1) 0 ∉ f n}
  obtain ⟨n, hn⟩ := hall A ⟨0, mem_insert ..⟩
  have h : Nat.pair (n+1) 0 ∈ f n ↔ Nat.pair (n+1) 0 ∉ f n := calc
    _ ↔ n+1 ∈ A := by rw [hn]; simp [Language, col]
    _ ↔ _ := by simp [A]
  by_cases hm : Nat.pair (n+1) 0 ∈ f n
  · exact h.mp hm hm
  · exact hm (h.mpr hm)

end UncountableGeneration
