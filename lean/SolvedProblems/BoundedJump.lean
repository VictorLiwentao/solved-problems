module

public import SolvedProblems.BoundedJumpConstruction
import SolvedProblems.BoundedJumpGeometry
import SolvedProblems.BoundedJumpSeries

public section

namespace BoundedJump

/-- An accepting offset word and a counted permutation determine each other. -/
noncomputable def acceptingEquiv (h : Fits k B) (n : Nat) :
    {w : Fin n → Letter m // (machine m k B).accepts (List.ofFn w) = true} ≃
      {p : Equiv.Perm (Fin n) // Counted m B p} :=
  (Equiv.subtypeEquivRight (fun w => machine_spec h w)).trans (wordEquiv m B n)

theorem counted_words (h : Fits k B) (hn : 0 < n) :
    (machine m k B).wordCount n (machine m k B).start = permutationCount m B n := by
  classical
  simp only [permutationCount,ite_eq_right (Nat.ne_of_gt hn)]
  rw [← Fintype.card_congr (acceptingEquiv (m := m) h n)]
  symm
  apply Fintype.card_of_subtype
  intro w
  simp [Machine.accepts]

/-- Correctness of the executable compiler on the supplied pattern family. -/
theorem machine_enumerates (h : Fits k B) : Enumeration m B (machine m k B) := by
  let M := machine m k B
  refine ⟨fun n => ⟨acceptingEquiv h n⟩, fun _ hn => counted_words h hn, ?_,
    wordCount_zero M, wordCount_step M, table_complexity M⟩
  have hc (s : Nat) : (permutationCount m B s : ℤ) =
      (if s = 0 then 1 else (M.wordCount s M.start : ℤ)) := by
    by_cases hs : s = 0
    · simp [hs,permutationCount]
    · simpa [hs] using congrArg (fun v : Nat => (v : ℤ))
        (counted_words (m := m) h (Nat.pos_of_ne_zero hs)).symm
  obtain ⟨d,den,num,h0,hf,hn⟩ := wordCount_rational M
  exact ⟨d,den,num,h0,hf,fun n => by simpa only [hc] using hn n⟩

/-- For every jump bound and finite set of classical forbidden patterns, construct
a deterministic automaton in bijection with the restricted permutations. Its state
bound depends only on the jump bound and maximum pattern length. -/
theorem finiteEnumeration :
    ∃ (build : (m k : Nat) → List (List Nat) → Machine (Letter m)) (bound : Nat → Nat → Nat),
      ∀ m k B, Fits k B → Enumeration m B (build m k B) ∧
        (build m k B).finite.elems.card ≤ bound m k := by
  exact ⟨machine,stateBound,fun _ _ _ h => ⟨machine_enumerates h, machine_size _ _ _⟩⟩

end BoundedJump
