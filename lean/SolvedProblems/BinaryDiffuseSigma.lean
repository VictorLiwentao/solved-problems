module

public import SolvedProblems.BinaryDiffuseModel

@[expose] public section

open Set MeasureTheory

namespace BinaryDiffuse

/-- The smallest sigma algebra making every allowed binary reward measurable
is the full powerset on the arms. -/
theorem reward_sigma_algebra :
    MeasurableSpace.generateFrom {U : Set Arm | Eligible U} = ⊤ := by
  classical
  let s := MeasurableSpace.generateFrom {U : Set Arm | Eligible U}
  have basic (f : Coord → Bool) :
      @MeasurableSet Arm s (winSet fun x ↦ some (f x)) := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact Or.inr ⟨_, by simp, rfl⟩
  apply top_unique
  intro T _
  let fiber (b : Bool) := winSet fun _ : Coord ↦ some b
  let graph (b : Bool) := winSet fun x ↦ some (if (show Arm from (x,b)) ∈ T then b else !b)
  have split : T = (fiber false ∩ graph false) ∪ (fiber true ∩ graph true) := by
    ext a
    obtain ⟨x,b⟩ := a
    change (show Arm from (x,b)) ∈ T ↔
      (some false = some b ∧ some (if (show Arm from (x,false)) ∈ T then false else !false) = some b) ∨
      (some true = some b ∧ some (if (show Arm from (x,true)) ∈ T then true else !true) = some b)
    cases b <;> by_cases hf : (show Arm from (x,false)) ∈ T <;>
      by_cases ht : (show Arm from (x,true)) ∈ T <;> simp [hf, ht]
  rw [split]
  exact @MeasurableSet.union Arm s _ _ (@MeasurableSet.inter Arm s _ _ (basic _) (basic _))
    (@MeasurableSet.inter Arm s _ _ (basic _) (basic _))

end BinaryDiffuse
