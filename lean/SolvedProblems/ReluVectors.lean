module

public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

namespace ReluMoments

abbrev Vector (p : ℕ) := Fin p → ℝ
abbrev Measurements (m j : ℕ) := (Fin m × Fin j) → ℝ

/-- Apply fixed linear measurements to a finite vector of moments. -/
noncomputable def measureVector {m j : ℕ} (A : Measurements m j) (v : Vector j) : Vector m :=
  fun i => ∑ k, A (i,k) * v k

end ReluMoments
