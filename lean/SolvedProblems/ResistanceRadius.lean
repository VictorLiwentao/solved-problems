module

public import SolvedProblems.ResistanceBinaryRecovery

@[expose] public section

open Filter Set
open scoped Topology

namespace ResistanceRecovery

/-- The supremum of the adversarial error levels at which all compatible
connected graphs are uniquely identified by the specified measurements. -/
noncomputable def recoveryRadius (n : ℕ) : ℝ := sSup {η : ℝ | Identifiable n η}

theorem sharp_bounds (k : ℕ) :
    1/((k:ℝ)+4)^2 ≤ recoveryRadius (k+4) ∧ recoveryRadius (k+4) ≤ radius k := by
  let S := {η : ℝ | Identifiable (k+4) η}
  let a : ℝ := 1/((k:ℝ)+4)^2
  have small : Set.Iio a ⊆ S := by
    intro η h
    exact binary_identifiability _ _ (by simpa [a] using h)
  have cap : ∀ η ∈ S, η ≤ radius k := by
    intro η h
    by_contra! large
    exact binary_obstruction k η large.le h
  have finite : BddAbove S := ⟨_,cap⟩
  have nonempty : S.Nonempty := Set.nonempty_Iio.mono small
  change a ≤ sSup S ∧ sSup S ≤ radius k
  exact ⟨by simpa only [csSup_Iio] using csSup_le_csSup finite Set.nonempty_Iio small, csSup_le nonempty cap⟩

/-- The leading constant of the worst-case unweighted error threshold for
missing-pair measurements is exactly one. -/
theorem sharp_limit : Tendsto (fun k : ℕ => ((k:ℝ)+4)^2 * recoveryRadius (k+4)) atTop (𝓝 1) := by
  have hlow (k : ℕ) : 1 ≤ ((k:ℝ)+4)^2*recoveryRadius (k+4) := by
    have h := mul_le_mul_of_nonneg_left (sharp_bounds k).1 (sq_nonneg ((k:ℝ)+4))
    have denom : ((k:ℝ)+4)^2 ≠ 0 := by positivity
    simpa only [one_div, mul_inv_cancel₀ denom] using h
  have high (k : ℕ) : ((k:ℝ)+4)^2*recoveryRadius (k+4) ≤ 1+2/((k:ℝ)+2) := by
    apply (mul_le_mul_of_nonneg_left (sharp_bounds k).2 (sq_nonneg ((k:ℝ)+4))).trans_eq
    unfold radius
    have h₁ : (k:ℝ)+4 ≠ 0 := by positivity
    have h₂ : (k:ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring
  have den : Tendsto (fun k : ℕ => (k:ℝ)+2) atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have limit : Tendsto (fun k : ℕ => 1+2/((k:ℝ)+2)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_const_nhds.div_atTop den (a := (2:ℝ)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds limit hlow high

end ResistanceRecovery
