module

public import SolvedProblems.UncountableGenerationSparse
public import SolvedProblems.UncountableGenerationRenyiModel

@[expose] public section

open MeasureTheory Set Function
namespace UncountableGeneration

theorem pure_zero {P : Rule} (hp : ProbLaw P) (hc : Causal P) (ε : ℝ)
    (hpriv : PrivateWith P (fun p ↦ Real.exp ε * p)) : ZeroUtility P := by
  apply vanishing_modulus_zero hp hc _ hpriv
  intro a ha
  refine ⟨a / Real.exp ε, div_pos ha (Real.exp_pos _), fun p _ hp ↦ ?_⟩
  simpa only [mul_comm] using (lt_div_iff₀ (Real.exp_pos ε)).mp hp

theorem renyi_zero {P : Rule} (hp : ProbLaw P) (hc : Causal P) {α D : ℝ}
    (hα : 1 < α) (hpriv : RenyiBudget P α D) : ZeroUtility P := by
  let K := Real.exp ((α-1)*D)
  have hK : 0 < K := Real.exp_pos _
  have hα' : 0 < α := by linarith
  have ha' : 0 < α-1 := by linarith
  let ω (p : ℝ) := (K * p^(α-1))^α⁻¹
  have vanish : Vanishes ω := by
    intro a ha
    let δ := (a ^ α / K) ^ (α-1)⁻¹
    refine ⟨δ, Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos ha _) hK) _,
      fun p hp hpd ↦ ?_⟩
    apply (Real.rpow_inv_lt_iff_of_pos (mul_nonneg hK.le (Real.rpow_nonneg hp.1 _)) ha.le hα').2
    have hh := (Real.lt_rpow_inv_iff_of_pos hp.1
      (div_pos (Real.rpow_pos_of_pos ha α) hK).le ha').1 hpd
    simpa only [mul_comm] using (lt_div_iff₀ hK).mp hh
  apply vanishing_modulus_zero hp hc vanish
  intro x y hxy E hE
  let := hp x
  let := hp y
  obtain ⟨hac, htest⟩ := hpriv x y hxy
  apply (Real.le_rpow_inv_iff_of_pos measureReal_nonneg
    (mul_nonneg hK.le (Real.rpow_nonneg measureReal_nonneg _)) hα').2
  by_cases hz : (P y).real E = 0
  · have hxz : (P x).real E = 0 := (measureReal_eq_zero_iff (measure_ne_top (P x) E)).mpr
      (hac ((measureReal_eq_zero_iff (measure_ne_top (P y) E)).mp hz))
    rw [hxz, Real.zero_rpow hα'.ne']
    positivity
  · have h := htest 1 (fun _ ↦ E) (fun i j h ↦ (h (Subsingleton.elim i j)).elim) (fun _ ↦ hE)
    simp only [Fin.sum_univ_one] at h
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)) _)).mp h

end UncountableGeneration
