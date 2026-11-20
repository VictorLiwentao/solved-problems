module

public import SolvedProblems.UncountableGenerationModel
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

open Set MeasureTheory Filter
open scoped ENNReal BigOperators

namespace UncountableGeneration

private theorem measurable_success (A : Set ℕ) (x : Input) : MeasurableSet (Success A x) := by
  have eq : Success A x = ⋃ N : ℕ, ⋂ t : {t : ℕ // N ≤ t},
      ({u : Output | col (u t.val) ∈ A} ∩ ⋂ i : Fin (t.val+1), {u : Output | u t.val ≠ x i}) := by
    ext u; simp [Success, Fin.forall_iff]
  rw [eq]
  apply MeasurableSet.iUnion; intro N
  apply MeasurableSet.iInter; intro t
  apply MeasurableSet.inter
  · exact ((measurable_of_countable col).comp (measurable_pi_apply t.val)) (Set.to_countable A).measurableSet
  · apply MeasurableSet.iInter; intro i
    exact (measurableSet_eq_fun (measurable_pi_apply t.val) (measurable_const (a := x i))).compl

private def release (r : ℕ) (x : Input) (h : Output) (t : ℕ) : ℕ :=
  if r ≤ t then Nat.pair (col (x r)) (h t) else 0

private theorem measurable_release (x : Input) (r : ℕ) : Measurable (release r x) := by
  apply measurable_pi_lambda; intro t
  by_cases h : r ≤ t
  · simpa only [release,ite_eq_left h,Function.comp_def] using
      ((measurable_of_countable (Nat.pair (col (x r)))).comp (measurable_pi_apply t) : Measurable (fun z : Output => Nat.pair (col (x r)) (z t)))
  · simpa only [release,ite_eq_right h] using (measurable_const : Measurable (fun _ : Output => (0:ℕ)))

/-- Randomly select one of the first m input records. Its column is used only
after that record has arrived. The height law eventually avoids every finite observed prefix. -/
theorem lottery_of_heights (ν : Measure Output) [IsProbabilityMeasure ν]
    (fresh : ∀ x : Input, ∀ᵐ h ∂ν, ∃ N : ℕ, ∀ t ≥ N, ∀ i ≤ t, h t ≠ (x i).unpair.2)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : Rule, ProbLaw P ∧ Causal P ∧ PrivateWith P (fun p ↦ p + δ) ∧
      ∀ A : Set ℕ, A.Nonempty → ∀ x, Valid A x → (P x).real (Success A x) = 1 := by
  classical
  obtain ⟨k,hk⟩ := exists_nat_gt (1/δ)
  let m := k+1
  have pos : 0 < (m:ℝ) := by dsimp [m]; positivity
  have inv : (m:ℝ)⁻¹ ≤ δ := by
    apply (inv_le_iff_one_le_mul₀ pos).mpr
    have := (div_lt_iff₀ hδ).mp hk
    dsimp [m]; push_cast; nlinarith
  let Q (x : Input) (r : Fin m) := ν.map (release r.val x)
  have probQ (x : Input) (r : Fin m) : IsProbabilityMeasure (Q x r) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_release x r.val).aemeasurable).mpr inferInstance
  let P (x : Input) : Measure Output := ((m : ℝ≥0∞)⁻¹) • ∑ r, Q x r
  have law : ProbLaw P := by
    intro x
    let _ := probQ x
    constructor
    simp [P,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul,m]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have mass (x : Input) (E : Set Output) :
      (P x).real E = (m:ℝ)⁻¹ * ∑ r, (Q x r).real E := by
    let _ := probQ x
    simp [P,measureReal_def,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul,ENNReal.toReal_sum]
  refine ⟨P,law,?_,?_,?_⟩
  · intro x y t hxy E hE hpre
    rw [mass,mass]; congr 1; apply Finset.sum_congr rfl; intro r _
    simp only [Q,map_measureReal_apply (measurable_release _ _) hE]
    congr 1; ext h
    apply hpre; intro j hj
    by_cases hle : r.val ≤ j
    · simp [release,hle,hxy r.val (lt_of_le_of_lt hle hj)]
    · simp [release,hle]
  · intro x y h E hE
    obtain ⟨d,_,hd⟩ := h
    have single (r : Fin m) : (Q x r).real E ≤ (Q y r).real E + (if r.val=d then 1 else 0) := by
      by_cases eq : r.val=d
      · have := probQ x r; have := probQ y r
        rw [ite_eq_left eq]
        linarith [measureReal_le_one (μ:=Q x r) (s:=E), measureReal_nonneg (μ:=Q y r) (s:=E)]
      · have same : release r.val x = release r.val y := by
          funext h t; simp only [release, hd r.val eq]
        simp [Q,same,eq]
    have diff := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin m))) => single r)
    rw [Finset.sum_add_distrib] at diff
    have one : (∑ r : Fin m, if r.val=d then (1:ℝ) else 0) ≤ 1 := by
      by_cases lt : d < m
      · let j : Fin m := ⟨d,lt⟩
        change (∑ r : Fin m, if r.val = j.val then (1:ℝ) else 0) ≤ 1
        simp [Fin.val_inj]
      · have no (r : Fin m) : r.val ≠ d := by omega
        simp [no]
    rw [mass,mass]
    have h' := mul_le_mul_of_nonneg_left (diff.trans (add_le_add_right one _)) (inv_nonneg.mpr pos.le)
    linarith
  · intro A _ x valid
    have good (r : Fin m) : (Q x r).real (Success A x) = 1 := by
      have hcol : col (x r.val) ∈ A := by
        change x r.val ∈ Language A
        rw [← valid]; exact ⟨r.val,rfl⟩
      have ev : ∀ᵐ h ∂ν, release r.val x h ∈ Success A x := by
        filter_upwards [fresh x] with h hh
        obtain ⟨N,hN⟩ := hh
        refine ⟨max r.val N,fun t ht => ?_⟩
        have le := le_trans (le_max_left _ _) ht
        refine ⟨by simpa [release,le,col] using hcol, fun i hi eq => ?_⟩
        apply hN t (le_trans (le_max_right _ _) ht) i hi
        simpa [release,le] using congrArg (fun z : ℕ => z.unpair.2) eq
      have hprob := (mem_ae_iff_prob_eq_one ((measurable_success A x).preimage (measurable_release x r.val))).mp ev
      change (ν.map (release r.val x)).real (Success A x) = 1
      rw [map_measureReal_apply (measurable_release _ _) (measurable_success A x), measureReal_def,hprob]
      simp
    rw [mass]; simp [good,Fintype.card_fin,ne_of_gt pos]

end UncountableGeneration
