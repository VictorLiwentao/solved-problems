module

public import SolvedProblems.ReluVectors
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open Set MeasureTheory MeasureTheory.Measure Module Filter
open scoped Topology ENNReal NNReal

namespace ReluMoments

/-- Reconstruct the missing column of a matrix killing `v` from all other columns;
the chart is used only where `v h ≠ 0`. -/
noncomputable def chart {j m : ℕ} (h : Fin (j+1)) (u : Vector (j+1) × Measurements m j) : Measurements m (j+1) :=
  fun ik => h.insertNth (α := fun _ => ℝ) (-(∑ k : Fin j, u.2 (ik.1,k) * u.1 (h.succAbove k)) / u.1 h)
    (fun k : Fin j => u.2 (ik.1,k)) ik.2

abbrev PairDomain (p m j : ℕ) := (Vector p × Vector p) × Measurements m j

def secants {p q m j : ℕ} (f : Vector p → Vector q) (u : PairDomain p m j) : Vector q × Measurements m j :=
  (f u.1.1 - f u.1.2, u.2)

theorem secants_locally {p q m j : ℕ} {f : Vector p → Vector q} (hf : LocallyLipschitz f) :
    LocallyLipschitz (secants (m:=m) (j:=j) f) := by
  have h₁ : LocallyLipschitz (fun u : PairDomain p m j => f u.1.1) := hf.comp (LipschitzWith.prod_fst.comp LipschitzWith.prod_fst).locallyLipschitz
  have h₂ : LocallyLipschitz (fun u : PairDomain p m j => f u.1.2) := hf.comp (LipschitzWith.prod_snd.comp LipschitzWith.prod_fst).locallyLipschitz
  exact (h₁.sub h₂).prodMk LipschitzWith.prod_snd.locallyLipschitz

theorem chart_smooth {j m : ℕ} (h : Fin (j+1)) (u : Vector (j+1) × Measurements m j) (hu : u.1 h ≠ 0) :
    DifferentiableAt ℝ (chart (m:=m) h) u := by
  apply differentiableAt_pi.mpr
  intro ⟨i,k⟩
  induction k using h.succAboveCases with
  | x =>
    simp only [chart, Fin.insertNth_apply_same]
    simp only [div_eq_mul_inv]
    apply DifferentiableAt.fun_mul
    · fun_prop
    · exact DifferentiableAt.fun_inv (by fun_prop) hu
  | p k =>
    simp only [chart, Fin.insertNth_apply_succAbove]
    fun_prop

/-- Matrices destroying a secant through this chart are a null set. The
parameter dimension is 2p + m⨉j, strictly below m⨉(j+1) when m > 2p. -/
theorem chart_null {p j m : ℕ} (hm : 2*p<m) (h : Fin (j+1))
    {f : Vector p → Vector (j+1)} (hf : LocallyLipschitz f) :
    volume (chart h '' (secants (m:=m) (j:=j) f '' {u | (f u.1.1 - f u.1.2) h ≠ 0})) = 0 := by
  let U : Set (PairDomain p m j) := {u | (f u.1.1-f u.1.2) h ≠ 0}
  let g := secants (m:=m) (j:=j) f
  have hs : DifferentiableOn ℝ (chart (m:=m) h) (g '' U) := by
    rintro _ ⟨u,hu,rfl⟩
    exact (chart_smooth h (g u) hu).differentiableWithinAt
  have hdim : dimH (g '' U) ≤ dimH (Set.univ : Set (PairDomain p m j)) := by
    apply (dimH_mono (Set.image_subset_range g U)).trans
    exact dimH_range_le_of_locally_lipschitzOn (secants_locally hf)
  have hd : finrank ℝ (PairDomain p m j) < Fintype.card (Fin m × Fin (j+1)) := by
    simp only [PairDomain, Vector, Measurements, Module.finrank_prod, Module.finrank_pi,
      Fintype.card_fin, Fintype.card_prod]
    nlinarith only [hm]
  rw [Real.dimH_univ_eq_finrank] at hdim
  rw [← hausdorffMeasure_pi_real]
  apply hausdorffMeasure_of_dimH_lt (d := Fintype.card (Fin m × Fin (j+1)))
  exact hs.dimH_image_le.trans_lt (hdim.trans_lt (by exact_mod_cast hd))

/-- Almost every matrix with more than 2p rows is injective on the entire image
of any locally Lipschitz p-parameter moment map, with no global boundedness or
smoothness assumption. -/
theorem compression {p j m : ℕ} (hm : 2*p<m) (f : Vector p → Vector j) (hf : LocallyLipschitz f) :
    ∀ᵐ A : Measurements m j ∂volume, ∀ x y, measureVector A (f x) = measureVector A (f y) → f x = f y := by
  classical
  cases j with
  | zero => exact Filter.Eventually.of_forall fun _ _ _ _ => funext (fun i => Fin.elim0 i)
  | succ j =>
    let bad (h : Fin (j+1)) := chart h '' (secants (m:=m) (j:=j) f '' {u | (f u.1.1-f u.1.2) h ≠ 0})
    have hz : volume (⋃ h, bad h) = 0 := measure_iUnion_null (fun h => chart_null hm h hf)
    rw [ae_iff]
    apply measure_mono_null _ hz
    intro A hA
    change ¬(∀ x y, measureVector A (f x) = measureVector A (f y) → f x = f y) at hA
    push Not at hA
    obtain ⟨x,y,he,hne⟩ := hA
    obtain ⟨h,hd⟩ : ∃ h, (f x-f y) h ≠ 0 := by
      by_contra! hzero
      apply hne
      ext i
      exact sub_eq_zero.mp (hzero i)
    let B : Measurements m j := fun ik => A (ik.1,h.succAbove ik.2)
    refine Set.mem_iUnion.mpr ⟨h, _, ⟨((x,y),B), hd, rfl⟩, ?_⟩
    ext ⟨i,k⟩
    induction k using h.succAboveCases with
    | x =>
      simp only [chart, Fin.insertNth_apply_same, secants, B, Pi.sub_apply]
      apply (div_eq_iff (show f x h - f y h ≠ 0 from hd)).mpr
      have hk : (∑ k, A (i,k) * (f x k - f y k)) = 0 := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (congrFun he i)
      rw [Fin.sum_univ_succAbove _ h] at hk
      linarith
    | p k => simp [chart,secants,B]

end ReluMoments
