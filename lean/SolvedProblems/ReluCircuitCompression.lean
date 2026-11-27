module

public import SolvedProblems.ReluMomentMap
public import SolvedProblems.ReluParamCircuit
public import SolvedProblems.ReluCircuitMoments

@[expose] public section

open MeasureTheory
open scoped Topology

namespace ReluMoments

noncomputable def polynomialObservations {p n m : ℕ} (b : IndexedCircuit p n) (a : IndexedAffine n p)
    (μ : Measure ℝ) (D : ℕ) (A : Measurements m (D+1)) (θ : Vector p) : Vector m :=
  fun i => ∫ x, (∑ k : Fin (D+1), A (i,k)*x^k.val) * (b.instantiate θ).out (a.instantiate θ) x ∂μ

/-- Almost every fixed list of 2P+1 polynomial measurements identifies every
realized function of a shared, P-parameter architecture on the real line. -/
theorem circuit_compression {p n : ℕ} (b : IndexedCircuit p n) (a : IndexedAffine n p)
    (μ : Measure ℝ) [μ.IsOpenPosMeasure] (D : ℕ) (hD : 2*(2^n+2^n+2^n*2^n) ≤ D)
    (hi : ∀ k ≤ D, Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ) :
    ∀ᵐ A : Measurements (2*p+1) (D+1) ∂volume, ∀ θ η,
      polynomialObservations b a μ D A θ = polynomialObservations b a μ D A η ↔
        (b.instantiate θ).out (a.instantiate θ) = (b.instantiate η).out (a.instantiate η) := by
  let e : ℝ → Vector 1 := fun x _ => x
  have he : Continuous e := continuous_pi fun _ => continuous_id
  let ν := μ.map e
  let t (k : Fin (D+1)) (z : Vector 1) := z 0 ^ k.val
  let f := a.makeExpr b.exprs
  have ht (k) : Continuous (t k) := (continuous_apply 0).pow _
  have hwt (k : Fin (D+1)) : Integrable (fun z => |t k z| * (1+‖z‖)) ν := by
    apply (integrable_map_measure ((ht k).abs.mul (continuous_const.add continuous_norm)).aestronglyMeasurable
      he.aemeasurable).mpr
    change Integrable (fun x : ℝ => |x^k.val| * (1+‖fun _ : Fin 1 => x‖)) μ
    simpa only [abs_pow,pi_norm_const,Real.norm_eq_abs] using hi k.val (by omega)
  have hc := network_compression (m:=2*p+1) (by omega) f ν t
    (fun k => (ht k).aestronglyMeasurable) hwt
  have hu (θ : Vector p) (k : Fin (D+1)) : moments f ν t θ k =
      ∫ x, x^k.val * (b.instantiate θ).out (a.instantiate θ) x ∂μ := by
    rw [moments,show ν = μ.map e from rfl,integral_map (f:=fun z => t k z * f.eval θ z) he.aemeasurable ((ht k).mul (f.continuous_input θ)).aestronglyMeasurable]
    simp only [e,t,f,b.eval_output]
  have hm (A : Measurements (2*p+1) (D+1)) (θ : Vector p) :
      measureVector A (moments f ν t θ) = polynomialObservations b a μ D A θ := by
    funext i
    rw [measurement_integral f ν t (fun k => (ht k).aestronglyMeasurable) hwt]
    have hw : Continuous (fun z => (∑ k, A (i,k) * t k z)*f.eval θ z) := by
      apply Continuous.mul _ (f.continuous_input θ)
      fun_prop (disch := solve_by_elim)
    rw [show ν = μ.map e from rfl,integral_map he.aemeasurable hw.aestronglyMeasurable]
    simp only [polynomialObservations,e,t,f,b.eval_output]
  filter_upwards [hc] with A hA
  intro θ η
  rw [←hm,←hm,hA]
  constructor
  · intro hh
    apply (circuit_identification _ _ _ _ μ D hD hi).mp
    intro k hk
    let i : Fin (D+1) := ⟨k,by omega⟩
    simpa only [hu] using congrFun hh i
  · intro hh
    funext k
    rw [hu,hu,hh]

end ReluMoments
