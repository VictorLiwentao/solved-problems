module

public import SolvedProblems.ReluInputLaws
public import SolvedProblems.ReluCircuitCompression

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ReluMoments

/-- For any two scalar real-input feedforward networks with at most h hidden
gates each, the draft's two displayed lists of ordinary moments both determine
the realized function everywhere, separately for their respective laws. -/
theorem univariate_laws {n m h : ℕ} (hn : n ≤ h) (hm : m ≤ h)
    (b : Circuit n) (c : Circuit m) (a : GateAffine n) (a' : GateAffine m) :
    ((∀ k ≤ laplaceDegree h, (∫ x, x^k*b.out a x ∂standardLaplace) =
      ∫ x, x^k*c.out a' x ∂standardLaplace) ↔ b.out a = c.out a') ∧
    ((∀ k ≤ gaussianDegree h, (∫ x, x^k*b.out a x ∂(gaussianReal 0 1)) =
      ∫ x, x^k*c.out a' x ∂(gaussianReal 0 1)) ↔ b.out a = c.out a') := by
  let : (gaussianReal 0 1).IsOpenPosMeasure := gaussian_open _ one_ne_zero
  exact ⟨circuit_identification b c a a' _ _ (display_degrees hn hm).1 (fun k _ => laplace_envelope k),
    circuit_identification b c a a' _ _ (display_degrees hn hm).2 (fun k _ => gaussian_envelope _ _ k)⟩

/-- Each law separately admits almost every fixed list of 2P+1 polynomial
tests from the corresponding displayed degree range, uniformly in all
parameters and with pointwise agreement on the entire real line. -/
theorem univariate_compressed_laws {p h : ℕ} (b : IndexedCircuit p h) (a : IndexedAffine h p) :
    (∀ᵐ A : Measurements (2*p+1) (laplaceDegree h+1) ∂volume, ∀ θ η,
      polynomialObservations b a standardLaplace (laplaceDegree h) A θ =
        polynomialObservations b a standardLaplace (laplaceDegree h) A η ↔
      (b.instantiate θ).out (a.instantiate θ) = (b.instantiate η).out (a.instantiate η)) ∧
    (∀ᵐ A : Measurements (2*p+1) (gaussianDegree h+1) ∂volume, ∀ θ η,
      polynomialObservations b a (gaussianReal 0 1) (gaussianDegree h) A θ =
        polynomialObservations b a (gaussianReal 0 1) (gaussianDegree h) A η ↔
      (b.instantiate θ).out (a.instantiate θ) = (b.instantiate η).out (a.instantiate η)) := by
  let : (gaussianReal 0 1).IsOpenPosMeasure := gaussian_open _ one_ne_zero
  have hdeg := display_degrees (n:=h) (m:=h) (h:=h) le_rfl le_rfl
  exact ⟨circuit_compression b a _ _ hdeg.1 (fun k _ => laplace_envelope k),
    circuit_compression b a _ _ hdeg.2 (fun k _ => gaussian_envelope _ _ k)⟩

end ReluMoments
