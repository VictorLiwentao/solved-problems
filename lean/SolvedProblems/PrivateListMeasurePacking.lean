module

public import SolvedProblems.PrivateListPacking
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace PrivateList

open MeasureTheory Set
open scoped Classical

def MeasureDominates {Ω : Type} [MeasurableSpace Ω] (scale δ : ℝ) (μ ν : Measure Ω) : Prop :=
  ∀ E : Set Ω, MeasurableSet E → ν.real E ≤ scale * μ.real E + δ

/-- Sharp-margin packing inequality on arbitrary measurable prediction spaces.
The finite quotient is the joint vector of answers to all N membership tests. -/
theorem measurePacking {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Fin N → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (E : Fin N → Set Ω) (me : ∀ j, MeasurableSet (E j))
    {scale δ γ c : ℝ} (hscale : 0 ≤ scale) (hδ : 0 ≤ δ) (hδγ : δ < 2*γ)
    (hc : γ ≤ c) (hc' : c ≤ 1-γ) (dp : ∀ i, MeasureDominates scale δ μ (P i))
    (below : ∀ i j, j < i → (P i).real (E j) ≤ c-γ)
    (above : ∀ i j, i < j → c+γ ≤ (P i).real (E j))
    (d : ℕ) (hn : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 2*(scale+1) := by
  classical
  let f (ω : Ω) (i : Fin N) : Bool := if ω ∈ E i then true else false
  have hf : Measurable f := Measurable.of_eval (fun i =>
    Measurable.ite (me i) measurable_const measurable_const)
  let atom (Q : Measure Ω) (a : Fin N → Bool) := Q.real (f ⁻¹' {a})
  have ma (Q : Measure Ω) [IsProbabilityMeasure Q] (s : Finset (Fin N → Bool)) :
      mass (atom Q) s = Q.real (f ⁻¹' (s : Set _)) :=
    sum_measureReal_preimage_singleton _ (fun a _ => hf (measurableSet_singleton a))
  have law (Q : Measure Ω) [IsProbabilityMeasure Q] : Law (atom Q) :=
    ⟨fun _ => measureReal_nonneg, by simpa [mass] using ma Q Finset.univ⟩
  let event (j : Fin N) := Finset.univ.filter fun a : Fin N → Bool => a j = true
  have ef (j) : f ⁻¹' (event j : Set _) = E j := by ext x; simp [event,f]
  apply finitePacking (atom μ) (law μ) (fun i => atom (P i)) (fun i => law (P i))
    event hscale hδ hδγ hc hc' _ _ _ d hn
  · intro i s
    rw [ma,ma]
    exact dp i _ (hf s.finite_toSet.measurableSet)
  · intro i j lt; rw [ma, ef]; exact below i j lt
  · intro i j lt; rw [ma, ef]; exact above i j lt

/-- At the endpoint δ=2γ, arbitrarily many distributions satisfy the threshold
constraints even with multiplicative privacy factor one. -/
theorem packingSharp (N : ℕ) {γ c : ℝ} (hγ : 0 ≤ γ) (hc : γ ≤ c) (hc' : c ≤ 1-γ) :
    ∃ P : Fin N → Option (Option (Fin N)) → ℝ, (∀ i, Law (P i)) ∧
      (∀ i j, Domination 1 (2*γ) (P i) (P j)) ∧
      ∃ E : Fin N → Finset (Option (Option (Fin N))),
        (∀ i j, j < i → mass (P i) (E j) = c-γ) ∧
        (∀ i j, i < j → mass (P i) (E j) = c+γ) := by
  classical
  let X := Option (Option (Fin N))
  let base : X → ℝ
    | none => c-γ
    | some none => 1-c-γ
    | some (some _) => 0
  let atom (i : Fin N) : X := some (some i)
  let P (i : Fin N) (x : X) := base x + if x = atom i then 2*γ else 0
  have bn (x) : 0 ≤ base x := by rcases x with _|(_|i) <;> dsimp [base] <;> linarith
  have total : (∑ x, base x) = 1-2*γ := by
    rw [Fintype.sum_option,Fintype.sum_option]; simp [base];ring
  have calcMass (i : Fin N) (s : Finset X) :
      mass (P i) s = mass base s + if atom i ∈ s then 2*γ else 0 := by
    unfold mass
    simp only [P,Finset.sum_add_distrib]
    exact congrArg (fun z => _ + z) (Finset.sum_ite_eq' _ _ _)
  have law (i) : Law (P i) := by
    constructor
    · intro x; unfold P; split <;> linarith [bn x]
    · rw [show (∑ x,P i x) = mass (P i) Finset.univ from rfl, calcMass, mass, total]
      simp
  let accept (j : Fin N) : X → Prop
    | none => True
    | some none => False
    | some (some i) => i < j
  let E (j) := Finset.univ.filter (accept j)
  have eb (j) : mass base (E j) = c-γ := by
    rw [mass,Finset.sum_filter,Fintype.sum_option,Fintype.sum_option]
    simp [base,accept]
  have pat (i j) : mass (P i) (E j) = c-γ + if i<j then 2*γ else 0 := by
    rw [calcMass,eb]
    simp [atom,E,accept]
  refine ⟨P,law,?_,E,?_,?_⟩
  · intro i j s
    simp only [calcMass,one_mul]
    split <;> split <;> linarith
  · intro i j h; simp [pat,not_lt.mpr h.le]
  · intro i j h; rw [pat,ite_eq_left h]; ring

end PrivateList
