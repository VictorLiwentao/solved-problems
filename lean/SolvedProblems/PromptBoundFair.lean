module

public import SolvedProblems.PromptBoundProbability
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.NormNum

public section

open MeasureTheory Set
open scoped ENNReal

namespace PromptBound

private theorem coin_mem (n : ℕ) (u : List Bool) : u ∈ coinWords n ↔ u.length = n := by
  induction n generalizing u with
  | zero => simp [coinWords]
  | succ n ih =>
    rw [coinWords,List.mem_flatMap]
    cases u with
    | nil => simp
    | cons b bs => cases b <;> simp [ih]

private theorem coin_nodup (n : ℕ) : (coinWords n).Nodup := by
  induction n with
  | zero => simp [coinWords]
  | succ n ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun x _ ↦ by simp,ih.imp ?_⟩
    intro a b h
    apply List.disjoint_left.mpr
    intro x hx hy
    simp at hx hy
    grind

private theorem coin_count (n : ℕ) : (coinWords n).length = 2^n := by
  induction n with
  | zero => simp [coinWords]
  | succ n ih =>
    simp [coinWords,List.length_flatMap,ih,pow_succ,Nat.mul_comm]

private noncomputable def bitLaw : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac false + Measure.dirac true)

private instance : IsProbabilityMeasure bitLaw := by
  constructor
  simp [bitLaw,smul_eq_mul]
  rw [← two_mul,ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

private theorem bit_mass (b : Bool) : bitLaw {b} = (2 : ℝ≥0∞)⁻¹ := by
  cases b <;> simp [bitLaw,Measure.dirac_apply' _ (measurableSet_singleton _),smul_eq_mul]

private noncomputable def tapeLaw : Measure Tape := Measure.infinitePi fun _ : ℕ => bitLaw

private instance : IsProbabilityMeasure tapeLaw := by unfold tapeLaw; infer_instance

private theorem tape_atom (n : ℕ) (u : List Bool) (hu : u.length = n) :
    tapeLaw ((fun x : Tape => initial x n) ⁻¹' {u}) = ((2 : ℝ≥0∞)⁻¹)^n := by
  have eq : ((fun x : Tape => initial x n) ⁻¹' {u}) =
      Set.pi (Finset.range n : Set ℕ) (fun i => {u.getD i false}) := by
    ext x
    change initial x n = u ↔ ∀ i ∈ (Finset.range n : Set ℕ), x i = u.getD i false
    constructor
    · rintro rfl i hi
      have hi' : i < n := Finset.mem_range.mp hi
      simp [initial,List.getD_eq_getElem?_getD,hi']
    · intro h
      apply List.ext_getElem
      · simp [initial,hu]
      · intro i _ hi
        have hin : i < n := hu ▸ hi
        simpa [initial,List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using
          h i (Finset.mem_range.mpr hin)
  rw [eq,tapeLaw,Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton _)]
  simp [bit_mass]

/-- The infinite product of unbiased Boolean laws has exactly the finite uniform
prefix marginals used by the randomized generator. -/
theorem fairLaw_exists : Nonempty FairLaw := by
  classical
  refine ⟨⟨tapeLaw,inferInstance,?_⟩⟩
  intro n f
  let V := ((coinWords n).filter f).toFinset
  have same : {w : Tape | f (initial w n) = true} = (fun w : Tape => initial w n) ⁻¹' (V : Set _) := by
    ext w
    simp [V,coin_mem,initial]
  rw [same,← sum_measureReal_preimage_singleton V (fun u _ ↦ measurable_tape_test n (fun v ↦ v = u))]
  calc
    _ = ∑ _u ∈ V, ((2 : ℝ)⁻¹)^n := by
      apply Finset.sum_congr rfl
      intro u hu
      have len : u.length = n := (coin_mem n u).mp ((List.mem_filter.mp
        (List.mem_toFinset.mp hu)).1)
      rw [measureReal_def,tape_atom n u len]
      simp
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,coin_count, List.toFinset_card_of_nodup ((coin_nodup n).filter f)]
      simp [div_eq_mul_inv]

end PromptBound
