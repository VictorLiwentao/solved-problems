module

public import SolvedProblems.PrivateListDimensions
public import SolvedProblems.PrivateListEmpirical
public import SolvedProblems.PrivateListBalanced
public import SolvedProblems.PrivateListTransfer
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace PrivateList

open MeasureTheory

/-- The planar finite-support class answers the private list-learning question negatively.
Both list dimensions equal one. For each sample size `s`, approximate privacy at ε=1/10
and δ≤1/(1000(k+1)(s+1)) rules out the displayed fixed PAC accuracy and confidence,
even for improper outputs and even just on uniform realizable finite populations. -/
theorem separation (k : ℕ) (hk : 2 ≤ k) :
    (∀ n, (LittlestoneDepth k n ↔ n ≤ 1) ∧ (MonotoneLength k n ↔ n ≤ 1)) ∧
    ∀ (s : ℕ) (Ω : Type) [MeasurableSpace Ω] (A : Rule k s Ω) (δ : ℝ),
      0 ≤ δ → δ ≤ 1/(1000*(k+1:ℝ)*(s+1:ℝ)) → Private A (Real.exp (1/10)) δ →
      ¬PopulationPAC A (1/(800*(k+1:ℝ)^2)) (1/(800*(k+1:ℝ)^2)) := by
  refine ⟨dimensionOne k hk, ?_⟩
  intro s Ω _ A δ hδ small priv pac
  let q := k+1
  let n := 400*q*(s+1)^2
  let m := q*n
  have hp : 0 < m := by dsimp [m,n,q]; positivity
  let : NeZero m := ⟨hp.ne'⟩
  have hm : (0:ℝ) < m := by exact_mod_cast hp
  have hq : (0:ℝ) < k+1 := by positivity
  have sp : (0:ℝ) < s+1 := by positivity
  have scale : Real.exp (1/10) ≤ 2 := (Real.exp_le_two_add_div_two_sub (x := 1/10) (by norm_num) (by norm_num)).trans (by norm_num)
  have pr : Private A 2 δ := fun t t' adj E hE => (priv t t' adj E hE).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right scale measureReal_nonneg) _)
  let B : Rule k m Ω := resample A
  have err : (s:ℝ)^2/m ≤ 1/(400*(k+1:ℝ)^2) := by
    apply (div_le_div_iff₀ hm (by positivity)).mpr
    dsimp [m,n,q];push_cast;nlinarith [sq_nonneg (s:ℝ),sq_nonneg (k:ℝ)]
  have dsmall : δ*((s:ℝ)/m) ≤ 1/(1000*(k+1:ℝ)*m) := by
    calc
      _ ≤ (1/(1000*(k+1:ℝ)*(s+1:ℝ)))*(s/m) := mul_le_mul_of_nonneg_right small (by positivity)
      _ ≤ _ := by field_simp; nlinarith
  let T := balancedTemplate k n
  have balanced (y) : m ≤ 2*(k+1)*(Finset.univ.filter fun i => T.label i=y).card := by
    rw [show (Finset.univ.filter fun i => T.label i=y).card = n from balanced_counts k n y]
    change (k+1)*n ≤ _
    calc _ ≤ 2*((k+1)*n) := Nat.le_mul_of_pos_left _ (by decide)
         _ = _ := by rw [Nat.mul_assoc]
  apply template_impossible T hp balanced (balanced_fits k n) B (mul_nonneg hδ (by positivity)) dsmall
    (resample_private A hδ pr)
  intro t fit
  have e := resample_empirical (m := m) A (by positivity) pac t fit
  apply e.trans
  apply mul_le_mul_of_nonneg_left _ hm.le
  have eq : 1/(800*(k+1:ℝ)^2)+1/(800*(k+1:ℝ)^2)+1/(400*(k+1:ℝ)^2) = 1/(200*(k+1:ℝ)^2) := by field_simp;ring
  rw [← eq];exact add_le_add_right err _

end PrivateList
