module

public import SolvedProblems.PrivateWitnessIID
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

public section
namespace PrivateWitness
open scoped NNReal ENNReal

/-- For any support atom, privacy compares its output probability to the error
when one of the data points is replaced by that same atom. -/
private theorem atom_cost {G : Rule} {k : ℝ≥0} (priv : Private G k) (p : Law)
    {x : Nat} (pos : x ∈ p.support) (n : Nat) :
    output G p {x} (n+1) ≤ ((k:ℝ≥0∞)*(p x)⁻¹) * error G p (n+1) := by
  let f := fun h => mass (G h) {x}
  let loss := fun h => mass (G h) {y | y ∉ p.support ∨ y ∈ h}
  have hterm : iid p f n [x] ≤ iid p loss n [x] := by
    apply iid_context
    intro u
    apply mass_mono
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Or.inr (by simp)
  have finite : p x ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top (p.total ▸ ENNReal.one_ne_top) x
  have one : p x * iid p loss n [x] ≤ error G p (n+1) :=
    ENNReal.le_tsum (f := fun y => p y*iid p loss n [y]) x
  have div : iid p loss n [x] ≤ (p x)⁻¹*error G p (n+1) := by
    calc
      _ = (p x)⁻¹*(p x*iid p loss n [x]) := by rw [← mul_assoc,ENNReal.inv_mul_cancel pos finite,one_mul]
      _ ≤ _ := mul_le_mul_right one _
  calc
    _ ≤ ∑' y, p y * ((k:ℝ≥0∞)*iid p f n [x]) :=
      ENNReal.tsum_le_tsum (fun y => mul_le_mul_right (iid_private priv p {x} n y x []) _)
    _ = (k:ℝ≥0∞)*iid p f n [x] := by rw [ENNReal.tsum_mul_right,p.total,one_mul]
    _ ≤ (k:ℝ≥0∞)*((p x)⁻¹*error G p (n+1)) := mul_le_mul_right (hterm.trans div) _
    _ = _ := (mul_assoc ..).symm

private theorem exp_atom {G : Rule} {k : ℝ≥0} (priv : Private G k) (p : Law)
    (risk : Exponential (error G p)) (x : Nat) (hx : x ∈ p.support) :
    Exponential (output G p {x}) := by
  obtain ⟨c,r,hr,H⟩ := risk
  let d := (k:ℝ≥0∞)*(p x)⁻¹
  have df : d ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.mpr hx)
  refine ⟨1+d.toNNReal*c,r,hr,fun n => ?_⟩
  cases n with
  | zero =>
    simp only [ENNReal.coe_add,ENNReal.coe_one,ENNReal.coe_mul,pow_zero,mul_one]
    exact (mass_le_one _ _).trans le_self_add
  | succ n =>
    have h := (atom_cost priv p hx n).trans (mul_le_mul_right (H (n+1)) d)
    rw [← mul_assoc] at h
    simp only [ENNReal.coe_add,ENNReal.coe_one,ENNReal.coe_mul,ENNReal.coe_toNNReal df]
    exact h.trans (mul_le_mul_left le_add_self _)

theorem exp_finite {G : Rule} {k : ℝ≥0} (priv : Private G k) (p : Law)
    (risk : Exponential (error G p)) {F : Set Nat} (finite : F.Finite) (sub : F ⊆ p.support) :
    Exponential (output G p F) := by
  classical
  induction F, finite using Set.Finite.induction_on with
  | empty => exact exp_empty _ _
  | @insert x s _ hs ih =>
    rw [Set.insert_eq]
    exact exp_union (exp_atom priv _ risk _ (sub (by simp)))
      (ih (fun _ h => sub (Set.mem_insert_of_mem _ h)))

theorem exp_outside {G : Rule} {k : ℝ≥0} (priv : Private G k) (p : Law)
    (risk : Exponential (error G p)) (L : Set Nat) (finite : (p.support \ L).Finite) :
    Exponential (output G p Lᶜ) := by
  have outside : Exponential (output G p p.supportᶜ) := by
    apply exponential_mono _ risk
    intro n
    apply iid_mono
    exact fun h => mass_mono _ (fun _ hx => Or.inl hx)
  apply subevent _ (exp_union outside (exp_finite priv p risk finite (fun _ h => h.1)))
  intro x hx
  by_cases pos : x ∈ p.support
  · exact Or.inr ⟨pos,hx⟩
  · exact Or.inl pos

theorem not_exp_univ (G : Rule) (p : Law) : ¬ Exponential (output G p Set.univ) := by
  rintro ⟨c,r,hr,H⟩
  have limit := Filter.Tendsto.const_mul (c:ℝ)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (r:ℝ) from r.property)
      (show (r:ℝ) < 1 by exact_mod_cast hr))
  rw [mul_zero] at limit
  obtain ⟨n,hn⟩ := (limit.eventually_lt_const (show (0:ℝ) < 1 by norm_num)).exists
  have h : (1:ℝ≥0∞) ≤ (c:ℝ≥0∞)*(r:ℝ≥0∞)^n := by simpa [output,iid_const] using H n
  have le : (1:ℝ) ≤ (c:ℝ)*(r:ℝ)^n := by exact_mod_cast h
  linarith

end PrivateWitness
