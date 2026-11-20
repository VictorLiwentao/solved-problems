module

public import SolvedProblems.UncountableGenerationAveraging
public import SolvedProblems.UncountableGenerationCompletion
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

open MeasureTheory Set Function Filter
open scoped ENNReal

namespace UncountableGeneration

/-- On a fixed selection, eventual membership implies membership at every sufficiently
late horizon. Subadditivity bounds the latter by the sum over the selected columns. -/
theorem members_le_liminf (P : Rule) (hp : ProbLaw P) {m : ℕ → ℕ} (z : Choices m) :
    (P (sparse z)) (Members (selected z)) ≤
      liminf (fun t ↦ ∑' i, hitProb P t i z) atTop := by
  let μ := P (sparse z)
  let := hp (sparse z)
  let E (N : ℕ) := {u : Output | ∀ t ≥ N, col (u t) ∈ selected z}
  have he : Members (selected z) = ⋃ N, E N := by ext u; simp [E, Members]
  have hm : Monotone E := fun _ _ hab _ h t ht ↦ h t (hab.trans ht)
  rw [he, hm.measure_iUnion]
  refine iSup_le fun N ↦ le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop N] with t ht
  have hs : E N ⊆ ⋃ i, hit t (poolColumn i (z i)) := by
    intro u hu
    obtain ⟨i, hi⟩ := hu t ht
    exact mem_iUnion.mpr ⟨i, hi.symm⟩
  calc
    _ ≤ μ (⋃ i, hit t (poolColumn i (z i))) := measure_mono hs
    _ ≤ ∑' i, μ (hit t (poolColumn i (z i))) := measure_iUnion_le _
    _ = _ := tsum_congr fun i ↦ (ofReal_measureReal (measure_ne_top (P (sparse z)) _)).symm

/-- A uniformly vanishing event-probability modulus forces zero worst-case success
for unions of complete columns, even on fixed injective enumerations. -/
theorem vanishing_modulus_zero {P : Rule} (hp : ProbLaw P) (hc : Causal P)
    {ω : ℝ → ℝ} (hw : Vanishes ω) (hpriv : PrivateWith P ω) : ZeroUtility P := by
  classical
  intro η hη
  let b := η/4
  have hb : 0 < b := by dsimp [b]; linarith
  let e (i : ℕ) := b/2/2^i
  have he (i : ℕ) : 0 < e i := by dsimp [e]; positivity
  choose m hm using fun i ↦ pool_size ω hw (e i) (he i)
  let G (t : ℕ) (z : Choices m) := ∑' i, hitProb P t i z
  have hmeas t : Measurable (G t) := Measurable.tsum fun i ↦ hitProb_measurable hc t i
  have hmean (t : ℕ) : (∫⁻ z, G t z ∂choiceLaw m) ≤ ENNReal.ofReal b := by
    change (∫⁻ z, ∑' i, hitProb P t i z ∂choiceLaw m) ≤ _
    rw [lintegral_tsum fun i ↦ (hitProb_measurable hc t i).aemeasurable]
    calc
      _ ≤ ∑' i, ENNReal.ofReal (e i) := ENNReal.tsum_le_tsum fun i ↦
        mean_hit_le hc (pool_sum hp hpriv hm) t i
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ (he i).le) (summable_geometric_two' b)]
        exact congrArg ENNReal.ofReal (tsum_geometric_two' b)
  have avg : (∫⁻ z, liminf (fun t ↦ G t z) atTop ∂choiceLaw m) ≤ ENNReal.ofReal b :=
    (lintegral_liminf_le hmeas).trans (liminf_le_of_frequently_le' (Eventually.of_forall hmean).frequently)
  obtain ⟨z, hz⟩ : ∃ z : Choices m, liminf (fun t ↦ G t z) atTop < ENNReal.ofReal (b+b) := by
    by_contra! h
    have hbig := lintegral_mono (μ := choiceLaw m) h
    rw [lintegral_const, measure_univ, mul_one] at hbig
    have hh : ENNReal.ofReal b < ENNReal.ofReal (b+b) :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb.le |>.mpr (by linarith)
    exact hh.not_ge (hbig.trans avg)
  have hx (i : ℕ) : col (sparse z i) ∈ selected z := by
    change col (Nat.pair (poolColumn i (z i)) 0) ∈ selected z
    rw [col, Nat.unpair_pair]
    exact mem_range_self i
  have hz' : (P (sparse z)).real (Members (selected z)) < b+b :=
    ENNReal.toReal_lt_of_lt_ofReal ((members_le_liminf P hp z).trans_lt hz)
  obtain ⟨y, hyj, hy, hyb⟩ := extend_members hp hc hw hpriv (selected z) (sparse z)
    hx (sparse_injective z) hb
  refine ⟨selected z, ⟨_, hx 0⟩, y, hyj, hy, ?_⟩
  dsimp [b] at *
  linarith

end UncountableGeneration
