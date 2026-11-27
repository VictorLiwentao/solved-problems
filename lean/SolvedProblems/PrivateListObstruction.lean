module

public import SolvedProblems.PrivateListVariable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace PrivateList

open MeasureTheory Set
open scoped Classical

/-- Threshold inequalities allow either orientation of the two neighboring rank
cells, since complementing every event reverses the pattern. -/
theorem orientedPacking {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Fin N → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (E : Fin N → Set Ω) (me : ∀ j, MeasurableSet (E j))
    {δ γ τ l h : ℝ} (hδ : 0 ≤ δ) (hδγ : δ < 2*γ) (hτ : 0 ≤ τ)
    (lr : 0 ≤ l ∧ l ≤ 1) (hr : 0 ≤ h ∧ h ≤ 1) (gap : 2*γ+2*τ ≤ |h-l|)
    (priv : ∀ i j, MeasureDominates 2 δ (P i) (P j))
    (below : ∀ i j, j < i → |(P i).real (E j) - l| ≤ τ)
    (above : ∀ i j, i < j → |(P i).real (E j) - h| ≤ τ)
    (d : ℕ) (hN : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 6 := by
  have nonempty : 0 < N := by
    have : 1 < 2^(d+1) := Nat.one_lt_two_pow (by omega); omega
  let i₀ : Fin N := ⟨0,nonempty⟩
  rw [show (6:ℝ) = 2*(2+1) by norm_num]
  by_cases dir : l ≤ h
  · rw [abs_of_nonneg (sub_nonneg.mpr dir)] at gap
    apply measurePacking (P i₀) P E me (c := (l+h)/2) (by norm_num) hδ hδγ
      (by linarith [lr.1]) (by linarith [hr.2]) (priv i₀) _ _ d hN
    · intro i j lt
      linarith [(abs_le.mp (below i j lt)).2]
    · intro i j lt
      linarith [(abs_le.mp (above i j lt)).1]
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge dir))] at gap
    apply measurePacking (P i₀) P (fun j => (E j)ᶜ) (fun j => (me j).compl)
      (c := 1-(l+h)/2) (by norm_num) hδ hδγ (by linarith [lr.2])
      (by linarith [hr.1]) (priv i₀) _ _ d hN
    · intro i j lt
      rw [probReal_compl_eq_one_sub (me _)]
      linarith [(abs_le.mp (below i j lt)).1]
    · intro i j lt
      rw [probReal_compl_eq_one_sub (me _)]
      linarith [(abs_le.mp (above i j lt)).2]

theorem horizontal_bound {k m Ω N L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ δ γ} (hom : HomogeneousOn A T X Y v τ) (priv : Private A 2 δ)
    (range : ∀ i y, 0 ≤ v i y ∧ v i y ≤ 1) (room : m+N+2 ≤ L)
    (hδ : 0 ≤ δ) (hδγ : δ < 2*γ) (hτ : 0 ≤ τ)
    (j : Fin m) (z : Fin (m+1)) (y : Label k)
    (jump : 2*γ+2*τ ≤ |v (j.succ,z) y - v (j.castSucc,z) y|)
    (d : ℕ) (hN : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 6 := by
  have size : m+1 ≤ L := by omega
  let b := holding size z
  let coord := spare size z
  let s (i : Fin N) := place T (X ∘ varying room j i) (Y ∘ b)
  let P (i : Fin N) := A.law (s i)
  have inst (i) : IsProbabilityMeasure (P i) := A.normalized _
  let E (i : Fin N) := {ω | y ∉ A.predict ω (X (sweep room j i),Y coord)}
  apply orientedPacking P E (fun i => A.measurable _ _) hδ hδγ hτ (range _ _) (range _ _) jump _ _ _ d hN
  · intro i u; exact priv _ _ (sweep_neighbor T room j X (Y ∘ b) i u)
  · intro i u lt
    exact local_rank hom (varying_mono room j i) (holding_mono size z) (j.castSucc,z) _ _ (varying_left room j lt) (holding_rank size z) y
  · intro i u lt
    exact local_rank hom (varying_mono room j i) (holding_mono size z) (j.succ,z) _ _ (varying_right room j lt) (holding_rank size z) y

end PrivateList
