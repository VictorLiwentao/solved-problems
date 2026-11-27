module

public import SolvedProblems.PrivateListMarginals
public import SolvedProblems.PrivateListObstruction
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace PrivateList

open MeasureTheory
open scoped Classical

/-- A two-axis realizable template with balanced label counts precludes even a
private improper empirical list learner at the given fixed accuracy. -/
theorem template_impossible {k m Ω} [MeasurableSpace Ω] (T : Template k m) (hm : 0 < m)
    (balanced : ∀ y, m ≤ 2*(k+1)*(Finset.univ.filter fun i => T.label i = y).card)
    (fits : ∀ a b : Fin m → ℕ, StrictMono a → StrictMono b → Consistent (place T a b))
    (A : Rule k m Ω) {δ : ℝ} (hδ : 0 ≤ δ) (small : δ ≤ 1/(1000*(k+1:ℝ)*m))
    (priv : Private A 2 δ) : ¬Empirical A (1/(200*(k+1:ℝ)^2)) := by
  intro emp
  let D := 1000*(k+1)*m
  let τ : ℝ := 1/D
  let γ : ℝ := 5*τ
  have hD : 0 < D := by dsimp [D]; positivity
  have τp : 0 < τ := by dsimp [τ]; positivity
  have sm : δ ≤ τ := by simpa [τ,D] using small
  have margin : δ < 2*γ := by dsimp [γ]; linarith
  have apos : 0 < γ-δ/2 := by linarith
  obtain ⟨d,hd⟩ := exists_nat_gt (6/(γ-δ/2)^2)
  let N : ℕ := 2^(d+1)
  let L := 2*m + N + 4
  have bigN : m+N+2 ≤ L := by change _ ≤ 2*m+N+4;omega
  have room : 2*m+1 ≤ L := by
    change 2*m+1 ≤ 2*m+N+4
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _
  obtain ⟨X,Y,v,range,huniform⟩ := homogeneousRanks A T L D hD
  have hom : HomogeneousOn A T X Y v τ := huniform
  let s := place T (X ∘ spaced room) (Y ∘ spaced room)
  have inc : StrictMono (@spaced m L room) := by intro i j h; have : i.val < j.val := h; change 2*i.val+1 < 2*j.val+1; omega
  have hs : Consistent s := fits _ _ (X.strictMono.comp inc) (Y.strictMono.comp inc)
  let i₀ : Fin m := ⟨0,hm⟩
  obtain ⟨y,high⟩ := high_omission A s (s i₀).1
  obtain ⟨i,lab,low⟩ := low_omission A hm hs y (balanced y) emp
  let cell (i : Fin m) : Cell m := ((T.xRank i).succ,(T.yRank i).succ)
  have high' : omission A s (s i₀).1 y ≤ 2*(v (cell i₀) y+τ)+δ := (training_cells hom priv room i₀ y).2
  have low' : v (cell i) y ≤ 2*omission A s (s i).1 y+δ+τ := (training_cells hom priv room i y).1
  have eq : (m:ℝ)*τ = (1/(k+1:ℝ))/1000 := by
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    dsimp [τ,D]; push_cast; field_simp
  have mi : (1:ℝ) ≤ m := by exact_mod_cast hm
  have smallτ : τ ≤ m*τ := le_mul_of_one_le_left τp.le mi
  have gap : 4*(m:ℝ)*(2*γ+2*τ) < v (cell i₀) y - v (cell i) y := by
    dsimp [γ]
    have pos : 0 < (1/(k+1:ℝ)) := by positivity
    rw [show (1:ℝ)/(100*(k+1)) = (1/(k+1:ℝ))/100 by rw [mul_comm, div_div]] at low
    nlinarith only [high,low,high',low',smallτ,sm,eq,pos]
  have bound : (d:ℝ)*(γ-δ/2)^2 ≤ 6 := by
    obtain jump | jump := grid_jump (fun t => v t y) (e := 2*γ+2*τ)
      (by dsimp [γ]; positivity) _ _ gap
    · obtain ⟨j,z,hj⟩ := jump
      exact horizontal_bound hom priv range bigN hδ margin τp.le j z y hj d (Nat.sub_le ..)
    · obtain ⟨j,z,hj⟩ := jump
      exact horizontal_bound (swapped_homogeneous hom) (swapped_private priv) (fun t => range t.swap)
        bigN hδ margin τp.le j z y hj d (Nat.sub_le ..)
  exact (not_lt.mpr bound) ((div_lt_iff₀ (sq_pos_of_pos apos)).mp hd)

end PrivateList
