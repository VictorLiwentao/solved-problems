module

public import SolvedProblems.PrivateListClipping
public import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrivateList

open scoped Classical

noncomputable def query {X : Type} (E : Finset X) : Option X → ℝ
  | none => 1
  | some x => if x ∈ E then 1 else 0

noncomputable def weighted {X : Type} (p : X → ℝ) : Option X → ℝ
  | none => 1
  | some x => p x

noncomputable def rowVector {X : Type} (b : ℝ) (g : X → ℝ) : Option X → ℝ
  | none => b
  | some x => g x

theorem dot_query {X : Type} [Fintype X] (p g : X → ℝ) (b : ℝ) (E : Finset X) :
    dot (weighted p) (rowVector b g) (query E) = b + mass (fun x => p x * g x) E := by
  classical
  rw [dot, Fintype.sum_option]
  simp only [weighted,rowVector,query,one_mul,mul_one]
  congr 1
  simp [mass, mul_ite]

theorem square_query {X : Type} [Fintype X] (p : X → ℝ) (E : Finset X) :
    dot (weighted p) (query E) (query E) = 1 + mass p E := by
  classical
  rw [dot, Fintype.sum_option]
  simp only [weighted,query,mul_one]
  congr 1
  simp [mass, mul_ite]

theorem square_row {X : Type} [Fintype X] (p g : X → ℝ) (b : ℝ) :
    dot (weighted p) (rowVector b g) (rowVector b g) = b*b + dot p g g := by
  rw [dot,Fintype.sum_option]
  simp only [weighted,rowVector,one_mul]
  rfl

/-- A finite collection of events inducing a staggered threshold pattern must be
short when the additive privacy loss is strictly less than twice the margin.
Only one-sided domination by one common reference law is needed. -/
theorem finitePacking {X : Type} [Fintype X] {N : ℕ} (p : X → ℝ) (hp : Law p)
    (P : Fin N → X → ℝ) (law : ∀ i, Law (P i)) (E : Fin N → Finset X)
    {scale δ γ c : ℝ} (hscale : 0 ≤ scale) (hδ : 0 ≤ δ) (hδγ : δ < 2*γ)
    (hc : γ ≤ c) (hc' : c ≤ 1-γ)
    (dp : ∀ i, Domination scale δ p (P i))
    (below : ∀ i j, j < i → mass (P i) (E j) ≤ c-γ)
    (above : ∀ i j, i < j → c+γ ≤ mass (P i) (E j))
    (d : ℕ) (hn : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 2*(scale+1) := by
  let b := -c+δ/2
  let g i := density scale p (P i)
  have sqb : b*b ≤ 1 := by
    have hb : -1 ≤ b := by dsimp [b]; linarith
    have hb' : b ≤ 1 := by dsimp [b]; linarith
    nlinarith [mul_nonneg (show 0 ≤ 1+b by linarith) (show 0 ≤ 1-b by linarith)]
  have eval (i j) : dot (weighted p) (rowVector b (g i)) (query (E j)) =
      b + mass (clip scale p (P i)) (E j) := by
    rw [dot_query]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    exact (density_props hp (law i) hscale x).1
  apply thresholdPerceptron (weighted p) (by rintro (_|x) ; exacts [zero_le_one,hp.1 x])
    (fun j => query (E j)) (fun i => rowVector b (g i)) (a := γ-δ/2) (D := scale+1)
    (by linarith) _ _ _ _ d hn
  · intro j; rw [square_query]; linarith [mass_le_one hp (E j)]
  · intro i; rw [square_row]; linarith [density_norm hp (law i) hscale]
  · intro i j hj; rw [eval]; dsimp [b]
    linarith [(clip_event (dp i) (E j)).2, below i j hj]
  · intro i j hj; rw [eval]; dsimp [b]
    linarith [(clip_event (dp i) (E j)).1, above i j hj]

end PrivateList
