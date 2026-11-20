module

public import SolvedProblems.SingletonDensityBlocks
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace SingletonDensity

attribute [local instance] Classical.propDecidable

private theorem endpoint (j : Nat) : start (j+1) = start j + j + 3 := rfl

private theorem start_increasing : StrictMono start := strictMono_nat_of_lt_succ fun j => by
  rw [endpoint]; omega

private theorem quadratic (j : Nat) : j*j ≤ 2*start j := by
  induction j with
  | zero => decide
  | succ j ih => rw [endpoint, Nat.succ_mul, Nat.mul_succ]; omega

private theorem insideBlock (n : Nat) : ∃ j, start j ≤ n ∧ n < start (j+1) := by
  induction n with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨j, lo, hi⟩ := ih
    by_cases h : n+1 < start (j+1)
    · exact ⟨j, by omega, h⟩
    · exact ⟨j+1, by omega, by rw [endpoint (j+1)]; omega⟩

private theorem nondecreasingCnt (A : Set Nat) : Monotone (cnt A) := by
  classical
  intro i j le
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono le))

private theorem countStep (A : Set Nat) (j : Nat) :
    cnt A (start (j+1)) = cnt A (start j) + blockCount A j := by
  classical
  let p := fun x => x ∈ A
  let small := (Finset.range (start j)).filter p
  let big := (Finset.range (start (j+1))).filter p
  have sub : small ⊆ big := Finset.filter_subset_filter p (Finset.range_mono (start_increasing j.lt_succ_self).le)
  have diff : big \ small = (block j).filter p := by
    ext x
    by_cases hx : x ∈ A <;> simp [p, big, small, block, hx]
  change big.card = small.card + ((block j).filter p).card
  rw [← diff, Finset.card_sdiff_of_subset sub]
  have := Finset.card_le_card sub
  omega

/-- Positive integer quotas below half a block suffice for every prescribed density
from zero through one half. Every set meeting those quotas has exactly that density. -/
theorem densityQuotas {a : ℝ} (ha : 0 ≤ a) (aHalf : a ≤ 1/2) :
    ∃ q : Nat → Nat, (∀ j, 2*q j+1 ≤ j+3) ∧ (∀ n, ∃ j ≥ n, 0 < q j) ∧
    ∀ A : Set Nat, (∀ j, blockCount A j = q j) → Exact A a := by
  classical
  let q (j : Nat) := max 1 ⌊a*((j:ℝ)+2)⌋₊
  have nn (j : Nat) : 0 ≤ a*((j:ℝ)+2) := mul_nonneg ha (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hfloor (j : Nat) := Nat.floor_le (nn j)
  have loQ (j : Nat) : a*((j:ℝ)+3)-2 ≤ (q j : ℝ) := by
    have h := Nat.lt_floor_add_one (a*((j:ℝ)+2))
    have m : (⌊a*((j:ℝ)+2)⌋₊ : ℝ) ≤ (q j : ℝ) := Nat.cast_le.mpr (Nat.le_max_right 1 _)
    linarith
  have hiQ (j : Nat) : (q j : ℝ) ≤ a*((j:ℝ)+3)+2 := by
    dsimp [q]; rw [Nat.cast_max]; apply max_le
    · have h := nn j; push_cast; linarith
    · have h := hfloor j; linarith
  refine ⟨q, ?_, fun n => ⟨n, le_rfl, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left ..)⟩, ?_⟩
  · intro j
    have h : (2:ℝ) * (⌊a*((j:ℝ)+2)⌋₊ : ℝ) ≤ (j:ℝ)+2 := by
      have h' := mul_le_mul_of_nonneg_right aHalf (show 0 ≤ (j:ℝ)+2 by have := Nat.cast_nonneg (α := ℝ) j; linarith)
      linarith [hfloor j]
    have intBound : 2 * ⌊a*((j:ℝ)+2)⌋₊ ≤ j+2 := by exact_mod_cast h
    dsimp [q]; omega
  · intro A blocks
    have ends (j : Nat) :
        a*(start j : ℝ)-2*j ≤ (cnt A (start j) : ℝ) ∧
        (cnt A (start j) : ℝ) ≤ a*(start j : ℝ)+2*j := by
      induction j with
      | zero => simp [start, cnt]
      | succ j ih =>
        rw [countStep, blocks, endpoint]
        push_cast
        constructor <;> nlinarith [ih.1, ih.2, loQ j, hiQ j]
    intro ε he
    obtain ⟨J, hJ⟩ := exists_nat_gt (12/ε + 3)
    refine ⟨start J, ?_⟩
    intro n hn
    obtain ⟨j, lower, upper⟩ := insideBlock n
    have le : J ≤ j := by
      by_contra! hh
      exact (not_lt_of_ge hn) (lt_of_lt_of_le upper (start_increasing.monotone hh))
    have lj : (J:ℝ) ≤ (j:ℝ) := by exact_mod_cast le
    have divnonneg := div_nonneg (show 0 ≤ (12:ℝ) by norm_num) he.le
    have large : (3:ℝ) < (j:ℝ) := by linarith
    have eLarge : (12:ℝ) < (j:ℝ)*ε := (div_lt_iff₀ he).mp (by linarith)
    have hquad : (j:ℝ)*(j:ℝ) ≤ 2*(start j:ℝ) := by exact_mod_cast quadratic j
    have ln : (start j:ℝ) ≤ (n:ℝ) := by exact_mod_cast lower
    have un : (n:ℝ) ≤ (start j:ℝ)+j+3 := by rw [endpoint] at upper; exact_mod_cast upper.le
    have room : 5*(j:ℝ) + 3 ≤ ε*(n:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hquad he.le
      have h' := mul_lt_mul_of_pos_right eLarge (show 0 < (j:ℝ) by linarith)
      have h'' := mul_le_mul_of_nonneg_left ln he.le
      nlinarith
    have cLo : (cnt A (start j):ℝ) ≤ (cnt A n:ℝ) := by exact_mod_cast nondecreasingCnt A lower
    have cHi : (cnt A n:ℝ) ≤ (cnt A (start (j+1)):ℝ) := by exact_mod_cast nondecreasingCnt A upper.le
    rw [endpoint] at cHi
    have e0 := (ends j).1
    have e1 := (ends (j+1)).2
    rw [endpoint] at e1
    push_cast at e1
    have nearLo := mul_le_mul_of_nonneg_left un ha
    have nearHi := mul_le_mul_of_nonneg_left ln ha
    have prod := mul_le_mul_of_nonneg_right aHalf (show 0 ≤ (j:ℝ) by exact Nat.cast_nonneg j)
    constructor <;> nlinarith

end SingletonDensity
