module

public import SolvedProblems.UniversalWadgeDigits
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace UniversalWadge

open scoped Classical Topology

/-- Multiplying by the n-th character clears the denominators of every earlier digit. -/
theorem prior_integer (a : Tests) {i n : ℕ} (hi : i<n) :
    ∃ z : ℕ, (character n:ℝ)*term a i = z := by
  obtain ⟨j,hj⟩ := digit_realized a i
  unfold term
  rw [hj,bitValue];split
  · have bound : level i + (j.val+2) ≤ level n := by
      have m : (i+1+2)^2 ≤ (n+2)^2 := Nat.pow_le_pow_left (by omega) _
      have ji := j.isLt
      unfold level;nlinarith
    let d := level n - (level i+(j.val+2))
    have dec : level n = d+(level i+(j.val+2)) := (Nat.sub_add_cancel bound).symm
    refine ⟨2^d, ?_⟩
    rw [← dyad_add];unfold character dyad;push_cast;rw [dec,pow_add (2:ℝ) d _,mul_assoc,← mul_pow];norm_num
  · exact ⟨0,by simp⟩

noncomputable def tail (a : Tests) (n : ℕ) := ∑' j, (character n:ℝ)*term a (j+(n+1))

theorem scaled_tail_bound (a : Tests) (n j : ℕ) :
    (character n:ℝ)*term a (j+(n+1)) ≤ (dyad (n+1)/4)*dyad j := by
  let r := j+(n+1)
  have bounds : level n + (n+1+j) ≤ level r := by unfold level;dsimp [r];nlinarith
  have wd := mul_le_mul_of_nonneg_left (dyad_antitone bounds) (by positivity : 0 ≤ (character n:ℝ))
  rw [dyad_add,← mul_assoc,char_dyad,one_mul,dyad_add] at wd
  change (character n:ℝ)*(dyad (level r)*digit a r) ≤ _
  rw [← mul_assoc]
  calc
    _ ≤ (dyad (n+1)*dyad j)*(1/4) := mul_le_mul wd (digit_range a r).2 (digit_range a r).1
      (mul_nonneg (dyad_pos _).le (dyad_pos _).le)
    _ = _ := by ring

theorem tail_range (a : Tests) (n : ℕ) : 0 ≤ tail a n ∧ tail a n ≤ dyad (n+1)/2 := by
  have nn (j) : 0 ≤ (character n:ℝ)*term a (j+(n+1)) := mul_nonneg (Nat.cast_nonneg _) (term_bound a _).1
  have s := dyad_summable.mul_left (dyad (n+1)/4)
  have t := Summable.of_nonneg_of_le nn (scaled_tail_bound a n) s
  refine ⟨tsum_nonneg nn, (t.tsum_le_tsum (scaled_tail_bound a n) s).trans_eq ?_⟩
  rw [tsum_mul_left,dyad_sum];ring

theorem norm_character (a : Tests) (n : ℕ) : ‖character n • code a‖ = digit a n + tail a n := by
  let p (i) := (character n:ℝ)*term a i
  have sum : Summable p := (term_summable a).mul_left _
  let z (i : ℕ) := if h : i<n then (prior_integer a h).choose else 0
  have hz : (∑ i∈Finset.range n, p i) = ((∑ i∈Finset.range n, z i:ℕ):ℝ) := by
    push_cast;apply Finset.sum_congr rfl;intro i hi
    have lt := Finset.mem_range.mp hi
    simpa only [z,lt,↓reduceDIte] using (prior_integer a lt).choose_spec
  have mid : p n = digit a n := by dsimp [p,term];rw [← mul_assoc,char_dyad,one_mul]
  have parts : (character n:ℝ)*(∑' i, term a i) = ((∑ i∈Finset.range n, z i:ℕ):ℝ)+(digit a n+tail a n) := by
    rw [← tsum_mul_left, ← sum.sum_add_tsum_nat_add (n+1),Finset.sum_range_succ,hz,mid,add_assoc];rfl
  have clear : (((∑ i∈Finset.range n, z i:ℕ):ℝ):Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨(∑ i∈Finset.range n, z i:ℕ),by simp⟩
  change ‖character n • (((∑' i, term a i):ℝ):Circle)‖ = _
  rw [← AddCircle.coe_nsmul,nsmul_eq_mul,parts,AddCircle.coe_add,clear,zero_add]
  have r := tail_range a n
  have d := digit_range a n
  have le : dyad (n+1) ≤ 1/2 := (dyad_antitone (show 1≤n+1 by omega)).trans (by norm_num [dyad])
  rw [((AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num : (1:ℝ)≠0)).mpr (by
    rw [abs_of_nonneg (add_nonneg d.1 r.1),abs_one];linarith)), abs_of_nonneg (add_nonneg d.1 r.1)]

end UniversalWadge
