module

public import SolvedProblems.EMXUpper
import SolvedProblems.EMXCounting
public import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace EMX

open scoped Classical

noncomputable def optimalSize (m : ℕ) : ℕ :=
  sInf {d : ℕ | Within d m}

theorem optimal_spec (m : ℕ) : Within (optimalSize m) m ∧ ∀ d, Within d m → optimalSize m ≤ d :=
  ⟨csInf_mem (s := {d : ℕ | Within d m}) ⟨_, logUpper m⟩,
    fun _ hd => csInf_le (OrderBot.bddBelow _) hd⟩

/-- Explicit finite-sample form of d(m) = log₂(m) + O(log log m). The optimum
ranges over all ordered messages with repetitions and a decoder at the size bound.
The upper construction uses no side information. -/
theorem logarithmicSize (m : ℕ) (hm : 2 ≤ m) :
    optimalSize m ≤ m.log2 ∧ m.log2 ≤ optimalSize m + 2*(m.log2.log2+1) := by
  let T := m.log2
  let k := T.log2+1
  let t := T-k
  let d := optimalSize m
  have hT : 1 ≤ T := (Nat.le_log2 (by omega : m ≠ 0)).mpr hm
  have up := (optimal_spec m).2 _ (logUpper m)
  rw [show max 1 m.log2 = T from Nat.max_eq_right hT] at up
  refine ⟨up, ?_⟩
  change T ≤ d+2*k
  have hk : 1 ≤ k := Nat.succ_pos _
  by_cases hsmall : t < 2
  · dsimp [t] at hsmall; omega
  have tbound : t ≤ T := Nat.sub_le .. 
  have tsize : t+k = T := Nat.sub_add_cancel (by dsimp [t] at hsmall; omega)
  have ht : 2 ≤ t := by omega
  have fit : 2^t*t-t ≤ m := by
    calc
      _ ≤ 2^t*t := Nat.sub_le ..
      _ ≤ 2^t*2^k := Nat.mul_le_mul_left _ (tbound.trans Nat.lt_log2_self.le)
      _ = 2^T := by rw [← Nat.pow_add, tsize]
      _ ≤ m := Nat.log2_self_le (by omega)
  by_cases td : t ≤ d
  · omega
  obtain ⟨D, works⟩ := (optimal_spec m).1
  have hwidth : width (t-2) = t := by dsimp [width];omega
  have low := counting_necessary (t-2) d 1 D (by rw [hwidth]; exact works _ fit)
  rw [hwidth, Nat.one_mul] at low
  have htk : t ≤ 2^k := tbound.trans Nat.lt_log2_self.le
  have hd1 : d+1 ≤ t := by omega
  have bits : (d+1)*(2^t*t)^d ≤ 2^(k+(t+k)*d) := by
    rw [Nat.pow_add 2 k _, Nat.pow_mul 2 (t+k) d, Nat.pow_add 2 t k]
    exact Nat.mul_le_mul (hd1.trans htk) (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ htk) _)
  have hlog := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (low.trans bits)
  have ar : t*t ≤ t*(d+k) := by
    have hprod := Nat.mul_le_mul_left k hd1
    nlinarith
  have t_le := Nat.le_of_mul_le_mul_left ar (by omega : 0 < t)
  omega

end EMX
