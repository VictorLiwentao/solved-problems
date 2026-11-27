module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

open Filter Finset
open scoped Topology

namespace AtomicGrowth

/-- A large integer w absorbs the polynomial prefactor in the Pantone–Vatter
bound. A geometric majorant of ratio 99/100 controls every positive partial
sum, uniformly in the valley length. -/
theorem choose_scale :
    ∃ w : ℕ, 4105 ≤ w ∧
      ∀ q : ℕ → ℕ, (∀ n, 0<n → q n ≤ 512*8^n*n^2*(n+2).choose 2*(w+513)^(n-1)) →
        ∀ m, (∑ i : Fin m, (q (i.val+1) : ℝ) / (17*(w:ℝ)/2)^(i.val+1)) ≤ 1 := by
  let r : ℝ := 99/100
  let t : ℝ := 97/100
  obtain ⟨M,hM⟩ := (tendsto_pow_const_mul_const_pow_of_lt_one 4 (by norm_num [t] : 0≤t)
    (by norm_num [t] : t<1)).bddAbove_range
  obtain ⟨w,hw⟩ := exists_nat_gt (max 30000 (460800*M))
  have hwbig : (30000:ℝ) < w := (le_max_left ..).trans_lt hw
  have hcoef : 460800*M < w := (le_max_right ..).trans_lt hw
  refine ⟨w,by exact_mod_cast (show (4105:ℝ) ≤ w by linarith),?_⟩
  intro q hq m
  let L := 17*(w:ℝ)/2
  have hL : 0<L := by dsimp [L]; positivity
  have hbase : 8*((w:ℝ)+513) ≤ (t*r)*L := by dsimp [t,r,L]; linarith
  have each (k : ℕ) : (q (k+1) : ℝ)/L^(k+1) ≤ (1/100)*r^k := by
    let n := k+1
    have hn : 1 ≤ (n:ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hcast : (q n:ℝ) ≤ 512*(8:ℝ)^n*(n:ℝ)^2*((n+2).choose 2:ℕ)*((w:ℝ)+513)^k := by
      have hh := hq n (by dsimp [n]; omega)
      have hk : n-1=k := by simp [n]
      rw [hk] at hh
      exact_mod_cast hh
    have hbin : (((n+2).choose 2:ℕ):ℝ) ≤ 9*(n:ℝ)^2 := by
      have hc : (((n+2).choose 2:ℕ):ℝ) ≤ ((n:ℝ)+2)^2 := by exact_mod_cast Nat.choose_le_pow (n+2) 2
      nlinarith only [hc,hn,sq_nonneg ((n:ℝ)-1)]
    have hmajor : (q n:ℝ)*((w:ℝ)+513) ≤ 4608*(n:ℝ)^4*(8*((w:ℝ)+513))^n := by
      have hx := mul_le_mul_of_nonneg_right hcast (by positivity : 0≤(w:ℝ)+513)
      have hy := mul_le_mul_of_nonneg_left hbin (by positivity : 0≤512*(8:ℝ)^n*(n:ℝ)^2*((w:ℝ)+513)^n)
      rw [mul_pow]
      rw [show ((w:ℝ)+513)^n = ((w:ℝ)+513)^k*((w:ℝ)+513) from pow_succ ..] at hy ⊢
      nlinarith only [hx,hy]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 8*((w:ℝ)+513)) hbase n
    have hbd : (n:ℝ)^4*t^n ≤ M := hM ⟨n,rfl⟩
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0≤4608*(n:ℝ)^4)
    have hm' := mul_le_mul_of_nonneg_right hbd (by positivity : 0≤4608*r^n*L^n)
    simp only [mul_pow] at hmul hmajor
    have hlarge := mul_le_mul_of_nonneg_right (show 4608*M ≤ ((w:ℝ)+513)/100 by linarith) (by positivity : 0≤r^n*L^n)
    have hqn : (q n:ℝ) ≤ (1/100)*r^n*L^n := by
      apply le_of_mul_le_mul_right (a:=((w:ℝ)+513)) _ (by positivity)
      nlinarith only [hmajor,hmul,hm',hlarge]
    have hr : r^(k+1)≤r^k := by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num [r])
    exact ((div_le_iff₀ (pow_pos hL _)).mpr hqn).trans (mul_le_mul_of_nonneg_left hr (by norm_num))
  change _ ≤ _
  calc (∑ i : Fin m, (q (i.val+1):ℝ)/L^(i.val+1)) ≤ ∑ i : Fin m, (1/100)*r^i.val :=
         Finset.sum_le_sum fun i _ => each i.val
       _ = (1/100)* ∑ k ∈ Finset.range m, r^k := by rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
       _ ≤ 1 := by
         have hsum := (summable_geometric_of_lt_one (by norm_num [r] : 0≤r) (by norm_num [r] : r<1)).sum_le_tsum
           (Finset.range m) (fun i _ => pow_nonneg (by norm_num [r]) i)
         rw [tsum_geometric_of_lt_one (by norm_num [r]) (by norm_num [r])] at hsum
         dsimp [r] at hsum ⊢
         norm_num at hsum
         linarith

end AtomicGrowth
