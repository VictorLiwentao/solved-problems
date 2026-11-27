module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter Real

namespace SphericalEntropy

theorem factorial_rate {α B : ℝ} (ha : 0<α) (hb : 0<B) :
    ∀ᶠ k : ℕ in atTop, B*α^k/(k.factorial:ℝ) ≤ exp (-(k:ℝ)*log k/2) := by
  let b := max 0 (log B)
  have ht : Tendsto (fun k : ℕ => log (k:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,ht.eventually_ge_atTop (2*(log α+1+b))] with k hk hlog
  have hone : (1:ℝ)≤k := by exact_mod_cast hk
  have hkpos : 0<(k:ℝ) := by linarith
  have hklog : 0≤log (k:ℝ) := log_nonneg hone
  have hpi : 0≤log (2*π) := log_nonneg (by linarith [two_le_pi])
  have hfac := Stirling.le_log_factorial_stirling (n:=k) (by omega)
  have h₁ : log B ≤ b := le_max_right .. 
  have h₂ : 0≤b := le_max_left .. 
  have h₃ : b ≤ (k:ℝ)*b := le_mul_of_one_le_left h₂ hone
  have h₄ := mul_le_mul_of_nonneg_left hlog hkpos.le
  rw [← log_le_log_iff (by positivity) (exp_pos _),log_div (by positivity) (by positivity),
    log_mul hb.ne' (pow_pos ha _).ne',log_pow,log_exp]
  linarith

/-- At large N, the highest degree supplied by C t^s ≤ N has the target
factorial rate in intrinsic dimension s. The index is N+1 to keep every
finite configuration nonempty. -/
theorem choose_degree {s C : ℕ} (hs : 0<s) (hC : 0<C) :
    ∃ c : ℝ, 0<c ∧ ∀ A : ℕ, ∀ᶠ N : ℕ in atTop,
      ∃ t : ℕ, A≤t+1 ∧ C*t^s ≤ N+1 ∧
      -(t+1:ℝ)*log (t+1)/2 ≤ -c*((N+1:ℝ)^((s:ℝ)⁻¹))*log (N+1) := by
  have hs' : 0<(s:ℝ) := by exact_mod_cast hs
  have hC' : 0<(C:ℝ) := by exact_mod_cast hC
  have hC₁ : 1≤(C:ℝ) := by exact_mod_cast hC
  let c := (4*(s:ℝ)*C)⁻¹
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  intro A
  let root (N : ℕ) := (N+1:ℝ)^((s:ℝ)⁻¹)
  let t (N : ℕ) := ⌊root N/C⌋₊
  have ht : Tendsto t atTop atTop := tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (inv_pos.mpr hs')).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop) |>.atTop_div_const hC')
  filter_upwards [ht.eventually_ge_atTop (max A C)] with N hN
  let k := t N + 1
  have hk : (k:ℝ) = (t N:ℝ)+1 := by simp [k]
  have hr : 0<root N := Real.rpow_pos_of_pos (by positivity) _
  have hrpow : (root N)^s=(N+1:ℝ) := Real.rpow_inv_natCast_pow (by positivity) hs.ne'
  have hcsmall : (C:ℝ)*(t N:ℝ)≤root N := by
    rw [mul_comm]
    exact (le_div_iff₀ hC').mp (Nat.floor_le (div_nonneg hr.le hC'.le))
  have hcp : (C:ℝ)≤(C:ℝ)^s := by simpa using pow_le_pow_right₀ hC₁ hs
  have hdesign : C*(t N)^s ≤ N+1 := by
    have hh := pow_le_pow_left₀ (by positivity) hcsmall s
    rw [mul_pow,hrpow] at hh
    exact_mod_cast (mul_le_mul_of_nonneg_right hcp (by positivity : (0:ℝ)≤(t N:ℝ)^s)).trans hh
  have hnext : root N < (C:ℝ)*k := by
    rw [mul_comm,hk]
    exact (div_lt_iff₀ hC').mp (Nat.lt_floor_add_one _)
  have hkc : (C:ℝ)≤k := by exact_mod_cast (le_max_right A C).trans (hN.trans (Nat.le_succ _))
  have hk1 : 1≤(k:ℝ) := hC₁.trans hkc
  have hlog : log (root N) ≤ 2*log (k:ℝ) := by
    have hb := Real.log_le_log hr hnext.le
    rw [Real.log_mul hC'.ne' (by positivity)] at hb
    linarith [Real.log_le_log hC' hkc]
  have hrlog : log (root N)=(s:ℝ)⁻¹*log (N+1:ℝ) := Real.log_rpow (by positivity) _
  have hnlog : log (N+1:ℝ) ≤ (2*(s:ℝ))*log (k:ℝ) := by
    rw [hrlog,inv_mul_eq_div] at hlog
    linarith [(div_le_iff₀ hs').mp hlog]
  have hprod := mul_le_mul hnext.le hnlog (log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) N])) (by positivity)
  refine ⟨t N,(le_max_left A C).trans (hN.trans (Nat.le_succ _)),hdesign,?_⟩
  change -((t N:ℝ)+1)*log ((t N:ℝ)+1)/2 ≤ -c*(root N)*log (N+1:ℝ)
  rw [←hk]
  dsimp [c]
  field_simp
  nlinarith only [hprod]

end SphericalEntropy
