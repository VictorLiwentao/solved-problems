module

public import SolvedProblems.MISLowerBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MISQueries

/-- The dense lower estimate gives a direct finite obstruction at every inverse
polynomial failure level. -/
theorem confidence_obstruction {n D t : ℕ} (hn : 2 ≤ n) (hd : 0 < D) (hdn : D ≤ n-1)
    (ht : 2*t ≤ n.choose 2) (a : ℝ) (size : 4*(a*Real.log n) ≤ D)
    (gap : exponent t D + Real.log 8 < a*Real.log n) (w : Strategy n t → ℝ) (hw : Distribution w) :
    ¬Learns w D ((n:ℝ)^(-a)) := by
  intro h
  let z := a*Real.log n
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n:ℝ)^(-a) = Real.exp (-z) := by rw [Real.rpow_def_of_pos hn']; congr 1; dsimp [z]; ring
  have hbound := randomized_lower hn hd hdn ht w hw (Real.rpow_nonneg hn'.le _) h
  rw [he] at hbound
  have htail : Real.exp (-(D:ℝ)/4) ≤ Real.exp (-z) := Real.exp_le_exp.mpr (by dsimp [z]; linarith only [size])
  have hstrict := Real.exp_lt_exp.mpr (show Real.log 8 + -z < -exponent t D by dsimp [z]; linarith only [gap])
  rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<8)] at hstrict
  change Real.exp (-exponent t D)/4 - _ ≤ Real.exp (-z) at hbound
  linarith

theorem square_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith only [ih, hk, Nat.mul_le_mul_left k hk]

theorem log_two_bounds : (1:ℝ)/2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  · linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

/-- Negative answer to Michel and Scott's high-confidence question. For any
fixed coefficient and any positive inverse-polynomial exponent, arbitrarily
large labeled graphs violate the proposed Δ² log(n/Δ) nonadaptive query bound. -/
theorem no_log_ratio_bound (a : ℝ) (ha : 0 < a) (C n₀ : ℕ) :
    ∃ n D : ℕ, n₀ ≤ n ∧ 2 ≤ n ∧ 0 < D ∧ D ≤ n-1 ∧
      ∀ (t : ℕ), t ≤ C * D^2 * Nat.log 2 (n/D) →
        ∀ w : Strategy n t → ℝ, Distribution w → ¬Learns w D ((n:ℝ)^(-a)) := by
  let k := C+4
  obtain ⟨m,hm⟩ := exists_nat_gt (max (max (max (k:ℝ) n₀) (8*a)) (2*(4608*C*k+4)/a))
  have hm₁ : (k:ℝ) < m := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hm))
  have hm₂ : (n₀:ℝ) < m := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hm))
  have hm₃ : 8*a < m := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hm)
  have hm₄ : 2*(4608*C*k+4) < (m:ℝ)*a := (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hm)
  have hkm : k < m := by exact_mod_cast hm₁
  have hk : 4 ≤ k := by dsimp [k]; omega
  let D := 2^m
  let r := 2^k
  let n := D*r
  have hd : 0 < D := by dsimp [D]; positivity
  have hr : 2 ≤ r := by dsimp [r]; exact (by decide : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hn : 2 ≤ n := by dsimp [n]; nlinarith only [hd,hr,Nat.mul_le_mul_left D hr]
  have hdn : D ≤ n-1 := by dsimp [n]; have := Nat.mul_le_mul_left D hr; omega
  have hn₀ : n₀ ≤ n := by
    have h₀ : n₀ < m := by exact_mod_cast hm₂
    have h₁ : m < D := Nat.lt_two_pow_self
    omega
  refine ⟨n,D,hn₀,hn,hd,hdn,?_⟩
  intro t ht w hw
  have hratio : Nat.log 2 (n/D) = k := by simp [n, D, r, Nat.log_pow]
  rw [hratio] at ht
  have hnr : (n:ℝ) = (D:ℝ)*r := by dsimp [n]; push_cast; rfl
  have hc : (C:ℝ) ≤ k := by exact_mod_cast (show C ≤ k by dsimp [k]; omega)
  have hkr : (4:ℝ)*k ≤ r := by
    have hh : k^2 ≤ r := square_le_two_pow hk
    exact_mod_cast (show 4*k ≤ r by nlinarith only [hh,Nat.mul_le_mul_right k hk])
  have htr : (t:ℝ) ≤ C*(D:ℝ)^2*k := by exact_mod_cast ht
  have hcap : 2*t ≤ n.choose 2 := by
    have hrr : 8*(C:ℝ)*k ≤ (r:ℝ)^2 := by
      have hks : 0 ≤ (k:ℝ) := by positivity
      nlinarith only [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*k) hkr 2, mul_nonneg (sub_nonneg.mpr hc) hks, sq_nonneg (k:ℝ)]
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hnlo : (n:ℝ)^2 ≤ 4*(n.choose 2:ℝ) := by
      nlinarith only [real_choose_two n, mul_nonneg (by positivity : 0 ≤ (n:ℝ)) (sub_nonneg.mpr hn')]
    rw [hnr] at hnlo
    have hcap' : 2*(t:ℝ) ≤ (n.choose 2:ℝ) := by nlinarith only [htr,hnlo,mul_nonneg (sq_nonneg (D:ℝ)) (sub_nonneg.mpr hrr)]
    exact_mod_cast hcap'
  have hl : Real.log (n:ℝ) = ((m:ℝ)+k)*Real.log 2 := by
    dsimp [n,D,r]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  apply confidence_obstruction hn hd hdn hcap a _ _ w hw
  · have hlog : Real.log (n:ℝ) ≤ 2*m := by rw [hl]; nlinarith only [hm₁, mul_nonneg (by positivity : 0 ≤ (m:ℝ)+k) (sub_nonneg.mpr log_two_bounds.2)]
    have hdlarge : m^2 ≤ D := square_le_two_pow (by omega)
    have hdr : (m:ℝ)^2 ≤ D := by exact_mod_cast hdlarge
    nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hlog), mul_nonneg (show 0 ≤ (m:ℝ) by positivity) (sub_nonneg.mpr hm₃.le), hdr]
  · have hex : exponent t D ≤ 4608*C*k := by
      unfold exponent
      apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hd))).mpr
      linarith only [htr]
    have hl₈ : Real.log 8 ≤ 3 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
      norm_num1
      linarith only [log_two_bounds.2]
    have hlm : (m:ℝ)/2 ≤ Real.log n := by
      rw [hl]
      nlinarith only [mul_nonneg (show 0 ≤ (m:ℝ) by positivity) (sub_nonneg.mpr log_two_bounds.1),
        mul_nonneg (show 0 ≤ (k:ℝ) by positivity) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
    nlinarith only [hm₄, hex, hl₈, mul_nonneg ha.le (sub_nonneg.mpr hlm)]

end MISQueries
