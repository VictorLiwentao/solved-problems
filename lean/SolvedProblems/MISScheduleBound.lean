module

public import SolvedProblems.MISSeparationProbability

@[expose] public section

namespace MISQueries

/-- The source uses independent blockers with this sampling probability. -/
noncomputable def rate (n D : ℕ) : ℝ := D / (4*n)
noncomputable def exponent (t D : ℕ) : ℝ := 4608*t/(D:ℝ)^2

theorem rate_pos {n D : ℕ} (hn : 0<n) (hd : 0<D) : 0 < rate n D := by unfold rate; positivity

theorem rate_le_one {n D : ℕ} (hn : 0<n) (hd : D ≤ n) : rate n D ≤ 1 := by
  unfold rate
  apply (div_le_one (by positivity)).mpr
  have h : (D:ℝ) ≤ n := by exact_mod_cast hd
  linarith

theorem pair_count (n : ℕ) : (pairs (Fin n)).card = n.choose 2 := by simp [pairs]

/-- Sum the supporting tangent to exp at the negative mean charge. -/
theorem exp_sum_lower {I : Type*} (T : Finset I) (f : I → ℝ) (m : ℝ)
    (h : ∑ x ∈ T, f x ≤ T.card * m) : T.card * Real.exp (-m) ≤ ∑ x ∈ T, Real.exp (-f x) := by
  have hx (x : I) : Real.exp (-m)*(1+m - f x) ≤ Real.exp (-f x) := by
    rw [show -f x = -m+(m-f x) by ring, Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith only [Real.add_one_le_exp (m-f x)]
  apply le_trans _ (Finset.sum_le_sum (fun x _ => hx x))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  nlinarith only [mul_nonneg (Real.exp_pos (-m)).le (sub_nonneg.mpr h)]

/-- Every fixed schedule misses a uniformly hidden pair with probability at least
one half of exp(-4608 t / Δ²), before discarding over-degree blocker samples. -/
theorem schedule_bound {n D t : ℕ} (hn : 2 ≤ n) (hd : 0 < D) (hdn : D ≤ n)
    (ht : 2*t ≤ n.choose 2) (Q : Fin t → Finset (Fin n)) :
    ((n.choose 2:ℝ)/2)*Real.exp (-exponent t D) ≤
      ∑ e ∈ pairs (Fin n), average (rate n D) Finset.univ.toList (fun S => bit (miss Q e S)) := by
  classical
  let R := remaining Q
  have hsurv := remaining_card Q
  rw [pair_count] at hsurv
  have hN : n.choose 2 ≤ 2*R.card := by dsimp [R]; omega
  have hNr : (n.choose 2 : ℝ) ≤ 2*R.card := by exact_mod_cast hN
  have hnn : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hcap : (n:ℝ)^2 ≤ 8*R.card := by nlinarith only [real_choose_two n,hNr,mul_nonneg (show 0 ≤ (n:ℝ) by positivity) (sub_nonneg.mpr hnn)]
  have hp := rate_pos (n:=n) (by omega) hd
  have hp' := rate_le_one (n:=n) (by omega) hdn
  have hb : (∑ e ∈ R, cost (rate n D) Q e) ≤ R.card * exponent t D := by
    apply (cost_sum hp Q).trans
    unfold rate exponent
    field_simp [ne_of_gt (show (0:ℝ)<D by exact_mod_cast hd),ne_of_gt (show (0:ℝ)<n by positivity)]
    nlinarith only [mul_nonneg (show 0 ≤ (t:ℝ) by positivity) (sub_nonneg.mpr hcap)]
  have hpart := exp_sum_lower R (cost (rate n D) Q) (exponent t D) hb
  calc
    _ ≤ R.card * Real.exp (-exponent t D) := mul_le_mul_of_nonneg_right (by linarith only [hNr]) (Real.exp_pos _).le
    _ ≤ _ := hpart
    _ ≤ ∑ e ∈ R, average (rate n D) Finset.univ.toList (fun S => bit (miss Q e S)) :=
      Finset.sum_le_sum (fun e he => miss_for_pair hp hp' Q he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun _ _ _ => average.nonneg hp.le hp' _ (fun _ => bit_nonneg _))

/-- With p = Δ/(4n), the discarded degree tail is at most exp(-Δ/4). -/
theorem degree_tail {n D : ℕ} (hn : 0<n) (hd : 0 < D) (hdn : D ≤ n) :
    average (rate n D) (Finset.univ : Finset (Fin n)).toList (fun S => bit (D ≤ S.card)) ≤
      Real.exp (-(D:ℝ)/4) := by
  let p := rate n D
  have hp : 0 ≤ p := (rate_pos hn hd).le
  have hb := bad_probability hp (rate_le_one hn hdn) (Finset.univ : Finset (Fin n)).toList D
  simp only [Finset.length_toList, Finset.card_univ, Fintype.card_fin] at hb
  apply hb.trans
  have hbase : 1+p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have up := pow_le_pow_left₀ (show 0 ≤ 1+p by linarith) hbase n
  rw [←Real.exp_nat_mul] at up
  have hnz : (n:ℝ) ≠ 0 := by positivity
  have hpval : (n:ℝ)*p = D/4 := by dsimp [p,rate]; field_simp
  rw [hpval] at up
  have hlog : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hlo : Real.exp ((D:ℝ)/2) ≤ (2:ℝ)^D := by
    calc
      _ ≤ Real.exp ((D:ℝ)*Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg (show 0 ≤ (D:ℝ) by positivity) (sub_nonneg.mpr hlog)]
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  apply le_trans (div_le_div₀ (Real.exp_pos _).le up (Real.exp_pos _) hlo)
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

end MISQueries
