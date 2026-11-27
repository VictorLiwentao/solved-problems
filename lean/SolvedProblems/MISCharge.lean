module

public import SolvedProblems.MISModel
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace MISQueries

/-- With k spare vertices the chance of seeing a blocker dominates this exponential.
The quadratic bound makes the charge summable over the pairs inside one query. -/
theorem hit_ge_exp {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1) {k : ℕ} (hk : 0 < k) :
    Real.exp (-(4 / (p * k)^2)) ≤ 1 - (1-p)^k := by
  let r := p * k
  have hr : 0 < r := mul_pos hp (by exact_mod_cast hk)
  have hpow : (1-p)^k ≤ Real.exp (-r) := by
    calc
      _ ≤ (Real.exp (-p)) ^ k := by
        apply pow_le_pow_left₀ (sub_nonneg.mpr hp') _ _
        linarith [Real.add_one_le_exp (-p)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; dsimp [r]; ring
  have hE : 1 < Real.exp r := Real.one_lt_exp_iff.mpr hr
  have hsq : r^2/4 ≤ Real.exp r - 1 := by
    have he : 1 + r/2 ≤ Real.exp (r/2) := by linarith [Real.add_one_le_exp (r/2)]
    have he2 := pow_le_pow_left₀ (show 0 ≤ 1+r/2 by linarith) he 2
    rw [sq (Real.exp _), ← Real.exp_add, show r/2+r/2 = r by ring] at he2
    nlinarith only [he2, hr]
  have hrec : 1/(Real.exp r-1) ≤ 4/r^2 := by
    apply (div_le_div_iff₀ (by linarith) (sq_pos_of_pos hr)).mpr
    nlinarith only [hsq]
  have hbase : 0 < 1-Real.exp (-r) := by rw [Real.exp_neg]; exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hE)
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
  rw [Real.log_inv] at hlog
  have hid : (1-Real.exp (-r))⁻¹ - 1 = 1/(Real.exp r-1) := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos r), ne_of_gt (sub_pos.mpr hE)]
    ring
  rw [hid] at hlog
  calc
    _ ≤ Real.exp (Real.log (1-Real.exp (-r))) := by
      apply Real.exp_le_exp.mpr
      change -(4/r^2) ≤ _
      linarith
    _ = 1-Real.exp (-r) := Real.exp_log hbase
    _ ≤ 1-(1-p)^k := sub_le_sub_left hpow _

/-- Charge paid by an included pair in a query. Queries of size two are removed
before applying this bound. -/
noncomputable def charge (p : ℝ) (q : ℕ) : ℝ := 4/(p*(q-2 : ℕ))^2

theorem charge_nonneg (p : ℝ) (q : ℕ) : 0 ≤ charge p q := by unfold charge; positivity

theorem real_choose_two (n : ℕ) : 2*(n.choose 2 : ℝ) = n*(n-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show (n+1).choose 2 = n.choose 1 + n.choose 2 from Nat.choose_succ_succ ..,
      Nat.choose_one_right, Nat.cast_add, Nat.cast_succ]
    linarith only [ih]

theorem paid_per_query {p : ℝ} (hp : 0 < p) {q : ℕ} (hq : 3 ≤ q) :
    (q.choose 2 : ℝ) * charge p q ≤ 36 / p^2 := by
  let k := q-2
  have hk : (0:ℝ) < k := by exact_mod_cast (show 0 < k by dsimp [k]; omega)
  have hqk : (q:ℝ) ≤ 3*k := by exact_mod_cast (show q ≤ 3*k by dsimp [k]; omega)
  have hsq := pow_le_pow_left₀ (show 0 ≤ (q:ℝ) by positivity) hqk 2
  have hc := real_choose_two q
  have hq0 : 0 ≤ (q:ℝ) := by positivity
  unfold charge
  change (q.choose 2 : ℝ) * (4/(p*k)^2) ≤ 36 / p^2
  field_simp [ne_of_gt hp, ne_of_gt hk]
  nlinarith only [hc,hsq,hq0,sq_nonneg (k:ℝ)]

end MISQueries
