module

public import SolvedProblems.ReluGateCircuit
public import SolvedProblems.ReluUnivariate

@[expose] public section

open MeasureTheory

namespace ReluMoments

theorem GateAffine.continuous_eval {n : ℕ} (a : GateAffine n) {v : ℝ → Fin n → ℝ}
    (hv : ∀ i, Continuous (fun x => v x i)) : Continuous fun x => a.eval x (v x) := by
  unfold GateAffine.eval Line.value
  fun_prop (disch := solve_by_elim)

theorem Circuit.continuous_values {n : ℕ} (b : Circuit n) :
    ∀ i, Continuous (fun x => b.values x i) := by
  induction b with
  | empty => exact fun i => i.elim0
  | append prev a ih =>
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [values,Fin.snoc_last] using (a.continuous_eval ih).max continuous_const
    | cast i => simpa only [values,Fin.snoc_castSucc] using ih i

theorem Circuit.continuous_out {n : ℕ} (b : Circuit n) (a : GateAffine n) : Continuous (b.out a) :=
  a.continuous_eval b.continuous_values

theorem Circuit.integrable_out {n : ℕ} (b : Circuit n) (a : GateAffine n) (μ : Measure ℝ) (k : ℕ)
    (hi : Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ) :
    Integrable (fun x => x^k * b.out a x) μ := by
  let coeff (σ : Fin n → Bool) := |(a.onLines (b.maskLines σ)).1| + |(a.onLines (b.maskLines σ)).2|
  let C := ∑ σ, coeff σ
  have hh (x : ℝ) : |b.out a x| ≤ C*(1+|x|) := by
    obtain ⟨σ,hx,_⟩ := b.common_mask (x:=x) (y:=x) (fun _ _ => Iff.rfl)
    rw [b.out_on_mask a hx]
    have hle : coeff σ ≤ C := Finset.single_le_sum (f:=coeff) (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ σ)
    let l := a.onLines (b.maskLines σ)
    change |l.1*x+l.2| ≤ _
    apply (abs_add_le ..).trans
    rw [abs_mul]
    calc _ ≤ (|l.1|+|l.2|)*(1+|x|) := by nlinarith only [abs_nonneg l.1,mul_nonneg (abs_nonneg l.2) (abs_nonneg x)]
         _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
  apply (hi.const_mul C).mono' ((continuous_id.pow k).mul (b.continuous_out a)).aestronglyMeasurable
  filter_upwards with x
  change |x^k*b.out a x| ≤ _
  rw [abs_mul,abs_pow]
  calc _ ≤ |x|^k*(C*(1+|x|)) := mul_le_mul_of_nonneg_left (hh x) (by positivity)
       _ = _ := by ring

theorem circuit_identification {n m : ℕ} (b : Circuit n) (c : Circuit m) (a : GateAffine n) (a' : GateAffine m)
    (μ : Measure ℝ) [μ.IsOpenPosMeasure] (D : ℕ) (hD : 2*(2^n+2^m+2^n*2^m) ≤ D)
    (hi : ∀ k ≤ D, Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ) :
    (∀ k ≤ D, (∫ x, x^k*b.out a x ∂μ) = ∫ x, x^k*c.out a' x ∂μ) ↔ b.out a = c.out a' := by
  constructor
  · intro h
    obtain ⟨s,hc,hs⟩ := b.sign_cuts c a a'
    have hki (k) (hk : k ≤ 2*s.card) : k ≤ D := by omega
    have hd (k) (hk : k ≤ 2*s.card) : Integrable (fun x => x^k * (b.out a x - c.out a' x)) μ := by
      simp_rw [mul_sub]
      exact (b.integrable_out a μ k (hi k (hki k hk))).sub (c.integrable_out a' μ k (hi k (hki k hk)))
    have hz (k) (hk : k ≤ 2*s.card) : ∫ x, x^k * (b.out a x - c.out a' x) ∂μ = 0 := by
      simp_rw [mul_sub]
      rw [integral_sub (b.integrable_out a μ k (hi k (hki k hk))) (c.integrable_out a' μ k (hi k (hki k hk)))]
      exact sub_eq_zero.mpr (h _ (hki _ hk))
    have hr := zero_of_moments μ _ ((b.continuous_out a).sub (c.continuous_out a')) s hs hd hz
    funext x
    exact sub_eq_zero.mp (congrFun hr x)
  · intro he k _
    rw [he]

def faceBound (h : ℕ) : ℕ := 4^(2*h+1)
def laplaceDegree (h : ℕ) : ℕ := let N := faceBound h; N*(2*N+1)-1
def gaussianDegree (h : ℕ) : ℕ := let S := 2*faceBound h; S*(S-1)/2+S-1

theorem display_degrees {n m h : ℕ} (hn : n ≤ h) (hm : m ≤ h) :
    2*(2^n+2^m+2^n*2^m) ≤ laplaceDegree h ∧ 2*(2^n+2^m+2^n*2^m) ≤ gaussianDegree h := by
  let t : ℕ := 4^h
  let N := faceBound h
  have h1 : 1 ≤ t := Nat.one_le_pow _ _ (by decide)
  have hbase : 2^h ≤ t := Nat.pow_le_pow_left (by decide) _
  have hₙ := (Nat.pow_le_pow_right (by decide : 0 < 2) hn).trans hbase
  have hₘ := (Nat.pow_le_pow_right (by decide : 0 < 2) hm).trans hbase
  have hN : N = 4*t*t := by simp [N,faceBound,t,pow_succ,Nat.mul_comm 2 h,pow_mul]; ring
  have hNN : 0 < N := by dsimp [N,faceBound]; positivity
  have hc : 2^n+2^m+2^n*2^m ≤ N := by
    rw [hN]
    nlinarith only [hₙ,hₘ,Nat.mul_le_mul hₙ hₘ,Nat.mul_le_mul h1 h1,Nat.mul_le_mul_left t h1]
  change _ ≤ N*(2*N+1)-1 ∧ _ ≤ (2*N)*(2*N-1)/2+2*N-1
  have hp : 2 ≤ (2*N)*(2*N-1) := by
    have h2 : 1 ≤ 2*N-1 := by omega
    nlinarith only [Nat.mul_le_mul (show 2 ≤ 2*N by omega) h2]
  have hq : 1 ≤ (2*N)*(2*N-1)/2 := by omega
  have hr : 2*N+1 ≤ N*(2*N+1) := by nlinarith only [Nat.mul_le_mul_right (2*N+1) (show 1≤N by omega)]
  omega

end ReluMoments
