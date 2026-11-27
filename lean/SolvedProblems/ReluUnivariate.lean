module

public import SolvedProblems.ReluLineRegions
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

open MeasureTheory Polynomial
open scoped Polynomial

namespace ReluMoments

/-- Ordinary monomial moments through twice the number of sign cuts determine
a continuous function with these sign cuts under any full-support input law. -/
theorem zero_of_moments (μ : Measure ℝ) [μ.IsOpenPosMeasure] (g : ℝ → ℝ) (hg : Continuous g)
    (s : Finset ℝ) (hs : ∀ x y, SameCell s x y → 0 ≤ g x*g y)
    (hi : ∀ k ≤ 2*s.card, Integrable (fun x => x^k * g x) μ)
    (hz : ∀ k ≤ 2*s.card, ∫ x, x^k * g x ∂μ = 0) : g = 0 := by
  classical
  obtain ⟨q,hd,hroots,hpos,_⟩ := exists_sign_polynomial s g hs
  let v (k : ℕ) (x : ℝ) := q.coeff k * (x^k * g x)
  let indices := Finset.range (q.natDegree+1)
  have hki (k) (hk : k ∈ indices) : k ≤ 2*s.card := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hd
  have hvi (k) (hk : k ∈ indices) : Integrable (v k) μ := (hi k (hki k hk)).const_mul _
  have heq (x : ℝ) : q.eval x * g x = ∑ k ∈ indices, v k x := by
    simp only [indices,v,q.eval_eq_sum_range x,Finset.sum_mul,mul_assoc]
  have hqi : Integrable (fun x => q.eval x * g x) μ := by
    simp_rw [heq]
    exact integrable_finsetSum _ hvi
  have hqz : (∫ x, q.eval x * g x ∂μ) = 0 := by
    simp_rw [heq]
    rw [integral_finsetSum _ hvi]
    apply Finset.sum_eq_zero
    intro k hk
    rw [show (∫ x, v k x ∂μ) = q.coeff k * ∫ x, x^k * g x ∂μ from integral_const_mul _ _,hz k (hki k hk),mul_zero]
  have hall (x : ℝ) : q.eval x * g x = 0 := by
    by_contra hne
    have h := integral_pos_of_integrable_nonneg_nonzero (q.continuous.mul hg) hqi hpos hne
    exact (ne_of_gt h) hqz
  apply Continuous.ext_on (dense_univ.sdiff_finset s) hg continuous_const
  intro x hx
  exact (mul_eq_zero.mp (hall x)).resolve_left (fun h => hx.2 ((hroots x).mp h))

noncomputable def Network.realize {p : ℕ} (f : Network 1 p) (θ : Vector p) (x : ℝ) : ℝ :=
  f.eval θ (fun _ => x)

theorem Network.continuous_realize {p : ℕ} (f : Network 1 p) (θ : Vector p) : Continuous (f.realize θ) :=
  (f.continuous_input θ).comp (continuous_pi fun _ => continuous_id)

theorem Network.integrable_realize {p : ℕ} (f : Network 1 p) (θ : Vector p) (μ : Measure ℝ)
    (k : ℕ) (hi : Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ) :
    Integrable (fun x => x^k * f.realize θ x) μ := by
  obtain ⟨C,hC,h₀,_⟩ := f.envelope (R:=1+‖θ‖) (by simp)
  apply (hi.const_mul C).mono' ((continuous_id.pow k).mul (f.continuous_realize θ)).aestronglyMeasurable
  filter_upwards with x
  have hh := h₀ θ (by linarith) (fun _ => x)
  simp only [pi_norm_const, Real.norm_eq_abs] at hh
  change |x^k * f.realize θ x| ≤ _
  rw [abs_mul,abs_pow]
  calc _ ≤ |x|^k * (C*(1+|x|)) := mul_le_mul_of_nonneg_left hh (by positivity)
       _ = _ := by ring

/-- A uniform moment-degree bound for two arbitrary fixed scalar architectures
on the real line. All members of both architectures are quantified, including
degenerate parameters. Positive support promotes the conclusion to all inputs. -/
theorem univariate_identification {p r : ℕ} (f : Network 1 p) (g : Network 1 r)
    (μ : Measure ℝ) [μ.IsOpenPosMeasure]
    (hi : ∀ k ≤ 2*f.pairCutBound g, Integrable (fun x : ℝ => |x|^k * (1+|x|)) μ)
    (θ : Vector p) (η : Vector r) :
    (∀ k ≤ 2*f.pairCutBound g, (∫ x, x^k * f.realize θ x ∂μ) = ∫ x, x^k * g.realize η x ∂μ) ↔
      f.realize θ = g.realize η := by
  constructor
  · intro h
    obtain ⟨s,hcard,hs⟩ := f.sign_cuts g θ η
    have hki (k) (hk : k ≤ 2*s.card) : k ≤ 2*f.pairCutBound g := by omega
    have hd (k) (hk : k ≤ 2*s.card) : Integrable (fun x => x^k * (f.realize θ x - g.realize η x)) μ := by
      simp_rw [mul_sub]
      exact (f.integrable_realize θ μ k (hi k (hki k hk))).sub (g.integrable_realize η μ k (hi k (hki k hk)))
    have hz (k) (hk : k ≤ 2*s.card) : ∫ x, x^k * (f.realize θ x - g.realize η x) ∂μ = 0 := by
      simp_rw [mul_sub]
      rw [integral_sub (f.integrable_realize θ μ k (hi k (hki k hk))) (g.integrable_realize η μ k (hi k (hki k hk)))]
      exact sub_eq_zero.mpr (h _ (hki _ hk))
    have hr := zero_of_moments μ _ ((f.continuous_realize θ).sub (g.continuous_realize η)) s hs hd hz
    funext x
    exact sub_eq_zero.mp (congrFun hr x)
  · intro he k _
    rw [he]

end ReluMoments
