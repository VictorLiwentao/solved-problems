module

public import SolvedProblems.ReluStabilityGeneric
public import SolvedProblems.ReluStabilityFamily
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open SignType Set Filter
open scoped Topology

namespace ReluStability

/-- An affine input form whose coefficients are polynomials in all network parameters. -/
structure Form (p d : ℕ) where
  bias : Coeff p
  weight : Fin d → Coeff p

noncomputable def Form.eval {p d : ℕ} (f : Form p d) (θ : Params p) (x : Input d) : ℝ :=
  MvPolynomial.eval θ f.bias + ∑ i, MvPolynomial.eval θ (f.weight i) * x i

theorem Form.continuous_eval {p d : ℕ} (f : Form p d) :
    Continuous (fun z : Params p × Input d => f.eval z.1 z.2) := by
  unfold eval
  exact (f.bias.continuous_eval.comp continuous_fst).add (continuous_finsetSum _ fun j _ =>
    ((f.weight j).continuous_eval.comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))

noncomputable def Form.scale {p d : ℕ} (a : Coeff p) (f : Form p d) : Form p d :=
  ⟨a*f.bias,fun i => a*f.weight i⟩

noncomputable def Form.sub {p d : ℕ} (f g : Form p d) : Form p d :=
  ⟨f.bias-g.bias,fun i => f.weight i-g.weight i⟩

def Form.tail {p d : ℕ} (f : Form p (d+1)) : Form p d :=
  ⟨f.bias,fun i => f.weight i.succ⟩

def Form.lead {p d : ℕ} (f : Form p (d+1)) := f.weight 0

noncomputable def Form.resultant {p d : ℕ} (f g : Form p (d+1)) : Form p d :=
  (g.tail.scale f.lead).sub (f.tail.scale g.lead)

theorem Form.eval_scale {p d : ℕ} (a : Coeff p) (f : Form p d) (θ : Params p) (x : Input d) :
    (f.scale a).eval θ x = MvPolynomial.eval θ a * f.eval θ x := by
  simp [eval,scale,mul_add,Finset.mul_sum,mul_assoc]

theorem Form.eval_sub {p d : ℕ} (f g : Form p d) (θ : Params p) (x : Input d) :
    (f.sub g).eval θ x = f.eval θ x - g.eval θ x := by
  simp only [sub,eval,map_sub,sub_mul,Finset.sum_sub_distrib]
  ring

theorem Form.eval_split {p d : ℕ} (f : Form p (d+1)) (θ : Params p) (x : Input (d+1)) :
    f.eval θ x = MvPolynomial.eval θ f.lead * x 0 + f.tail.eval θ (Fin.tail x) := by
  rw [eval,Fin.sum_univ_succ]
  dsimp [lead,tail,eval,Fin.tail]
  ring

noncomputable def Form.root {p d : ℕ} (f : Form p (d+1)) (θ : Params p) (x : Input d) : ℝ :=
  -f.tail.eval θ x / MvPolynomial.eval θ f.lead

theorem Form.root_sub {p d : ℕ} (f g : Form p (d+1)) (θ : Params p) (x : Input d)
    (hf : MvPolynomial.eval θ f.lead ≠ 0) (hg : MvPolynomial.eval θ g.lead ≠ 0) :
    f.root θ x - g.root θ x = (f.resultant g).eval θ x /
      (MvPolynomial.eval θ f.lead * MvPolynomial.eval θ g.lead) := by
  rw [root,root,resultant,eval_sub,eval_scale,eval_scale]
  field_simp
  ring

theorem Form.eval_from_root {p d : ℕ} (f : Form p (d+1)) (θ : Params p) (x : Input (d+1))
    (hf : MvPolynomial.eval θ f.lead ≠ 0) :
    f.eval θ x = MvPolynomial.eval θ f.lead * (x 0 - f.root θ (Fin.tail x)) := by
  rw [eval_split,root]
  field_simp
  ring

theorem sign_of_inverse (x : ℝ) : sign x⁻¹ = sign x := by
  rcases lt_trichotomy x 0 with h|rfl|h
  · rw [sign_neg h,sign_neg (inv_lt_zero.mpr h)]
  · simp
  · rw [sign_pos h,sign_pos (inv_pos.mpr h)]

theorem sign_quotient (x y : ℝ) : sign (x/y) = sign x * sign y := by
  rw [div_eq_mul_inv,sign_mul,sign_of_inverse]

theorem sign_sub_iff (a b c d : ℝ) :
    sign (a-b) = sign (c-d) ↔ ((a<b ↔ c<d) ∧ (a=b ↔ c=d)) := by
  constructor
  · intro h
    have hl (x y : ℝ) : x<y ↔ sign (x-y) = -1 := (sign_eq_neg_one_iff.trans sub_neg).symm
    have he (x y : ℝ) : x=y ↔ sign (x-y) = 0 := (sign_eq_zero_iff.trans sub_eq_zero).symm
    exact ⟨by rw [hl a b,hl c d,h],by rw [he a b,he c d,h]⟩
  · rintro ⟨hl,he⟩
    rcases lt_trichotomy a b with h|h|h
    · rw [sign_neg (sub_neg.mpr h),sign_neg (sub_neg.mpr (hl.mp h))]
    · rw [h,he.mp h]; simp
    · have h' := lt_of_le_of_ne (le_of_not_gt (mt hl.mpr h.not_gt)) (Ne.symm (mt he.mpr h.ne'))
      rw [sign_pos (sub_pos.mpr h),sign_pos (sub_pos.mpr h')]

noncomputable def projected {p d : ℕ} (fs : List (Form p (d+1))) : List (Form p d) :=
  fs.map Form.tail ++ fs.flatMap (fun f => fs.map (Form.resultant f))

noncomputable def discriminants {p : ℕ} : (d : ℕ) → List (Form p d) → List (Coeff p)
  | 0, fs => fs.map Form.bias
  | d+1, fs => fs.map Form.lead ++ discriminants d (projected fs)

theorem signs_near {p : ℕ} (fs : List (Coeff p)) {θ : Params p} (hθ : θ ∈ Good fs) :
    ∀ᶠ η in 𝓝 θ, ∀ q ∈ fs, sign (MvPolynomial.eval θ q) = sign (MvPolynomial.eval η q) := by
  induction fs with
  | nil => simp
  | cons q qs ih =>
    have htail := ih (fun f hf => hθ f (List.mem_cons_of_mem _ hf))
    by_cases hz : q = 0
    · simpa [hz] using htail
    have hx := hθ q (by simp) hz
    have hh : ∀ᶠ η in 𝓝 θ, sign (MvPolynomial.eval θ q) = sign (MvPolynomial.eval η q) := by
      rcases lt_or_gt_of_ne hx with hn|hp
      · filter_upwards [q.continuous_eval.continuousAt.eventually_lt continuousAt_const hn] with x hx
        rw [sign_neg hn,sign_neg hx]
      · filter_upwards [continuousAt_const.eventually_lt q.continuous_eval.continuousAt hp] with x hx
        rw [sign_pos hp,sign_pos hx]
    filter_upwards [hh,htail] with η h₁ h₂
    simpa [h₁] using h₂

end ReluStability
