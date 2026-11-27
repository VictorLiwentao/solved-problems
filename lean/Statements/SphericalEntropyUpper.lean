module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Spherical cross-entropy and the normalized exponential pair kernel. -/

open MeasureTheory Set Metric
open scoped Pointwise RealInnerProductSpace ENNReal

namespace SphericalEntropy

abbrev Ambient (s : ℕ) := EuclideanSpace ℝ (Fin (s+1))
abbrev Sphere (s : ℕ) := sphere (0 : Ambient s) 1

noncomputable def surface (s : ℕ) : Measure (Sphere s) :=
  ((volume : Measure (Ambient s)).toSphere univ)⁻¹ • volume.toSphere

instance surface_probability (s : ℕ) : IsProbabilityMeasure (surface s) := by
  constructor
  let μ := (volume : Measure (Ambient s)).toSphere
  have hμ : μ univ ≠ 0 := fun h => (Measure.toSphere_ne_zero _) (Measure.measure_univ_eq_zero.mp h)
  exact (Measure.smul_apply _ _ _).trans (ENNReal.inv_mul_cancel hμ (measure_ne_top _ _))

theorem sphere_norm {s} (x : Sphere s) : ‖x.val‖=1 := mem_sphere_zero_iff_norm.mp x.property

noncomputable def rotation {s} (R : Ambient s ≃ₗᵢ[ℝ] Ambient s) (x : Sphere s) : Sphere s :=
  ⟨R x.val,mem_sphere_zero_iff_norm.mpr ((R.norm_map _).trans (sphere_norm x))⟩

theorem rotation_continuous {s} (R : Ambient s ≃ₗᵢ[ℝ] Ambient s) : Continuous (rotation R) :=
  (R.continuous.comp continuous_subtype_val).subtype_mk _

theorem rotation_surface {s} (R : Ambient s ≃ₗᵢ[ℝ] Ambient s) :
    MeasurePreserving (rotation R) (surface s) (surface s) := by
  have hm := (rotation_continuous R).measurable
  refine ⟨hm,?_⟩
  ext U hU
  rw [Measure.map_apply hm hU,surface,Measure.smul_apply,Measure.smul_apply,
    Measure.toSphere_apply' _ (hm hU),Measure.toSphere_apply' _ hU]
  congr 2
  let cone (T : Set (Sphere s)) := Ioo (0:ℝ) 1 • (Subtype.val '' T)
  have heq : cone ((rotation R) ⁻¹' U) = R ⁻¹' cone U := by
    ext x
    constructor
    · rintro ⟨r,hr,_,⟨u,hu,rfl⟩,rfl⟩
      exact ⟨r,hr,_,⟨rotation R u,hu,rfl⟩,(R.map_smul r u.val).symm⟩
    · rintro ⟨r,hr,_,⟨u,hu,rfl⟩,he⟩
      refine ⟨r,hr,_,⟨rotation R.symm u,?_,rfl⟩,?_⟩
      · simpa [rotation] using hu
      · apply R.injective
        simpa [rotation] using he
  change volume (cone ((rotation R) ⁻¹' U)) = volume (cone U)
  rw [heq]
  exact R.measurePreserving.measure_preimage_emb R.toHomeomorph.measurableEmbedding _

noncomputable def kernel {s} (α : ℝ) (x y : Sphere s) : ℝ := Real.exp (α * ⟪x.val,y.val⟫)

theorem kernel_continuous {s} (α : ℝ) (x : Sphere s) : Continuous (kernel α x) := by
  unfold kernel
  fun_prop

noncomputable def partition {s} (α : ℝ) (x : Sphere s) : ℝ :=
  ∫ y, kernel α x y ∂(surface s)

theorem partition_invariant {s} (α : ℝ) (x z : Sphere s) : partition α x = partition α z := by
  let R : Ambient s ≃ₗᵢ[ℝ] Ambient s := (ℝ ∙ (x.val-z.val))ᗮ.reflection
  have hx : R x.val=z.val := Submodule.reflection_sub ((sphere_norm x).trans (sphere_norm z).symm)
  have hker (y : Sphere s) : kernel α z (rotation R y) = kernel α x y := by
    simp [kernel,rotation,←hx,R.inner_map_map]
  unfold partition
  calc (∫ y, kernel α x y ∂(surface s)) = ∫ y, kernel α z (rotation R y) ∂(surface s) := by simp_rw [hker]
       _ = _ := by
         have hm := rotation_surface R
         rw [← integral_map hm.measurable.aemeasurable (kernel_continuous α z).aestronglyMeasurable,hm.map_eq]

theorem inner_bound {s} (x y : Sphere s) : |⟪x.val,y.val⟫| ≤ 1 := by
  simpa [sphere_norm] using abs_real_inner_le_norm x.val y.val

theorem partition_pos {s} (α : ℝ) (x : Sphere s) : 0<partition α x := by
  unfold partition
  have hi : Integrable (kernel α x) (surface s) := (kernel_continuous α x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le) hi).mpr
  have hs : Function.support (kernel α x) = univ := Set.eq_univ_iff_forall.mpr fun _ => (Real.exp_pos _).ne'
  change 0 < (surface s) (Function.support (kernel α x))
  simp [hs]

end SphericalEntropy

open Finset

namespace SphericalEntropy

noncomputable def taylor (k : ℕ) (u : ℝ) := ∑ j ∈ range k, u^j / j.factorial

theorem taylor_error {α u : ℝ} (hu : |u|≤α) (k : ℕ) :
    |Real.exp u - taylor k u| ≤ α^k/(k.factorial:ℝ)*Real.exp α := by
  have ha : 0≤α := (abs_nonneg u).trans hu
  have hs (x:ℝ) : HasSum (fun n : ℕ => x^n/(n.factorial:ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hu' := (hs u).summable.sum_add_tsum_nat_add k
  rw [(hs u).tsum_eq] at hu'
  have htail : Real.exp u - taylor k u = ∑' i : ℕ, u^(i+k)/((i+k).factorial:ℝ) := by unfold taylor; linarith
  rw [htail,←Real.norm_eq_abs]
  let m (i : ℕ) := α^k/(k.factorial:ℝ)*(α^i/(i.factorial:ℝ))
  have hm : HasSum m (α^k/(k.factorial:ℝ)*Real.exp α) := (hs α).mul_left _
  have hb (i : ℕ) : ‖u^(i+k)/((i+k).factorial:ℝ)‖ ≤ m i := by
    have hden : |((i+k).factorial:ℝ)| = ((i+k).factorial:ℝ) := abs_of_nonneg (by positivity)
    rw [Real.norm_eq_abs,abs_div,abs_pow,hden]
    have hfac : (i.factorial:ℝ)*k.factorial ≤ (i+k).factorial := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add i k)
    have hpower := pow_le_pow_left₀ (abs_nonneg u) hu (i+k)
    calc _ ≤ α^(i+k)/((i+k).factorial:ℝ) := div_le_div_of_nonneg_right hpower (by positivity)
         _ ≤ α^(i+k)/((i.factorial:ℝ)*k.factorial) := div_le_div_of_nonneg_left (pow_nonneg ha _) (by positivity) hfac
         _ = _ := by rw [pow_add]; unfold m; ring
  have hnorm := hm.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hb hm.summable).trans_eq hm.tsum_eq)

end SphericalEntropy

open Finset MeasureTheory
open scoped RealInnerProductSpace

namespace SphericalEntropy

noncomputable def mean {N : ℕ} (v : Fin (N+1) → ℝ) := (N+1:ℝ)⁻¹ * ∑ i, v i

@[simp] theorem mean_const (N : ℕ) (a : ℝ) : mean (fun _ : Fin (N+1) => a) = a := by
  simp [mean,←mul_assoc,inv_mul_cancel₀ (show (N+1:ℝ)≠0 by positivity)]

theorem mean_mono {N : ℕ} {f g : Fin (N+1) → ℝ} (h : ∀ i, f i≤g i) : mean f≤mean g :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => h i) (by positivity)

theorem mean_sub {N : ℕ} (f g : Fin (N+1) → ℝ) : mean (fun i => f i-g i) = mean f - mean g := by
  simp [mean,sum_sub_distrib,mul_sub]

theorem abs_mean_le {N : ℕ} {f : Fin (N+1) → ℝ} {a : ℝ} (h : ∀ i, |f i|≤a) : |mean f|≤a := by
  apply abs_le.mpr
  constructor
  · simpa using (mean_mono fun i => (abs_le.mp (h i)).1)
  · simpa using (mean_mono fun i => (abs_le.mp (h i)).2)

noncomputable def averageKernel {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) (x : Sphere s) : ℝ :=
  mean (fun i => kernel α x (X i)) / partition α x

noncomputable def energyGap {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) : ℝ :=
  mean (fun i => averageKernel α X (X i)) - 1

noncomputable def lossGap {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) : ℝ :=
  mean (fun i => Real.log (averageKernel α X (X i)))

theorem averageKernel_pos {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) (x) : 0<averageKernel α X x := by
  unfold averageKernel mean
  apply div_pos _ (partition_pos _ _)
  apply mul_pos (by positivity)
  exact sum_pos (fun i _ => Real.exp_pos _) univ_nonempty

/-- The tangent line to log at one bounds tied cross-entropy by its quadratic pair energy. -/
theorem loss_le_energy {s N} (α : ℝ) (X : Fin (N+1) → Sphere s) : lossGap α X ≤ energyGap α X := by
  have h := mean_mono fun i => Real.log_le_sub_one_of_pos (averageKernel_pos α X (X i))
  simpa [lossGap,energyGap,mean_sub] using h

/-- Equal-weight nodes integrate every ambient polynomial of degree at most t
exactly against normalized spherical surface measure. -/
def IsDesign {s N} (t : ℕ) (X : Fin (N+1) → Sphere s) : Prop :=
  ∀ p : MvPolynomial (Fin (s+1)) ℝ, p.totalDegree≤t →
    mean (fun i => MvPolynomial.eval (X i).val p) =
      ∫ y : Sphere s, MvPolynomial.eval y.val p ∂(surface s)

noncomputable def dotPolynomial {s} (α : ℝ) (x : Sphere s) : MvPolynomial (Fin (s+1)) ℝ :=
  ∑ i, MvPolynomial.C (α*x.val i)*MvPolynomial.X i

theorem dotPolynomial_degree {s} (α : ℝ) (x : Sphere s) : (dotPolynomial α x).totalDegree≤1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X])

theorem dotPolynomial_eval {s} (α : ℝ) (x y : Sphere s) :
    MvPolynomial.eval y.val (dotPolynomial α x) = α*⟪x.val,y.val⟫ := by
  simp [dotPolynomial,PiLp.inner_apply,mul_sum,mul_assoc,mul_comm (x.val _) (y.val _)]

noncomputable def taylorPolynomial {s} (k : ℕ) (α : ℝ) (x : Sphere s) : MvPolynomial (Fin (s+1)) ℝ :=
  ∑ j ∈ range k, MvPolynomial.C ((j.factorial:ℝ)⁻¹) * (dotPolynomial α x)^j

theorem taylorPolynomial_degree {s} (t : ℕ) (α : ℝ) (x : Sphere s) :
    (taylorPolynomial (t+1) α x).totalDegree ≤ t := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  exact (MvPolynomial.totalDegree_pow ..).trans ((Nat.mul_le_mul_left j (dotPolynomial_degree α x)).trans (by simpa using Nat.le_of_lt_succ (mem_range.mp hj)))

theorem taylorPolynomial_eval {s} (k : ℕ) (α : ℝ) (x y : Sphere s) :
    MvPolynomial.eval y.val (taylorPolynomial k α x) = taylor k (α*⟪x.val,y.val⟫) := by
  simp [taylorPolynomial,taylor,dotPolynomial_eval,div_eq_inv_mul]

end SphericalEntropy

open Finset MeasureTheory
open scoped RealInnerProductSpace

namespace SphericalEntropy

theorem design_potential {s N t} {α : ℝ} (ha : 0≤α) (X : Fin (N+1) → Sphere s) (hd : IsDesign t X)
    (x : Sphere s) :
    |averageKernel α X x - 1| ≤
      2*(α^(t+1)/((t+1).factorial:ℝ)*Real.exp α)/partition α x := by
  let k := t+1
  let P (y : Sphere s) := taylor k (α*⟪x.val,y.val⟫)
  let err := α^k/(k.factorial:ℝ)*Real.exp α
  have hex : mean (fun i => P (X i)) = ∫ y, P y ∂(surface s) := by
    simpa [taylorPolynomial_eval,P,k] using hd (taylorPolynomial k α x) (taylorPolynomial_degree t α x)
  have he (y : Sphere s) : |kernel α x y - P y|≤err := by
    apply taylor_error
    rw [abs_mul,abs_of_nonneg ha]
    exact mul_le_of_le_one_right ha (inner_bound x y)
  have hmc := abs_mean_le fun i => he (X i)
  rw [mean_sub,hex] at hmc
  have hcont : Continuous P := by unfold P taylor; fun_prop
  have hk := (kernel_continuous α x).integrable_of_hasCompactSupport (μ:=surface s) (HasCompactSupport.of_compactSpace _)
  have hp := hcont.integrable_of_hasCompactSupport (μ:=surface s) (HasCompactSupport.of_compactSpace _)
  have hi := norm_integral_le_of_norm_le_const (μ:=surface s) (f:=fun y => kernel α x y-P y) (Filter.Eventually.of_forall fun y =>
    (show ‖kernel α x y-P y‖≤err by simpa [Real.norm_eq_abs] using he y))
  rw [integral_sub hk hp,Real.norm_eq_abs,(show (surface s).real Set.univ=1 by simp),mul_one,abs_sub_comm] at hi
  have hpair := abs_sub_le (mean fun i => kernel α x (X i)) (∫ y, P y ∂surface s) (partition α x)
  have ht : |(mean fun i => kernel α x (X i))-partition α x|≤2*err := by
    unfold partition at hpair ⊢
    linarith
  unfold averageKernel
  rw [div_sub_one (partition_pos _ _).ne',abs_div,abs_of_pos (partition_pos _ _)]
  exact div_le_div_of_nonneg_right ht (partition_pos _ _).le

/-- The simultaneous factorial upper bound on the empirical quadratic and
cross-entropy gaps of any actual equal-weight spherical design. -/
theorem design_gaps {s N t} {α : ℝ} (ha : 0≤α) (X : Fin (N+1) → Sphere s) (hd : IsDesign t X)
    (x : Sphere s) :
    lossGap α X ≤ energyGap α X ∧
      |energyGap α X| ≤ 2*(α^(t+1)/((t+1).factorial:ℝ)*Real.exp α)/partition α x := by
  refine ⟨loss_le_energy ..,?_⟩
  have h := abs_mean_le fun i => (design_potential ha X hd (X i)).trans_eq (by rw [partition_invariant α (X i) x])
  simpa [energyGap,mean_sub] using h

end SphericalEntropy

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

open Filter Real

namespace SphericalEntropy

/-- The exact-cardinality existence theorem for spherical designs used by
Bondarenko, Radchenko and Viazovska, stated separately from the rate. -/
def DesignExistence (s : ℕ) : Prop :=
  ∃ C : ℕ, 0<C ∧ ∀ t N : ℕ, C*t^s≤N+1 → ∃ X : Fin (N+1) → Sphere s, IsDesign t X

theorem upper_rate {s : ℕ} (hs : 0<s) (designs : DesignExistence s) {α : ℝ} (ha : 0<α) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, ∃ X : Fin (N+1) → Sphere s,
      lossGap α X ≤ energyGap α X ∧
        |energyGap α X| ≤ exp (-c*(N+1:ℝ)^((s:ℝ)⁻¹)*log (N+1)) := by
  classical
  obtain ⟨C,hC,hex⟩ := designs
  obtain ⟨c,hc,hdeg⟩ := choose_degree hs hC
  obtain ⟨sample,_⟩ := hex 0 0 (by simp [Nat.zero_pow hs])
  let x := sample 0
  let B := 2*exp α/partition α x
  have hB : 0<B := div_pos (by positivity) (partition_pos _ _)
  obtain ⟨A,hfac⟩ := eventually_atTop.mp (factorial_rate ha hB)
  refine ⟨c,hc,?_⟩
  filter_upwards [hdeg A] with N hN
  obtain ⟨t,ht,hsize,hscale⟩ := hN
  obtain ⟨X,hd⟩ := hex t N hsize
  obtain ⟨hle,henergy⟩ := design_gaps ha.le X hd x
  refine ⟨X,hle,henergy.trans (le_trans ?_ (exp_le_exp.mpr hscale))⟩
  have h := hfac (t+1) ht
  have he : 2*(α^(t+1)/((t+1).factorial:ℝ)*exp α)/partition α x = B*α^(t+1)/((t+1).factorial:ℝ) := by
    unfold B
    ring
  simpa [he] using h

end SphericalEntropy
