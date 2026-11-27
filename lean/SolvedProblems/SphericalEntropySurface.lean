module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

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
