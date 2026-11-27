module

public import SolvedProblems.ReluStabilityNetwork

@[expose] public section

open SignType Set MeasureTheory

namespace ReluStability

/-- The finite exceptional polynomial hypersurfaces are read directly from
the architecture. All ternary sign cells, their closures, face incidences and
small inductive dimensions are simultaneously preserved by a continuously
varying ambient homeomorphism equal to the identity at the base parameter. -/
theorem stability {p d n : ℕ} (N : Model p d n) :
    ∃ polys : List (Coeff p), IsOpen (Good polys) ∧ Dense (Good polys) ∧
      (∀ᵐ θ : Params p ∂volume, θ ∈ Good polys) ∧
      ∀ θ ∈ Good polys, ∃ V : Set (Params p), IsOpen V ∧ θ ∈ V ∧
        ∃ H : Family V (Input d), (∀ b : V, b.val = θ → ∀ x, H.map b x = x) ∧
          ∀ b : V, (∀ x, N.word θ x = N.word b.val (H.map b x)) ∧
            (∀ s, H.map b '' N.cell θ s = N.cell b.val s ∧
              H.map b '' closure (N.cell θ s) = closure (N.cell b.val s) ∧
              smallInductiveDimension (N.cell θ s) = smallInductiveDimension (N.cell b.val s)) ∧
            ∀ s t, closure (N.cell θ s) ⊆ closure (N.cell θ t) ↔
              closure (N.cell b.val s) ⊆ closure (N.cell b.val t) := by
  obtain ⟨hop,hd,ha,hl⟩ := arrangement_stable N.tests
  refine ⟨discriminants d N.tests,hop,hd,ha,?_⟩
  intro θ hθ
  obtain ⟨V,hV,hmem,H,hH,hid⟩ := hl θ hθ
  refine ⟨V,hV,hmem,H,hid,?_⟩
  intro b
  have hw (x) : N.word θ x = N.word b.val (H.map b x) :=
    (N.aligned_words _ _ _ _ (fun f hf => hH b f hf x)).1
  have hi (s) : H.map b '' N.cell θ s = N.cell b.val s := by
    ext y
    obtain ⟨x,rfl⟩ := (H.map b).surjective y
    constructor
    · rintro ⟨x',hx',he'⟩
      obtain rfl := (H.map b).injective he'
      exact (hw x').symm.trans hx'
    · exact fun hx => ⟨x,(hw x).trans hx,rfl⟩
  have hcl (s) : H.map b '' closure (N.cell θ s) = closure (N.cell b.val s) := by
    rw [(H.map b).image_closure,hi]
  refine ⟨hw,fun s => ⟨hi s,hcl s,?_⟩,fun s t => ?_⟩
  · exact (((H.map b).isEmbedding.homeomorphImage _).trans (Homeomorph.setCongr (hi s))).smallInductiveDimension_congr
  · rw [←hcl,←hcl]
    exact (image_subset_image_iff (H.map b).injective).symm

end ReluStability
