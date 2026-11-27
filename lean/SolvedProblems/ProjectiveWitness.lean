module

public import SolvedProblems.ProjectiveGeometry
public import SolvedProblems.ProjectivePowerCodes
public import SolvedProblems.ProjectiveNecessity

@[expose] public section

namespace ProjectiveSupports

open ProjectiveAlgebraic ProjectiveTransfer ProjectiveIndiscernibles Set Function

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- Necessity in the finite point-support permutation interpretation. The
hypothesis concerns a supported noninjective surjection on a power of the
actual internal power set. Its graph supplies a supported nondegenerate,
locally finite, locally homogeneous pregeometry on the atoms. -/
theorem supportedNecessity (am : Amorphous G) {k : ℕ} (F : (Fin k → Power G) → (Fin k → Power G))
    (hs : ∃ E, SupportedPowerMap G F E) (surj : Surjective F) (collides : ¬ Injective F) :
    ∃ cl : Set A → Set A, Geometry G cl := by
  classical
  let := am.1
  obtain ⟨E,hE⟩ := hs
  let e := powersEquiv G am k
  let f (x : Codes A k) := e.symm (F (e x))
  have support : SupportedCodeMap G f E := supports_conjugate G am F E hE
  have onto : Surjective f := e.symm.surjective.comp (surj.comp e.surjective)
  have collision : ¬ Injective f := by
    intro inj
    apply collides
    intro a b eq
    have h : f (e.symm a) = f (e.symm b) := by simp [f,eq]
    exact e.symm.injective (inj h)
  let := graphStructure f
  have act : SupportedStructure G (graphLanguage k) E := graph_supported G f E support
  obtain ⟨fin,min⟩ := structure_properties G am E act
  obtain ⟨ext,mono,idem,fc,lf,exchange⟩ := pregeometry fin min
  have nondeg := nondegenerateClosure k f fin min onto collision
  unfold Degenerate at nondeg
  push Not at nondeg
  refine ⟨acl (graphLanguage k),⟨E,?_⟩,ext,mono,idem,fc,lf,exchange,nondeg,localHomogeneity fin min⟩
  intro σ hg fix S
  obtain ⟨p,rfl⟩ := act σ hg fix
  exact acl_image fin p S

end ProjectiveSupports
