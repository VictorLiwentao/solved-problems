module

public import SolvedProblems.ProjectivePowerCodes

public section

namespace ProjectiveSupports

open ProjectiveTransfer ProjectiveAlgebraic

/-- A supported self-map on the actual internal power set of amorphous atoms
has a coded first-order graph with finite spectra in every finite arity and
finite/cofinite unary definable sets over all finite parameter tuples. -/
theorem powerStructureProperties {A : Type*} (G : Subgroup (Equiv.Perm A)) (am : Amorphous G) {k : ℕ}
    (F : (Fin k → Power G) → (Fin k → Power G)) (E : Finset A) (h : SupportedPowerMap G F E) :
    let e := powersEquiv G am k
    letI := graphStructure (fun x => e.symm (F (e x)))
    FiniteTypes (graphLanguage k) A ∧ Minimal (graphLanguage k) A := by
  let e := powersEquiv G am k
  let f (x : Codes A k) := e.symm (F (e x))
  let := graphStructure f
  exact structure_properties G am E (graph_supported G f E (supports_conjugate G am F E h))

end ProjectiveSupports
