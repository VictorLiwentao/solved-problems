module

public section

namespace OrdinalCube

/-- Classical truth values are available in ZF. Keeping this parameter explicit
allows Lean to audit the combinatorial construction independently of choice. -/
class TruthValues where
  truth (p : Prop) : Decidable p

scoped instance (priority := 10) (p : Prop) [TruthValues] : Decidable p := TruthValues.truth p

theorem truthCases [TruthValues] (p : Prop) : p ∨ ¬ p := @Decidable.em p (TruthValues.truth p)

end OrdinalCube
