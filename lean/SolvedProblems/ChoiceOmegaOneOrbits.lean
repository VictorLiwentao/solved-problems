module

public import SolvedProblems.ChoiceOmegaOneAssembly
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Filter Order

variable {I : Type u} {P : Type v} [Group P] [Finite P] {V : Type w} [MulAction (I → P) V]

/-- Every countable orbit of a full power of a finite perfect group is
controlled by finitely many ultrafilters on its coordinate set. -/
theorem descriptors_of_perfect (perfect : commutator P = ⊤) : OrbitDescriptors (I := I) (P := P) (V := V) := by
  intro x cnt
  apply finite_descriptors (supportFilter (P := P) x)
  rintro ⟨s,apart,pos⟩
  obtain ⟨w⟩ := witness_of_disjoint perfect s apart x pos
  exact witness_uncountable w cnt

/-- An ultrafilter on a finite palette selects a unique large fiber.
Here all choices and all ultrafilters live in the ground universe. -/
private def readAt (U : Ultrafilter I) (g : I→P) : P := (Ultrafilter.eq_pure_of_finite (U.map g)).choose

omit [Group P] in
private theorem large_value (U : Ultrafilter I) (g : I→P) : {i | g i = readAt U g} ∈ U := by
  have e := (Ultrafilter.eq_pure_of_finite (U.map g)).choose_spec
  apply (Ultrafilter.mem_map (m := g) (s := {readAt U g})).mp
  rw [e]; exact Ultrafilter.mem_pure.mpr rfl

/-- In fact every countable orbit is finite. Equal evaluations at all the
point's controlling ultrafilters imply equal images of the point. -/
theorem countable_orbit_finite (perfect : commutator P = ⊤) (x : V) (cnt : Countable (MulAction.orbit (I→P) x)) :
    Finite (MulAction.orbit (I→P) x) := by
  classical
  obtain ⟨filters,desc⟩ := descriptors_of_perfect perfect x cnt
  let O := MulAction.orbit (I→P) x
  have moved (z : O) : ∃ g : I→P, g • x = z.val := MulAction.mem_orbit_iff.1 z.property
  choose rep hrep using moved
  let code (z : O) (U : filters) := readAt U.val (rep z)
  apply Finite.of_injective code
  intro z t eq
  let D := {i : I | rep z i = rep t i}
  have agree (U : filters) : D ∈ U.val := by
    have e := congrFun eq U
    have both := inter_mem (large_value U.val (rep z)) (large_value U.val (rep t))
    exact mem_of_superset both (fun i hi => hi.1.trans (e.trans hi.2.symm))
  have holds := (desc D).mpr (fun U hu => agree ⟨U,hu⟩)
  have fixed := holds ((rep t)⁻¹ * rep z) (fun i hi => by change (rep t i)⁻¹ * rep z i = 1; rw [show rep z i = rep t i from hi,inv_mul_cancel])
  have image : rep z • x = rep t • x := by
    rw [mul_smul] at fixed
    exact inv_smul_eq_iff.mp fixed
  exact Subtype.ext ((hrep z).symm.trans (image.trans (hrep t)))

/-- Unconditional comparability on every supported carrier for the finite
perfect product with the nonstationary ideal of supports. -/
theorem comparison_of_perfect (rank : I → Row) (perfect : commutator P = ⊤)
    (points : AtomSupports (P := P) (V := V) rank) : ComparableAtOmegaOne (P := P) (V := V) rank :=
  comparison_from_descriptors rank points (descriptors_of_perfect perfect)

end ChoiceOmegaOne
