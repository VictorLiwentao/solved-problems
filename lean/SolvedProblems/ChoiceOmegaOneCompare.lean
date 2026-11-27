module

public import SolvedProblems.ChoiceOmegaOneUltra
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Pi.Basic

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Cardinal Ordinal Order Filter

variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V]

/-- A point in a residual row action is fixed by the full product on
the complement of the indicated coordinates. -/
def PointSupport (T : Set I) (x : V) : Prop := ∀ g : I → P, (∀ i ∈ T, g i = 1) → g • x = x

def AtomSupports (rank : I → Row) : Prop :=
  ∀ x : V, ∃ D, Small D ∧ PointSupport (P := P) (rank ⁻¹' D) x

/-- All allowed supports for the point, including large subsets of the residual
rows, are determined by finitely many ground-model ultrafilters. -/
def OrbitDescriptors : Prop := ∀ x : V, Countable (MulAction.orbit (I → P) x) →
  ∃ F : Finset (Ultrafilter I), ∀ T : Set I, PointSupport (P := P) T x ↔ ∀ U ∈ F, T ∈ U

/-- One of the two ambient injections has a supported graph. For injections to
the pure naturals, graph invariance is equivalent to fixing every argument. -/
def ComparableAtOmegaOne (rank : I → Row) : Prop :=
  (∃ (e : V ↪ ℕ) (D : Set Row), Small D ∧ ∀ g : I → P, (∀ i ∈ rank ⁻¹' D, g i = 1) → ∀ x, e (g • x) = e x) ∨
  (∃ (e : Row ↪ V) (D : Set Row), Small D ∧ ∀ a, PointSupport (P := P) (rank ⁻¹' D) (e a))

theorem row_embedding {Y : Type w} (h : ¬ Countable Y) : Nonempty (Row ↪ Y) := by
  apply Cardinal.lift_mk_le.{0}.mp
  have large : ℵ₁ ≤ #Y := Cardinal.aleph_one_le_iff.mpr (lt_of_not_ge (fun e => h (Cardinal.mk_le_aleph0_iff.mp e)))
  simpa [Row] using large

/-- All the points of each orbit share the support of any one representative,
since the subgroup fixing a given set of complete rows is normal. -/
theorem support_orbit {T : Set I} {x : V} (hx : PointSupport (P := P) T x) {y : V}
    (hy : y ∈ MulAction.orbit (I → P) x) : PointSupport (P := P) T y := by
  obtain ⟨k,rfl⟩ := MulAction.mem_orbit_iff.mp hy
  intro g hg
  have h : ∀ i ∈ T, (k⁻¹ * g * k) i = 1 := by
    intro i hi; simp [hg i hi]
  have e := congrArg (fun y : V => k • y) (hx _ h)
  simpa only [← mul_smul,mul_inv_cancel_left,mul_assoc,mul_inv_cancel,one_mul] using e

/-- The manuscript's comparison argument for every hereditary object carrier.
The index set can be any residual set of rows of a supported parent. Large
orbits use normality; in the countable-orbit case the club thinning supplies
one support for an ω₁-indexed family of distinct points. -/
theorem comparison_from_descriptors (rank : I → Row) (points : AtomSupports (P := P) (V := V) rank)
    (describes : OrbitDescriptors (P := P) (I := I) (V := V)) :
    ComparableAtOmegaOne (P := P) (V := V) rank := by
  classical
  by_cases cnt : Countable V
  · let _ := cnt
    obtain ⟨f,inj⟩ := Countable.exists_injective_nat V
    choose D small fix using points
    refine Or.inl ⟨⟨f,inj⟩,⋃ x, D x,small_countable_union D small,?_⟩
    intro g hg x
    exact congrArg f (fix x g (fun i hi => hg i (Set.mem_iUnion.2 ⟨x,hi⟩)))
  by_cases all : ∀ x : V, Countable (MulAction.orbit (I → P) x)
  · obtain ⟨f⟩ := row_embedding cnt
    choose F describe using fun a : Row => describes (f a) (all _)
    have each (a : Row) : ∃ D : Set Row, Small D ∧ ∀ U ∈ F a, rank ⁻¹' D ∈ U := by
      obtain ⟨D,small,fix⟩ := points (f a)
      exact ⟨D,small,(describe a _).mp fix⟩
    obtain ⟨J,D,cof,small,agree⟩ := thin_ultrafilters rank F each
    let e := ((Order.enum J cof).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)).trans f
    exact Or.inr ⟨e,D,small,fun a => (describe _ _).mpr (agree _ (Order.enum J cof a).property)⟩
  · obtain ⟨x,big⟩ := not_forall.mp all
    obtain ⟨f⟩ := row_embedding big
    obtain ⟨D,small,fix⟩ := points x
    exact Or.inr ⟨f.trans (Function.Embedding.subtype _),D,small,fun a => support_orbit fix (f a).property⟩

end ChoiceOmegaOne
