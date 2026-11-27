module

public import SolvedProblems.ChoiceOmegaOneRows
public import SolvedProblems.ChoiceOmegaOneOrbits

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set

variable {P : Type u} [Group P] {A : Type v} [MulAction (Row→P) A]

/-- In the action of the ground universe, a set and each of its elements
are symmetric if their stabilizers include one of the allowed subgroups. -/
def SymmetricSet (X : Set A) : Prop := ∃ E : Set Row, Small E ∧
  ∀ g : Row→P, OnSupport E g → ∀ a, g • a ∈ X ↔ a ∈ X

def SymmetricPoints (X : Set A) : Prop := ∀ a ∈ X, ∃ D : Set Row, Small D ∧ Holds (P := P) D a

/-- Either an injection into the pure naturals with supported graph, or a
supported graph of an injection from the pure ordinal ω₁. -/
def SetComparison (X : Set A) : Prop :=
  (∃ (_ : X ↪ ℕ) (D : Set Row), Small D ∧ ∀ a ∈ X, Holds (P := P) D a) ∨
  (∃ (e : Row ↪ X) (D : Set Row), Small D ∧ ∀ i, Holds (P := P) D (e i).val)

/-- Cardinal comparison for all internal set carriers, with the action of the
full product on their ambient objects. Restriction to the residual product is
necessary because the full group may move the set itself. -/
theorem set_comparison [Finite P] (perfect : commutator P = ⊤) (X : Set A)
    (setSym : SymmetricSet (P := P) X) (points : SymmetricPoints (P := P) X) :
    SetComparison (P := P) X := by
  classical
  obtain ⟨E,smallE,hE⟩ := setSym
  let I := {i : Row // i∉E}
  let extend := blockMap (P := P) Eᶜ
  have onE (g : I→P) : OnSupport E (extend g) := by
    intro i hi; simp [extend,blockMap,hi]
  let hom := (permOn (G := Row→P) X).comp (extend.codRestrict (respects X)
    (fun g => hE (extend g) (onE g)))
  let _ : MulAction (I→P) X := MulAction.compHom X hom
  have act (g : I→P) (a : X) : (g • a).val = extend g • a.val := rfl
  have sub : AtomSupports (P := P) (V := X) (fun i : I => i.val) := by
    intro a
    obtain ⟨D,smallD,fixed⟩ := points a.val a.property
    refine ⟨D,smallD,fun g hg => Subtype.ext ((act g a).trans (fixed _ ?_))⟩
    intro i hi
    by_cases mem : i ∈ E
    · simp [extend,blockMap,mem]
    · simpa [extend,blockMap,mem] using hg ⟨i,mem⟩ hi
  have liftFix {D : Set Row} {a : X} (h : PointSupport (P := P) ((fun i : I => i.val) ⁻¹' D) a) :
      Holds (P := P) (E∪D) a.val := by
    intro g hg
    let k (i : I) := g i.val
    have e : extend k = g := by
      funext i; by_cases hi : i∈E
      · simp [extend,blockMap,hi,hg i (Or.inl hi)]
      · simp [extend,blockMap,hi,k]
    have fixed := congrArg Subtype.val (h k (fun i hi => hg i.val (Or.inr hi)))
    rw [act,e] at fixed
    exact fixed
  rcases comparison_of_perfect (fun i : I => i.val) perfect sub with ⟨f,D,small,fix⟩ | ⟨f,D,small,fix⟩
  · exact Or.inl ⟨f,E∪D,small_union smallE small,fun a ha => liftFix (a := ⟨a,ha⟩)
      (fun g hg => f.injective (fix g hg _))⟩
  · exact Or.inr ⟨f,E∪D,small_union smallE small,fun i => liftFix (fix i)⟩

/-- Specialization to the full product of alternating groups on five letters:
the comparison statement holds for every hereditarily symmetric carrier. -/
theorem five_comparison {Y : Type v} [MulAction (Row→FiveGroup) Y] (X : Set Y)
    (setSym : SymmetricSet (P := FiveGroup) X) (points : SymmetricPoints (P := FiveGroup) X) :
    SetComparison (P := FiveGroup) X := set_comparison five_perfect X setSym points

/-- The atom over row i and each graph of a specified enumeration of row i
are fixed by the subgroup fixing that one row. -/
theorem enumerations_supported (i : Row) {J : Type u} (enum : J → Fin 5) :
    Small {i} ∧ ∀ g : Row → FiveGroup, OnSupport {i} g → ∀ j, g i • enum j = enum j := by
  refine ⟨small_singleton i,fun g hg j => ?_⟩
  rw [hg i rfl,one_smul]

/-- Each coordinate row has five atoms and its product with ℕ is denumerable. -/
theorem row_sizes : Nat.card (Fin 5) = 5 ∧ Nonempty ((Fin 5 × ℕ) ≃ ℕ) := by
  constructor
  · simp
  · exact nonempty_equiv_of_countable

/-- The finite-row permutation model in the manuscript, expressed by its
nonstationary-support semantics in the ground universe. -/
theorem five_row_model :
    (∀ (Y : Type v) [MulAction (Row→FiveGroup) Y] (X : Set Y), SymmetricSet (P := FiveGroup) X →
      SymmetricPoints (P := FiveGroup) X → SetComparison (P := FiveGroup) X) ∧
    (¬ ∃ (f : Row → Fin 5) (D : Set Row), Small D ∧
      ∀ g : Row → FiveGroup, OnSupport D g → ∀ i, g i • f i = f i) ∧
    (¬ ∃ (f : Row → Fin 5 × ℕ) (D : Set Row), Small D ∧
      ∀ g : Row → FiveGroup, OnSupport D g → ∀ i, (g i • (f i).1,(f i).2) = f i) :=
  ⟨fun _ _ => five_comparison,no_five_selector,no_denumerable_selector⟩

end ChoiceOmegaOne
