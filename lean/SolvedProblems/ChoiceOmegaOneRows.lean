module

public import SolvedProblems.ChoiceOmegaOneCompare
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Cardinal Ordinal Order Filter

/-- Residual product group fixing every row named in a support. -/
def OnSupport {P : Type u} [Group P] (E : Set Row) (g : Row → P) := ∀ i ∈ E, g i = 1

def Holds {P : Type u} [Group P] {V : Type v} [MulAction (Row → P) V] (E : Set Row) (x : V) :=
  ∀ g : Row → P, OnSupport E g → g • x = x

/-- Internally countable means an injection to the pure naturals has supported
graph. Injectivity makes invariance equivalent to pointwise fixing its domain. -/
def InternalCountable (P : Type u) [Group P] (V : Type v) [MulAction (Row → P) V] : Prop :=
  ∃ (f : V ↪ ℕ) (D : Set Row), Small D ∧ ∀ g : Row → P, OnSupport D g → ∀ x, f (g • x) = f x

/-- An injection from the pure ordinal ω₁ whose graph has a support. -/
def InternalOmegaOne (P : Type u) [Group P] (V : Type v) [MulAction (Row → P) V] : Prop :=
  ∃ (f : Row ↪ V) (D : Set Row), Small D ∧ ∀ i, Holds (P := P) D (f i)

theorem small_singleton (i : Row) : Small {i} :=
  ⟨Ioi i,above i,Set.disjoint_left.2 (by rintro x hx h; obtain rfl : x=i := hx; exact (show x < x from h).false)⟩

/-- A supported countable family of selectable ground objects admits one
common support for its entire sequence. -/
theorem support_sequence {P : Type u} [Group P] {V : Type v} [MulAction (Row → P) V]
    (f : ℕ → V) (ind : ∀ n, ∃ E, Small E ∧ Holds (P := P) E (f n)) :
    ∃ E, Small E ∧ ∀ n, Holds (P := P) E (f n) := by
  choose D small fix using ind
  refine ⟨⋃ n,D n,small_countable_union D small,?_⟩
  intro n g hg
  exact fix n g (fun i hi => hg i (Set.mem_iUnion.2 ⟨n,hi⟩))

/-- Ground dependent choice on a serial relation of hereditarily supported
objects produces a chain with an allowed support. -/
theorem supported_dependent_choice {P : Type u} [Group P] {V : Type v} [MulAction (Row → P) V]
    (ind : ∀ x : V, ∃ E, Small E ∧ Holds (P := P) E x)
    (R : V → V → Prop) (serial : ∀ x, ∃ y, R x y) (x : V) :
    ∃ f : ℕ → V, f 0 = x ∧ (∀ n, R (f n) (f (n+1))) ∧ ∃ E, Small E ∧ ∀ n, Holds (P := P) E (f n) := by
  choose next step using serial
  let f : ℕ → V := Nat.rec x (fun _ y => next y)
  exact ⟨f,rfl,fun n => step (f n),support_sequence f (fun n => ind (f n))⟩

/-- No rowwise selector can be invariant under a nonstationary-support
stabilizer if each row action moves every point somewhere. -/
theorem no_row_selector (P : Type u) [Group P] (Y : Type v) [MulAction P Y]
    (moves : ∀ y : Y, ∃ p : P, p • y ≠ y) :
    ¬ ∃ (f : Row → Y) (D : Set Row), Small D ∧ ∀ g : Row → P, OnSupport D g → ∀ i, (g i) • f i = f i := by
  classical
  rintro ⟨f,D,⟨C,club,dis⟩,fixed⟩
  obtain ⟨i,hi⟩ := club.nonempty
  obtain ⟨p,change⟩ := moves (f i)
  let g (j : Row) := if j=i then p else 1
  have h : OnSupport D g := by
    intro j hj
    have ne : j ≠ i := fun eq => Set.disjoint_left.1 dis hj (eq ▸ hi)
    simp [g,ne]
  exact change (by simpa [g] using fixed g h i)

/-- The row group is the alternating group on the five letters of each row. -/
abbrev FiveGroup := alternatingGroup (Fin 5)

theorem five_perfect : commutator FiveGroup = ⊤ :=
  commutator_alternatingGroup_eq_top (by simp)

theorem no_five_selector :
    ¬ ∃ (f : Row → Fin 5) (D : Set Row), Small D ∧
        ∀ g : Row → FiveGroup, OnSupport D g → ∀ i, (g i) • f i = f i := by
  let _ := alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  apply no_row_selector FiveGroup
  intro y
  obtain ⟨z,ne⟩ := exists_ne y
  obtain ⟨p,h⟩ := MulAction.exists_smul_eq FiveGroup y z
  exact ⟨p,fun eq => ne (h.symm.trans eq)⟩

/-- Multiplying each five-element row by the pure naturals gives denumerable
rows; projecting any supported selector to its first coordinates is impossible. -/
theorem no_denumerable_selector :
    ¬ ∃ (f : Row → Fin 5 × ℕ) (D : Set Row), Small D ∧ ∀ g : Row → FiveGroup, OnSupport D g →
      ∀ i, ((g i) • (f i).1,(f i).2) = f i := by
  rintro ⟨f,D,small,fix⟩
  exact no_five_selector ⟨fun i => (f i).1,D,small,fun g h i => congrArg Prod.fst (fix g h i)⟩

/-- Ground regularity gives an upper bound even for externally enumerated
countable sequences. Thus it also holds for supported sequences of ordinals. -/
theorem countable_bounded {J : Type u} [Countable J] (f : J → Row) : BddAbove (Set.range f) := by
  apply BddAbove.of_not_isCofinal
  intro h
  exact cofinal_uncountable h (Set.countable_range f)

end ChoiceOmegaOne
