module

public import SolvedProblems.EDMDensity
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.GroupAction.Defs

@[expose] public section
namespace EDMRows
variable (I : TallIdeal ℕ)

abbrev Atom := ℕ × ℕ
abbrev Support := ℕ → Set ℕ

def moved (g : Equiv.Perm ℕ) : Set ℕ := {a | g a ≠ a}

/-- Permutations with small moved set form the group acting on one row. -/
def rowGroup : Subgroup (Equiv.Perm ℕ) where
  carrier := {g | I.small (moved g)}
  one_mem' := by simpa [moved] using I.finite Set.finite_empty
  mul_mem' := by
    intro g h hg hh
    apply I.down _ (I.union hg hh)
    intro a ha
    by_contra! hn
    have h1 : g a = a := Classical.byContradiction (fun h => hn (Or.inl h))
    have h2 : h a = a := Classical.byContradiction (fun h => hn (Or.inr h))
    exact ha (by simp [h1,h2])
  inv_mem' := by
    intro g hg
    apply I.down _ hg
    intro a ha h
    exact ha (g.injective (by simp [h]))

/-- The full direct product, allowing independent permutations in infinitely
many rows, subject only to the small-moved-set condition in each row. -/
abbrev Group := ℕ → rowGroup I

instance : MulAction (Group I) Atom where
  smul := fun g a => (a.1,(g a.1).val a.2)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def Admissible (E : Support) : Prop := {n | ¬I.small (E n)}.Finite

def Fixes (g : Group I) (E : Support) : Prop := ∀ n a, a ∈ E n → (g n).val a = a

def Supports {V : Type*} [MulAction (Group I) V] (E : Support) (v : V) : Prop :=
  ∀ g : Group I, Fixes I g E → g • v = v

def FamilySupported {J V : Type*} [MulAction (Group I) V] (f : J → V) : Prop :=
  ∃ E : Support, Admissible I E ∧ ∀ j, Supports I E (f j)

def InternalInjection (f : Atom → ℕ) : Prop :=
  Function.Injective f ∧ ∃ E : Support, Admissible I E ∧
    ∀ (g : Group I), Fixes I g E → ∀ a, f (g • a) = f a

def row (n : ℕ) : Set Atom := {a | a.1 = n}

theorem small_swap (a b : ℕ) : Equiv.swap a b ∈ rowGroup I := by
  apply I.down (T := {a,b}) _ (I.finite ((Set.finite_singleton b).insert a))
  intro x hx
  by_contra! h
  have xa : x ≠ a := fun e => h (by simp [e])
  have xb : x ≠ b := fun e => h (by simp [e])
  exact hx (Equiv.swap_apply_of_ne_of_ne xa xb)

/-- A single transposition extended by the identity on every other row. -/
def swapAt (n a b : ℕ) (m : ℕ) : rowGroup I :=
  if m = n then ⟨Equiv.swap a b,small_swap I a b⟩ else 1

theorem swapAt_fixes (E : Support) {n a b : ℕ} (ha : a ∉ E n) (hb : b ∉ E n) :
    Fixes I (swapAt I n a b) E := by
  intro m z hz
  by_cases eq : m = n
  · subst m
    have aa : z ≠ a := fun e => ha (e ▸ hz)
    have bb : z ≠ b := fun e => hb (e ▸ hz)
    simpa [swapAt] using Equiv.swap_apply_of_ne_of_ne aa bb
  · simp [swapAt,eq]

theorem separates {f : Atom → ℕ} (h : InternalInjection I f) : False := by
  classical
  obtain ⟨inj,E,finite,fix⟩ := h
  have residual : ∃ n, I.small (E n) := by
    by_contra! all
    exact Set.infinite_univ (α := ℕ) (finite.subset (fun n _ => all n))
  obtain ⟨n,hn⟩ := residual
  obtain ⟨a,ha⟩ := (I.infinite_complement hn).nonempty
  obtain ⟨b,hb,bne⟩ := (I.infinite_complement hn).exists_gt a
  let g := swapAt I n a b
  have hmove : g • (n,a) = (n,b) := by change (n, (swapAt I n a b n).val a) = _; simp [swapAt]
  have eq := inj (fix g (swapAt_fixes I E ha hb) (n,a))
  exact bne.ne' (congrArg Prod.snd (hmove.symm.trans eq))

theorem row_enumerable (n : ℕ) : ∃ f : ℕ → Atom, Function.Injective f ∧
    Set.range f = row n ∧ FamilySupported I f := by
  let f (a : ℕ) := (n,a)
  have ran : Set.range f = row n := by ext ⟨m,a⟩; exact ⟨fun ⟨b,h⟩ => (congrArg Prod.fst h).symm,
    fun h => ⟨a,Prod.ext h.symm rfl⟩⟩
  let E (m : ℕ) : Set ℕ := if m = n then Set.univ else ∅
  have ok : Admissible I E := by
    apply (Set.finite_singleton n).subset
    intro m hm
    change m = n
    by_contra ne
    exact hm (by simpa [E,ne] using I.finite Set.finite_empty)
  refine ⟨f,fun _ _ e => congrArg Prod.snd e,ran,E,ok,fun a g h => ?_⟩
  exact Prod.ext rfl (h n a (by simp [E]))

/-- In the concrete density-zero support model the atom set is the disjoint
union of the invariant, internally denumerable rows. It has no supported
injection into the trivial natural-number sort. -/
theorem density_row_counterexample :
    (∀ (g : Group densityIdeal) n a, g • a ∈ row n ↔ a ∈ row n) ∧
    (Set.univ = ⋃ n, row n) ∧ (∀ n m, n ≠ m → Disjoint (row n) (row m)) ∧
    (∀ n, ∃ f : ℕ → Atom, Function.Injective f ∧ Set.range f = row n ∧ FamilySupported densityIdeal f) ∧
    ¬ ∃ f : Atom → ℕ, InternalInjection densityIdeal f := by
  refine ⟨fun _ _ _ => Iff.rfl, ?_, ?_, row_enumerable densityIdeal,fun ⟨_,h⟩ => separates _ h⟩
  · ext a
    exact ⟨fun _ => Set.mem_iUnion.mpr ⟨a.1,rfl⟩,fun _ => Set.mem_univ _⟩
  · intro n m ne
    exact Set.disjoint_left.mpr (fun a (ha : a.1 = n) (hb : a.1 = m) => ne (ha.symm.trans hb))

end EDMRows
