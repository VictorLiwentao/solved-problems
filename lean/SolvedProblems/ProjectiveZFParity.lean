module

public import SolvedProblems.ProjectiveZFFinite
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V] (M : Core V)

/-- A first-order parity test that needs no standardness assumption on the
ambient universe or on its natural numbers. -/
def Balanced (X : V) : Prop := ∃ U W : V, (∀ x, x ∈ X ↔ x ∈ U ∨ x ∈ W) ∧
  (∀ x, x ∈ U → x ∉ W) ∧ Equinumerous U W

theorem defBalanced {ι : Type*} {s : (ι → V) → V} (hs : Term s) : Definable (fun v => Balanced (s v)) := by
  unfold Balanced
  repeat' first | apply defEquinumerous | apply defIff | apply defAnd | apply defOr | apply defEx | apply defAll
                | apply defNot | apply defImp | apply defMem | zf_terms

private noncomputable def partEquiv {X U W : V} (cover : ∀ x : V, x ∈ X ↔ x ∈ U ∨ x ∈ W) (disj : ∀ x, x ∈ U → x ∉ W) :
    open Classical in El X ≃ (El U ⊕ El W) := by
  classical
  refine {
    toFun := fun x => if h : x.val ∈ U then .inl ⟨_,h⟩ else .inr ⟨_,((cover _).mp x.property).resolve_left h⟩
    invFun := Sum.elim (fun u => ⟨u.val,(cover _).mpr (Or.inl u.property)⟩) (fun w => ⟨w.val,(cover _).mpr (Or.inr w.property)⟩)
    left_inv := ?_
    right_inv := ?_ }
  · intro x; by_cases h : x.val ∈ U <;> simp [h]
  · rintro (x|x)
    · simp [x.property]
    · have outside : x.val ∉ U := fun h => disj _ h x.property
      simp [outside]

private noncomputable def numbered {X : V} {n : ℕ} (w : Fin n → V) (h : elts X = range w) (inj : Injective w) :
    Fin n ≃ El X := by
  let v (i : Fin n) : El X := ⟨w i,h.superset (mem_range_self i)⟩
  apply Equiv.ofBijective v
  refine ⟨fun i j h' => inj (congrArg Subtype.val h'),?_⟩
  intro x
  obtain ⟨i,hi⟩ := h.subset x.property
  exact ⟨i,Subtype.ext hi⟩

include M

/-- On every externally finite set, internal equinumerous halves exist exactly
when the actual number of members is even. -/
theorem balanced_iff_even (X : V) [Finite (El X)] : Balanced X ↔ Even (Nat.card (El X)) := by
  classical
  constructor
  · rintro ⟨U,W,cover,disj,eq⟩
    obtain ⟨e⟩ := equiv_of_equinumerous M eq
    let cut := partEquiv cover disj
    let := Finite.of_equiv (El X) cut
    let := Finite.of_injective (Sum.inl : El U → El U ⊕ El W) Sum.inl_injective
    let := Finite.of_injective (Sum.inr : El W → El U ⊕ El W) Sum.inr_injective
    refine ⟨Nat.card (El U),?_⟩
    rw [Nat.card_congr cut,Nat.card_sum,← Nat.card_congr e]
  · rintro ⟨m,card⟩
    let := Fintype.ofFinite (El X)
    let e := Fintype.equivOfCardEq (α := Fin m ⊕ Fin m) (β := El X) (by simpa [Nat.card_eq_fintype_card] using card.symm)
    let l (i : Fin m) := (e (.inl i)).val
    let r (i : Fin m) := (e (.inr i)).val
    obtain ⟨U,hU⟩ := representsFinite M X (Set.finite_range l)
    obtain ⟨W,hW⟩ := representsFinite M X (Set.finite_range r)
    have L := numbered l hU (Subtype.val_injective.comp (e.injective.comp Sum.inl_injective))
    have R := numbered r hW (Subtype.val_injective.comp (e.injective.comp Sum.inr_injective))
    let := Finite.of_equiv (Fin m) L
    refine ⟨U,W,?_,?_,equinumerous_of_finite M (L.symm.trans R)⟩
    · intro x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := e.surjective (⟨x,hx⟩ : El X)
        rcases i with i|i
        · exact Or.inl (hU.superset ⟨i,congrArg Subtype.val hi⟩)
        · exact Or.inr (hW.superset ⟨i,congrArg Subtype.val hi⟩)
      · rintro (hu|hw)
        · obtain ⟨i,rfl⟩ := hU.subset hu
          exact (e (.inl i)).property
        · obtain ⟨i,rfl⟩ := hW.subset hw
          exact (e (.inr i)).property
    · intro x hu hw
      obtain ⟨i,hi⟩ := hU.subset hu
      obtain ⟨j,hj⟩ := hW.subset hw
      exact Sum.inl_ne_inr (e.injective (Subtype.ext (hi.trans hj.symm)))

end ProjectiveZF
