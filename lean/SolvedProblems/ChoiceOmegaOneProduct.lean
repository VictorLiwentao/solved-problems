module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Subgroup

variable {I : Type u} {P : Type v} [Group P]

/-- Extend a tuple on one block by the identity off that block. -/
def blockMap (T : Set I) [DecidablePred (· ∈ T)] : (T → P) →* (I → P) where
  toFun f i := if h : i∈T then f ⟨i,h⟩ else 1
  map_one' := by funext i; by_cases hi : i∈T <;> simp [hi]
  map_mul' f g := by funext i; by_cases hi : i∈T <;> simp [hi]

/-- Finite coordinate patterns factor a finitely generated group through a
finite power of P, even for an arbitrary set of coordinates. -/
theorem locally_finite_power [Finite P] (s : Finset (I → P)) :
    Finite (Subgroup.closure (s : Set (I → P))) := by
  classical
  let read (i : I) (g : s) := g.val i
  let φ : ((s → P) → P) →* (I → P) :=
    {toFun := fun f i => f (read i), map_one' := rfl, map_mul' := fun _ _ => rfl}
  have le : Subgroup.closure (s : Set (I → P)) ≤ φ.range :=
    (Subgroup.closure_le _).mpr (fun f hf => ⟨(fun t => t ⟨f,hf⟩),rfl⟩)
  have fr : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact Finite.of_injective (Subgroup.inclusion le) (Subgroup.inclusion_injective le)

private def constBlock (T : Set I) [DecidablePred (· ∈ T)] : P →* (I → P) where
  toFun a i := if i∈T then a else 1
  map_one' := by funext i; simp
  map_mul' f g := by funext i; by_cases hi : i∈T <;> simp [hi]

/-- Every power of a fixed finite perfect group is perfect. Splitting by the
finitely many coordinate values reduces each tuple to constant block maps. -/
theorem perfect_power [Finite P] (perfect : commutator P = ⊤) :
    commutator (I → P) = ⊤ := by
  classical
  let _ := Fintype.ofFinite P
  apply top_unique
  intro f _
  have mapped (T : Set I) (p : P) : constBlock (I := I) T p ∈ commutator (I → P) := by
    let h := constBlock (P := P) T
    have m : h p ∈ (commutator P).map h := ⟨p,by rw [perfect]; exact trivial,rfl⟩
    rw [map_commutator_eq] at m
    exact Subgroup.commutator_mono le_top le_top m
  let part (s : Finset P) (i : I) := if f i ∈ s then f i else 1
  have ok (s : Finset P) : part s ∈ commutator (I → P) := by
    induction s using Finset.induction_on with
    | empty =>
      have e : part ∅ = (1 : I→P) := by funext i; simp [part]
      rw [e]; exact (commutator (I→P)).one_mem
    | @insert a s ha ih =>
      have e : part (insert a s) = constBlock {i | f i = a} a * part s := by
        funext i
        by_cases hi : f i = a <;> simp [part,constBlock,hi,ha]
      exact e ▸ (commutator (I→P)).mul_mem (mapped _ a) ih
  simpa [part] using ok Finset.univ

theorem block_commute {A B : Set I} [DecidablePred (·∈A)] [DecidablePred (·∈B)] (dis : Disjoint A B)
    (a : A → P) (b : B → P) : Commute (blockMap A a) (blockMap B b) := by
  funext i
  by_cases ha : i∈A
  · have hb : i∉B := Set.disjoint_left.1 dis ha
    simp [blockMap,ha,hb]
  · simp [blockMap,ha]

end ChoiceOmegaOne
