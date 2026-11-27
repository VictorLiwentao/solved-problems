module

public import SolvedProblems.ProjectiveExchange
public import SolvedProblems.ProjectiveClosure
import Mathlib.Data.Set.Finite.Range

public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set

variable {L : Language} {M : Type*} [L.Structure M]

/-- Exchange for arbitrary parameter sets. Only the finite tuple witnessing the
algebraicity of `b` over `S ∪ {a}` enters the proof. -/
theorem acl_exchange (fin : FiniteTypes L M) (min : Minimal L M) (S : Set M) {a b : M}
    (ha : b ∈ acl L (insert a S)) (hb : b ∉ acl L S) : a ∈ acl L (insert b S) := by
  classical
  obtain ⟨n,z,inside,alg⟩ := ha
  let D := (Finset.univ.image z).erase a
  let x := enumerate D
  have dom : Set.range x = (D : Set M) := range_enumerate D
  have ds : (D : Set M) ⊆ S := by
    rintro u hu
    obtain ⟨ne,h⟩ := Finset.mem_erase.mp hu
    obtain ⟨i,_,hh⟩ := Finset.mem_image.mp h
    exact (Set.mem_insert_iff.mp (inside ⟨i,hh⟩)).resolve_left ne
  have inc : Set.range z ⊆ Set.range (point x a) := by
    rintro _ ⟨i,rfl⟩
    by_cases h : z i = a
    · exact ⟨.inr (),h.symm⟩
    · have hd : z i ∈ D := Finset.mem_erase.mpr ⟨h,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
      obtain ⟨j,hj⟩ := (dom ▸ hd : z i ∈ Set.range x)
      exact ⟨.inl j,hj⟩
  have gen : b ∉ tupleClosure L x := fun hx => hb ⟨_,x,dom.subset.trans ds,hx⟩
  have ex := tuple_exchange fin min x (tuple_mono z _ inc alg) gen
  have sub : Set.range (point x b) ⊆ insert b S := by
    rintro _ ⟨j,rfl⟩
    cases j with
    | inl j => exact Set.mem_insert_of_mem b (ds (dom ▸ Set.mem_range_self j))
    | inr j => exact Set.mem_insert b S
  have out := acl_mono (L := L) sub ((acl_range (L := L) (point x b)).symm ▸ ex)
  exact out

/-- Closure is finitary even on an arbitrary parameter set. -/
theorem acl_finite_character (S : Set M) (a : M) :
    a ∈ acl L S ↔ ∃ D : Finset M, (D : Set M) ⊆ S ∧ a ∈ acl L (D : Set M) := by
  classical
  refine ⟨?_,fun ⟨D,h,ha⟩ => acl_mono h ha⟩
  rintro ⟨n,x,inc,hx⟩
  let D := Finset.univ.image x
  have eq : (D : Set M) = Set.range x := by simp [D]
  exact ⟨D,eq.subset.trans inc,eq ▸ (acl_range (L := L) x).symm ▸ hx⟩

/-- In a minimal structure with finitely many types of each finite arity,
algebraic closure is a locally finite pregeometry. -/
theorem pregeometry (fin : FiniteTypes L M) (min : Minimal L M) :
    (∀ S : Set M, S ⊆ acl L S) ∧
    (∀ S T : Set M, S ⊆ T → acl L S ⊆ acl L T) ∧
    (∀ S : Set M, acl L (acl L S) = acl L S) ∧
    (∀ S : Set M, ∀ a, a ∈ acl L S ↔ ∃ D : Finset M, (D : Set M) ⊆ S ∧ a ∈ acl L (D : Set M)) ∧
    (∀ S : Set M, S.Finite → (acl L S).Finite) ∧
    (∀ (S : Set M) (a b : M), b ∈ acl L (insert a S) → b ∉ acl L S → a ∈ acl L (insert b S)) :=
  ⟨acl_extensive,fun _ _ => acl_mono,acl_idempotent fin,acl_finite_character,
    fun _ => finite_acl fin,fun S _ _ => acl_exchange fin min S⟩

end ProjectiveAlgebraic
