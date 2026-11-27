module

public import SolvedProblems.ProjectiveAlgebraicModel
import Mathlib.Data.Set.Finite.Range

public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set

variable {L : Language} {M : Type*} [L.Structure M]

/-- In a finite spectrum of realized types, a single formula defines each complete type. -/
theorem isolate {ι : Type*} (fin : (typesIn L M ι).Finite) (x : ι → M) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ∀ y : ι → M, φ.Realize y ↔ tupleType L y = tupleType L x := by
  have distinguish {y : ι → M} (diff : tupleType L y ≠ tupleType L x) :
      ∃ φ : L.Formula ι, φ.Realize x ∧ ¬φ.Realize y := by
    by_contra! no
    apply diff
    ext φ
    change φ.Realize y ↔ φ.Realize x
    refine ⟨fun hy => ?_, no φ⟩
    by_contra hx
    exact (Formula.realize_not.mp (no φ.not (Formula.realize_not.mpr hx))) hy
  have aux (S : Set (Set (L.Formula ι))) (hs : S.Finite) (sub : S ⊆ typesIn L M ι) :
      ∃ φ : L.Formula ι, φ.Realize x ∧ ∀ y : ι → M, tupleType L y ∈ S →
        φ.Realize y → tupleType L y = tupleType L x := by
    induction S, hs using Set.Finite.induction_on with
    | empty => exact ⟨⊤,Formula.realize_top.mpr trivial,by simp⟩
    | @insert q S _ hs ih =>
      obtain ⟨ψ,hψ,indu⟩ := ih ((Set.subset_insert q S).trans sub)
      obtain ⟨y,hy⟩ := sub (Set.mem_insert q S)
      by_cases he : tupleType L y = tupleType L x
      · refine ⟨ψ,hψ,?_⟩
        intro z hz h
        rcases Set.mem_insert_iff.mp hz with eq | mem
        · exact (eq.trans hy.symm).trans he
        · exact indu z mem h
      · obtain ⟨θ,hθ,hθy⟩ := distinguish he
        refine ⟨ψ ⊓ θ, Formula.realize_inf.mpr ⟨hψ,hθ⟩, ?_⟩
        intro z hz h
        obtain ⟨hp,ht⟩ := Formula.realize_inf.mp h
        rcases Set.mem_insert_iff.mp hz with eq | mem
        · exact False.elim <| hθy ((show θ ∈ tupleType L y from (eq.trans hy.symm) ▸ ht))
        · exact indu z mem hp
  obtain ⟨φ,hφ,spec⟩ := aux _ fin Set.Subset.rfl
  exact ⟨φ,hφ, fun y => ⟨spec y ⟨y,rfl⟩,fun h => (show φ ∈ tupleType L y from h ▸ hφ)⟩⟩

variable {ι : Type} [Finite ι]

private def fiberType (x : ι → M) (p : Set (L.Formula (ι ⊕ Unit))) : Set M :=
  {a | tupleType L (point x a) = p}

/-- An element is algebraic over a finite tuple precisely when its complete
one-type over the tuple has only finitely many realizations. -/
theorem algebraic_iff_finite_type (fin : FiniteTypes L M) (x : ι → M) (a : M) :
    a ∈ tupleClosure L x ↔ {b | tupleType L (point x b) = tupleType L (point x a)}.Finite := by
  constructor
  · rintro ⟨φ,ha,small⟩
    exact small.subset fun b h => (show φ ∈ tupleType L (point x b) from h ▸ ha)
  · intro small
    obtain ⟨φ,ha,hφ⟩ := isolate (fin (ι ⊕ Unit)) (point x a)
    have eq : locus L x φ = {b | tupleType L (point x b) = tupleType L (point x a)} := by
      ext b; exact hφ (point x b)
    exact ⟨φ,ha,eq.symm ▸ small⟩

/-- Local finiteness of algebraic closure follows from finite finite-arity type spectra. -/
theorem finite_tupleClosure (fin : FiniteTypes L M) (x : ι → M) : (tupleClosure L x).Finite := by
  let S := {p ∈ typesIn L M (ι ⊕ Unit) | (fiberType x p).Finite}
  have hs : S.Finite := (fin (ι ⊕ Unit)).subset fun _ h => h.1
  apply (hs.biUnion (fun p hp => hp.2)).subset
  intro a ha
  have hf := (algebraic_iff_finite_type fin x a).mp ha
  exact Set.mem_iUnion₂.mpr ⟨_,⟨⟨_,rfl⟩,hf⟩,rfl⟩

/-- Nonalgebraic elements all realize the same complete unary type over any given finite tuple. -/
theorem generic_type (min : Minimal L M) {x : ι → M} {a b : M}
    (ha : a ∉ tupleClosure L x) (hb : b ∉ tupleClosure L x) :
    tupleType L (point x a) = tupleType L (point x b) := by
  have go {z w : M} (hz : z ∉ tupleClosure L x) (hw : w ∉ tupleClosure L x)
      (φ : L.Formula (ι ⊕ Unit)) (hφ : φ.Realize (point x z)) : φ.Realize (point x w) := by
    rcases min ι x φ with h | h
    · exact (hz ⟨φ,hφ,h⟩).elim
    · by_contra bad
      apply hw
      have setEq : locus L x φ.not = (locus L x φ)ᶜ := by
        ext v; exact Formula.realize_not
      exact ⟨φ.not,Formula.realize_not.mpr bad,setEq.symm ▸ h⟩
  exact Set.ext fun φ => ⟨go ha hb φ,go hb ha φ⟩

end ProjectiveAlgebraic
