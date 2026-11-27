module

public import SolvedProblems.ProjectiveIsolation
import SolvedProblems.ProjectiveCodeMatch

public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {ι : Type}

/-- Restrictions of matching tuples to a parameter list and one of the new entries. -/
theorem match_entry {κ : Type*} {x y : ι → M} {a b : κ → M}
    (same : tupleType L (Sum.elim x a) = tupleType L (Sum.elim y b)) (i : κ) :
    tupleType L (point x (a i)) = tupleType L (point y (b i)) := by
  have h := match_subtuple same (Sum.elim Sum.inl fun _ : Unit => Sum.inr i)
  have cut (u : ι → M) (v : κ → M) :
      Sum.elim u v ∘ Sum.elim Sum.inl (fun _ : Unit => Sum.inr i) = point u (v i) := by
    funext j; cases j <;> rfl
  rwa [cut,cut] at h

private theorem inj_transfer {κ : Type*} {a b : κ → M} (same : tupleType L a = tupleType L b)
    (ha : Injective a) : Injective b := by
  intro i j eq
  apply ha
  have h := Set.ext_iff.mp same ((Term.var i).equal (Term.var j))
  change ((Term.var i).equal (Term.var j)).Realize a ↔ ((Term.var i).equal (Term.var j)).Realize b at h
  exact (Formula.realize_equal.mp (h.mpr (Formula.realize_equal.mpr eq)))

variable [Finite ι]

private theorem copy_card_le (fin : FiniteTypes L M) {x y : ι → M} {S T : Set M}
    (m : tupleType L x = tupleType L y)
    (comp : ∀ a b, tupleType L (point x a) = tupleType L (point y b) → (a ∈ S ↔ b ∈ T)) :
    S.encard ≤ T.encard := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  obtain ⟨a,inside,inj⟩ := (S.le_encard_iff_exists_fin_injective n).mp hn
  obtain ⟨b,joint⟩ := extendTuple L (Eq.refl _) (fin (ι ⊕ Fin n)) m a
  have ab : tupleType L a = tupleType L b := match_subtuple joint Sum.inr
  exact (T.le_encard_iff_exists_fin_injective n).mpr
    ⟨b, fun i => (comp _ _ (match_entry joint i)).mp (inside i), inj_transfer ab inj⟩

/-- Any two sets of points that agree under matching all one-point extensions
have the same finite cardinal, or are both infinite. -/
theorem copy_card (fin : FiniteTypes L M) {x y : ι → M} {S T : Set M}
    (m : tupleType L x = tupleType L y)
    (comp : ∀ a b, tupleType L (point x a) = tupleType L (point y b) → (a ∈ S ↔ b ∈ T)) :
    S.encard = T.encard :=
  le_antisymm (copy_card_le fin m comp) (copy_card_le fin m.symm fun a b h => (comp b a h.symm).symm)

/-- The extended finite cardinality of a definable unary set depends only on the
complete type of its parameters. -/
theorem locus_card (fin : FiniteTypes L M) {x y : ι → M} (m : tupleType L x = tupleType L y)
    (φ : L.Formula (ι ⊕ Unit)) : (locus L x φ).encard = (locus L y φ).encard :=
  copy_card fin m fun _ _ h => Set.ext_iff.mp h φ

/-- Algebraicity is preserved under matching the full pointed tuples. -/
theorem algebraic_match (fin : FiniteTypes L M) {x y : ι → M} {a b : M}
    (m : tupleType L (point x a) = tupleType L (point y b)) : a ∈ tupleClosure L x ↔ b ∈ tupleClosure L y := by
  have base : tupleType L x = tupleType L y := match_subtuple m Sum.inl
  have go {u v : ι → M} {s t : M} (h : tupleType L (point u s) = tupleType L (point v t))
      (bse : tupleType L u = tupleType L v) (hs : s ∈ tupleClosure L u) : t ∈ tupleClosure L v := by
    obtain ⟨φ,has,small⟩ := hs
    exact ⟨φ,(Set.ext_iff.mp h φ).mp has,small.finite_of_encard_le (locus_card fin bse φ).ge⟩
  exact ⟨go m base,go m.symm base.symm⟩

/-- The finite sizes of the closures agree for elementarily matching parameter tuples. -/
theorem closure_card (fin : FiniteTypes L M) {x y : ι → M} (m : tupleType L x = tupleType L y) :
    (tupleClosure L x).encard = (tupleClosure L y).encard :=
  copy_card fin m fun _ _ h => algebraic_match fin h

end ProjectiveAlgebraic
