module

public import SolvedProblems.ProjectiveTypesCard
import SolvedProblems.ProjectiveCodeMatch

public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set

variable {L : Language} {M : Type*} [L.Structure M] {ι : Type}

/-- Swap the final two variables while retaining the base parameters. -/
private def swapLast : (ι ⊕ Unit) ⊕ Unit → (ι ⊕ Unit) ⊕ Unit
  | .inl (.inl i) => .inl (.inl i)
  | .inl (.inr _) => .inr ()
  | .inr _ => .inl (.inr ())

private theorem flip (x : ι → M) (a b : M) (φ : L.Formula ((ι ⊕ Unit) ⊕ Unit)) :
    b ∈ locus L (point x a) φ ↔ a ∈ locus L (point x b) (φ.relabel swapLast) := by
  change φ.Realize _ ↔ (φ.relabel swapLast).Realize _
  rw [Formula.realize_relabel]
  have e : point (point x a) b = point (point x b) a ∘ swapLast := by
    funext i
    rcases i with (i|i)|i <;> rfl
  rw [e]

/-- Algebraic closure satisfies exchange. The row containing `b` is finite.
If the inverse fibre through `a` were cofinite, more than the row size many
conjugates of `b` would have cofinite inverse fibres, with a common point. -/
theorem tuple_exchange [Finite ι] (fin : FiniteTypes L M) (min : Minimal L M) (x : ι → M) {a b : M}
    (ab : b ∈ tupleClosure L (point x a)) (bs : b ∉ tupleClosure L x) : a ∈ tupleClosure L (point x b) := by
  classical
  by_contra notAlg
  let joint := point (point x a) b
  obtain ⟨φ,hφ,iso⟩ := isolate (fin ((ι ⊕ Unit) ⊕ Unit)) joint
  let row (u : M) := locus L (point x u) φ
  let col (v : M) := locus L (point x v) (φ.relabel swapLast)
  have rfin : (row a).Finite := ((algebraic_iff_finite_type fin _ _).mp ab).subset
    (fun v hv => (iso (point (point x a) v)).mp hv)
  have ac : a ∈ col b := (flip x a b φ).mp hφ
  have cfin : (col b)ᶜ.Finite := (min _ (point x b) (φ.relabel swapLast)).resolve_left (fun h => notAlg ⟨_,ac,h⟩)
  let O := {v | tupleType L (point x v) = tupleType L (point x b)}
  have large : O.Infinite := fun small => bs ((algebraic_iff_finite_type fin x b).mpr small)
  obtain ⟨n,hn⟩ := rfin.exists_encard_eq_coe
  have enough : ((n+1 : ℕ) : ℕ∞) ≤ O.encard := large.encard_eq ▸ le_top
  obtain ⟨t,ht,inj⟩ := (O.le_encard_iff_exists_fin_injective (n+1)).mp enough
  have good (i : Fin (n+1)) : (col (t i))ᶜ.Finite := by
    have cmp := locus_card fin (ht i : tupleType L (point x (t i)) = tupleType L (point x b))
      (φ.relabel swapLast).not
    have cm (v : M) : locus L (point x v) (φ.relabel swapLast).not = (col v)ᶜ := by
      ext u; exact Formula.realize_not
    rw [cm,cm] at cmp
    exact cfin.finite_of_encard_le cmp.le
  have small : (⋃ i, (col (t i))ᶜ).Finite := Set.finite_iUnion good
  obtain ⟨u,_,outside⟩ := large.exists_notMem_finite small
  have mem (i : Fin (n+1)) : t i ∈ row u := by
    apply (flip x u (t i) φ).mpr
    by_contra h
    exact outside (Set.mem_iUnion.mpr ⟨i,h⟩)
  have ju := (iso (point (point x u) (t 0))).mp (mem 0)
  have ua : tupleType L (point x u) = tupleType L (point x a) := match_subtuple ju Sum.inl
  have rowEq := locus_card fin ua φ
  have tooMany := ((row u).le_encard_iff_exists_fin_injective (n+1)).mpr ⟨t,mem,inj⟩
  change (row u).encard = (row a).encard at rowEq
  rw [rowEq,hn] at tooMany
  exact Nat.not_succ_le_self n (ENat.natCast_le_natCast.mp tooMany)

end ProjectiveAlgebraic
