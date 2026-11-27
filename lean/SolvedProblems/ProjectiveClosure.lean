module

public import SolvedProblems.ProjectiveTypesCard
import SolvedProblems.ProjectiveCodeMatch
import Mathlib.Data.Set.Finite.Range

public section

namespace ProjectiveAlgebraic

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M]

/-- Extra tuple parameters preserve algebraicity, including when tuples have repetitions. -/
theorem tuple_mono {ι κ : Type*} (x : ι → M) (y : κ → M) (inc : Set.range x ⊆ Set.range y) :
    tupleClosure L x ⊆ tupleClosure L y := by
  classical
  choose t ht using fun i => inc (Set.mem_range_self i)
  rintro a ⟨φ,ha,small⟩
  let ψ := φ.relabel (Sum.map t id)
  have eq : locus L y ψ = locus L x φ := by
    ext b
    change (φ.relabel _).Realize _ ↔ _
    rw [Formula.realize_relabel]
    have m : point y b ∘ Sum.map t id = point x b := by
      funext i
      cases i with
      | inl i => exact ht i
      | inr u => rfl
    rw [m]
    rfl
  exact ⟨ψ,eq ▸ ha,eq ▸ small⟩

/-- Every displayed parameter itself belongs to the tuple closure. -/
theorem mem_of_param {ι : Type*} (x : ι → M) (i : ι) : x i ∈ tupleClosure L x := by
  let φ : L.Formula (ι ⊕ Unit) := (Term.var (Sum.inr ())).equal (Term.var (Sum.inl i))
  have eq : locus L x φ = {x i} := by
    ext b
    exact Formula.realize_equal
  exact ⟨φ,eq ▸ Set.mem_singleton _,eq ▸ Set.finite_singleton _⟩

/-- Algebraic closure is transitive over finite tuples: the finitely many
potential conjugates of the algebraic parameter tuple supply only finitely
many possible values. -/
theorem tuple_trans {ι κ : Type} [Finite ι] [Finite κ] (fin : FiniteTypes L M)
    (x : ι → M) (z : κ → M) (hz : ∀ j, z j ∈ tupleClosure L x) :
    tupleClosure L z ⊆ tupleClosure L x := by
  classical
  intro a ha
  let D := tupleClosure L x
  let := (finite_tupleClosure fin x).to_subtype
  let tuples : Set (κ → M) := Set.range (fun v : κ → D => (fun j => (v j).val))
  have small : (⋃ v ∈ tuples, tupleClosure L v).Finite :=
    (Set.finite_range _).biUnion (fun v _ => finite_tupleClosure fin v)
  apply (algebraic_iff_finite_type fin x a).mpr
  apply small.subset
  intro b hb
  have base : tupleType L (point x a) = tupleType L (point x b) := Eq.symm hb
  obtain ⟨w,joint⟩ := extendTuple L (Eq.refl _) (fin ((ι ⊕ Unit) ⊕ κ)) base z
  have mem (i : κ) : w i ∈ D := by
    have eqs := match_subtuple joint
      (Sum.elim (fun j : ι => Sum.inl (Sum.inl j)) fun _ : Unit => Sum.inr i)
    have cut (p : M) (v : κ → M) :
        Sum.elim (point x p) v ∘ Sum.elim (fun j : ι => Sum.inl (Sum.inl j)) (fun _ : Unit => Sum.inr i)
        = point x (v i) := by funext t; cases t <;> rfl
    rw [cut,cut] at eqs
    exact (algebraic_match fin eqs).mp (hz i)
  have eqs := match_subtuple joint (Sum.elim Sum.inr fun _ : Unit => Sum.inl (Sum.inr ()))
  have cut (p : M) (v : κ → M) :
      Sum.elim (point x p) v ∘ Sum.elim Sum.inr (fun _ : Unit => Sum.inl (Sum.inr ())) =
        point v p := by funext t; cases t <;> rfl
  rw [cut,cut] at eqs
  exact Set.mem_iUnion₂.mpr ⟨w,⟨fun i => ⟨_,mem i⟩,rfl⟩,(algebraic_match fin eqs).mp ha⟩

/-- The algebraic closure of the range of a finite tuple is its tuple closure. -/
theorem acl_range {ι : Type} [Finite ι] (x : ι → M) : acl L (Set.range x) = tupleClosure L x := by
  classical
  ext a
  constructor
  · rintro ⟨n,z,h,ha⟩; exact tuple_mono z x h ha
  · intro ha
    let := Fintype.ofFinite ι
    let e := Fintype.equivFin ι
    have eq : Set.range (x ∘ e.symm) = Set.range x := (e.symm.surjective.range_comp x)
    exact ⟨_,x ∘ e.symm,eq.subset,tuple_mono x _ eq.superset ha⟩

/-- Monotonicity of algebraic closure. -/
theorem acl_mono {S T : Set M} (h : S ⊆ T) : acl L S ⊆ acl L T := by
  rintro a ⟨n,x,hx,ha⟩
  exact ⟨n,x,hx.trans h,ha⟩

/-- Every parameter is algebraic over a set containing it. -/
theorem acl_extensive (S : Set M) : S ⊆ acl L S := by
  intro a ha
  let x : Fin 1 → M := fun _ => a
  exact ⟨1,x,fun _ ⟨_,h⟩ => h ▸ ha,mem_of_param x 0⟩

/-- For a finite set, enumerate its elements without repetitions. -/
@[expose] noncomputable def enumerate (D : Finset M) (i : Fin D.card) : M := (D.equivFin.symm i).val

theorem range_enumerate (D : Finset M) : Set.range (enumerate D) = (D : Set M) := by
  ext a
  exact ⟨fun ⟨i,e⟩ => e ▸ (D.equivFin.symm i).property,
    fun h => ⟨D.equivFin ⟨a,h⟩,by simp [enumerate]⟩⟩

/-- Local finiteness for the closure operator on sets. -/
theorem finite_acl (fin : FiniteTypes L M) {S : Set M} (hs : S.Finite) : (acl L S).Finite := by
  classical
  obtain ⟨D,rfl⟩ := hs.exists_finset_coe
  rw [← range_enumerate D,acl_range]
  exact finite_tupleClosure fin _

/-- Transitivity for the closure operator on arbitrary parameter sets follows
by collecting the finitely many finite lists of parameters witnessing algebraicity. -/
theorem acl_idempotent (fin : FiniteTypes L M) (S : Set M) : acl L (acl L S) = acl L S := by
  classical
  refine Set.Subset.antisymm ?_ (acl_extensive _)
  rintro a ⟨n,z,hz,ha⟩
  choose ar x inside mem using fun i => hz (Set.mem_range_self i)
  let T := ⋃ i : Fin n, Set.range (x i)
  have small : T.Finite := Set.finite_iUnion fun i => Set.finite_range (x i)
  obtain ⟨D,hD⟩ := small.exists_finset_coe
  let y := enumerate D
  have range : Set.range y = T := (range_enumerate D).trans hD
  have sub : T ⊆ S := Set.iUnion_subset inside
  have inc (i : Fin n) : Set.range (x i) ⊆ Set.range y := range ▸ Set.subset_iUnion (fun j => Set.range (x j)) i
  exact ⟨_,y,range.subset.trans sub,tuple_trans fin y z (fun i => tuple_mono _ y (inc i) (mem i)) ha⟩

end ProjectiveAlgebraic
