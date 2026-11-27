module

public import SolvedProblems.ProjectiveBlockTransfer
public import SolvedProblems.ProjectiveChart
public import SolvedProblems.ProjectiveIndiscernibles
import SolvedProblems.ProjectiveCodeMatch
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Data.Rat.Denumerable

public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer ProjectiveBlocks Set Function

variable {k : ℕ} {M : Type*} [(graphLanguage k).Structure M]

@[instance_reducible] private def pull {P : Type*} (e : P → M) : (graphLanguage k).Structure P where
  funMap := fun {_} f => nomatch f
  RelMap := fun {_} r v => Structure.RelMap (L := graphLanguage k) r (e ∘ v)

/-- Tarski--Vaught for an infinite algebraically closed subset of this minimal
relational structure. A finite definable fibre is in algebraic closure of the
parameters, and a cofinite fibre meets the infinite subset. -/
private theorem elementary_pull {P : Type*} (e : P → M) (inj : Injective e) (large : (Set.range e).Infinite)
    (closed : acl (graphLanguage k) (Set.range e) = Set.range e) (min : Minimal (graphLanguage k) M) :
    letI := pull (k := k) e
    P ≅[graphLanguage k] M := by
  let := pull (k := k) e
  let embed : P ↪[graphLanguage k] M := {
    toEmbedding := ⟨e,inj⟩
    map_fun' := fun f => nomatch f
    map_rel' := fun _ _ => Iff.rfl }
  apply ElementaryEmbedding.elementarilyEquivalent
  apply embed.toElementaryEmbedding
  intro n φ v a ha
  let ix : Empty ⊕ Fin (n+1) → Fin n ⊕ Unit := Sum.elim Empty.elim (Fin.lastCases (.inr ()) Sum.inl)
  let ψ := φ.toFormula.relabel ix
  let p := e ∘ v
  have truth (z : M) : z ∈ locus (graphLanguage k) p ψ ↔ φ.Realize default (Fin.snoc p z) := by
    change (φ.toFormula.relabel ix).Realize _ ↔ _
    rw [Formula.realize_relabel,BoundedFormula.realize_toFormula]
    have cut : (point p z ∘ ix) ∘ Sum.inr = Fin.snoc p z := by
      funext j; refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp [ix,point]
    rw [cut,Unique.eq_default ((point p z ∘ ix) ∘ Sum.inl)]
  rcases min _ p ψ with small | cofin
  · have alg : a ∈ tupleClosure (graphLanguage k) p := ⟨ψ,(truth a).mpr ha,small⟩
    have mem : a ∈ Set.range e := closed.subset ⟨n,p,Set.range_comp_subset_range v e,alg⟩
    obtain ⟨x,rfl⟩ := mem
    exact ⟨x,ha⟩
  · obtain ⟨_,⟨x,rfl⟩,inside⟩ := large.exists_notMem_finite cofin
    exact ⟨x,(truth _).mp (Classical.not_not.mp inside)⟩

/-- The full positionwise symmetry of the induced countable structure follows
from total indiscernibility on finite blocks, including tuples containing core
points and repeated positions. -/
private theorem sequence_symmetry {c d : ℕ} (core : Fin c → M) (B : ℚ → Fin d → M) (name : ℕ ≃ ℚ)
    (full : ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ),
      tupleType (graphLanguage k) (marked core B m) = tupleType _ (marked core B (π ∘ m))) :
    letI := pull (k := k) (layout core (B ∘ name))
    BlockModel c d k := by
  let := pull (k := k) (layout core (B ∘ name))
  intro σ n r v
  let π := (name.symm.trans σ).trans name
  let idx (i : Fin n) : ℚ := match v i with | .inl _ => 0 | .inr (j,_) => name j
  let keep (i : Fin n) : Fin c ⊕ (Fin n × Fin d) := match v i with
    | .inl a => .inl a
    | .inr (_,j) => .inr (i,j)
  let e := layout core (B ∘ name)
  have raw : marked core B idx ∘ keep = e ∘ v := by
    funext i; cases h : v i <;> simp [idx,keep,e,marked,layout,h]
  have moved : marked core B (π ∘ idx) ∘ keep = e ∘ (relabel σ ∘ v) := by
    funext i; cases h : v i <;> simp [idx,keep,e,marked,layout,relabel,h,π]
  have m := match_subtuple (full idx π) keep
  rw [raw,moved] at m
  exact (match_relation m r.1 r.2).symm

/-- A closed union of rationally indexed, totally indiscernible enumerated
blocks and a finite core yields an elementary model with full block symmetry.
The proof applies the Tarski--Vaught test to the actual induced structure. -/
theorem elementaryOfSequence (min : Minimal (graphLanguage k) M) {c d : ℕ} (i₀ : Fin d)
    (core : Fin c → M) (B : ℚ → Fin d → M) (name : ℕ ≃ ℚ)
    (inj : Injective (layout core (B ∘ name)))
    (closed : acl (graphLanguage k) (Set.range (layout core (B ∘ name))) = Set.range (layout core (B ∘ name)))
    (full : ∀ {ι : Type} [Finite ι] (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ),
      tupleType (graphLanguage k) (marked core B m) = tupleType _ (marked core B (π ∘ m))) :
    ∃ s : (graphLanguage k).Structure (Point c d), letI := s
      (M ≅[graphLanguage k] Point c d) ∧ BlockModel c d k := by
  let e := layout core (B ∘ name)
  let : Nonempty (Fin d) := ⟨i₀⟩
  have large : (Set.range e).Infinite := Set.infinite_range_of_injective inj
  let := pull (k := k) e
  exact ⟨pull (k := k) e,(elementary_pull e inj large closed min).symm,sequence_symmetry core B name full⟩

/-- In the degenerate case the graph theory has an elementarily equivalent
countable model with a finite named core and uniform finite blocks, invariant
under the entire symmetric group of the blocks. -/
theorem symmetricBlockModel [Infinite M] (fin : FiniteTypes (graphLanguage k) M) (min : Minimal (graphLanguage k) M)
    (deg : Degenerate (graphLanguage k) M) :
    ∃ (c d : ℕ) (_ : Fin d) (s : (graphLanguage k).Structure (Point c d)),
      letI := s
      (M ≅[graphLanguage k] Point c d) ∧ BlockModel c d k := by
  classical
  obtain ⟨c,d,i₀,core,R,raw⟩ := rawBlockChart fin min
  obtain ⟨B,oi,base⟩ := extractOrderSequence fin core R
  have chart := inherit_chart fin raw base
  have full {ι : Type} [Finite ι] (m : ι → ℚ) (π : _root_.Equiv.Perm ℚ) :=
    totalIndiscernibility fin min core B i₀ oi (chart_independent fin deg chart i₀) (chart_algebraic chart i₀) m π
  let name := (Denumerable.eqv ℚ).symm
  let e := layout core (B ∘ name)
  have cut : e = layout core B ∘ Sum.map id (Prod.map name id) := by funext i; cases i <;> rfl
  have inj : Injective e := by
    rw [cut]
    apply chart.disjoint.comp
    rintro (a|⟨i,j⟩) (b|⟨t,u⟩) h <;> simp_all
  obtain ⟨s,eq,inv⟩ := elementaryOfSequence min i₀ core B name inj (chart_closed fin deg chart name) full
  exact ⟨c,d,i₀,s,eq,inv⟩

end ProjectiveIndiscernibles
