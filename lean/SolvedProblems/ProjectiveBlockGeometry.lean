module

public import SolvedProblems.ProjectivePregeometry
public import SolvedProblems.ProjectiveBlueprint
import SolvedProblems.ProjectiveCodeMatch

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ I : Type}

/-- Degeneracy means that the closure of each nonempty finite set is the union
of its singleton closures, as in the manuscript and Truss's definition. -/
def Degenerate (L : Language) (M : Type*) [L.Structure M] : Prop :=
  ∀ D : Finset M, D.Nonempty → acl L (D : Set M) = ⋃ x ∈ D, acl L {x}

/-- The displayed core enumerates algebraic closure of the empty set. The other
coordinates are disjoint blocks and enumerate each singleton closure off the core. -/
structure BlockChart (L : Language) {M : Type*} [L.Structure M] (core : κ → M)
    (B : I → Fin d → M) : Prop where
  core_exact : Set.range core = acl L ∅
  disjoint : Injective (layout core B)
  singleton_exact : ∀ t j, acl L {B t j} = Set.range core ∪ Set.range (B t)

/-- A set containing the core and stable under singleton closure is closed
under all algebraic closure in the degenerate case. -/
theorem closed_of_singletons (deg : Degenerate L M) (S : Set M) (core : acl L ∅ ⊆ S)
    (stable : ∀ a ∈ S, acl L {a} ⊆ S) : acl L S = S := by
  classical
  refine Set.Subset.antisymm ?_ (acl_extensive _)
  intro x hx
  obtain ⟨D,ds,mem⟩ := (acl_finite_character S x).mp hx
  rcases D.eq_empty_or_nonempty with rfl | h
  · exact core (by simpa using mem)
  · rw [deg D h] at mem
    obtain ⟨a,ad,hx⟩ := Set.mem_iUnion₂.mp mem
    exact stable _ (ds ad) hx

private theorem cl_of_mem (fin : FiniteTypes L M) (a : M) {S : Set M} (h : a ∈ acl L S) :
    acl L {a} ⊆ acl L S := (acl_mono (Set.singleton_subset_iff.mpr h)).trans (acl_idempotent fin S).subset

private theorem equal_cl (fin : FiniteTypes L M) (min : Minimal L M) {a x : M}
    (h : x ∈ acl L {a}) (outside : x ∉ acl L ∅) : acl L {x} = acl L {a} := by
  have back : a ∈ acl L {x} := by simpa using acl_exchange fin min ∅ (a := a) (b := x) (by simpa using h) outside
  exact Set.Subset.antisymm (cl_of_mem fin _ h) (cl_of_mem fin _ back)

theorem separated_points [Infinite M] (fin : FiniteTypes L M) :
    ∃ z : ℕ → M, (∀ i, z i ∉ acl L ∅) ∧ ∀ i j, i < j → z j ∉ acl L {z i} := by
  classical
  choose pick fresh using fun s : Finset M => (finite_acl fin s.finite_toSet).exists_notMem
  let seen : ℕ → Finset M := Nat.rec ∅ fun _ s => insert (pick s) s
  let z (i : ℕ) := pick (seen i)
  have inc : Monotone seen := monotone_nat_of_le_succ fun i => Finset.subset_insert _ _
  refine ⟨z,fun i h => fresh (seen i) (acl_mono (Set.empty_subset _) h),?_⟩
  intro i j lt h
  have member : z i ∈ seen j := inc (Nat.succ_le_of_lt lt) (Finset.mem_insert_self _ _)
  exact fresh (seen j) (acl_mono (Set.singleton_subset_iff.mpr member) h)

/-- Every infinite structure satisfying the finite-type and minimality hypotheses
has a finite algebraic core and countably many disjoint, equally sized,
enumerated singleton-closure blocks outside it. This concerns the external
first-order structure, including its actual finite definable sets. -/
theorem rawBlockChart [Infinite M] (fin : FiniteTypes L M) (min : Minimal L M) :
    ∃ (c d : ℕ) (_ : Fin d) (core : Fin c → M) (R : ℕ → Fin d → M), BlockChart L core R := by
  classical
  obtain ⟨z,out,apart⟩ := separated_points fin
  let C := acl L (∅ : Set M)
  have cf : C.Finite := finite_acl fin Set.finite_empty
  let Cset := cf.toFinset
  let core := enumerate Cset
  have ce : Set.range core = C := (range_enumerate Cset).trans cf.coe_toFinset
  have one (i : ℕ) : tupleClosure L (fun _ : Unit => z i) = acl L {z i} := by rw [← acl_range]; simp
  let S (i : ℕ) := acl L {z i} \ C
  have sf (i : ℕ) : (S i).Finite := (finite_acl fin (Set.finite_singleton _)).subset Set.sdiff_subset
  have si (i : ℕ) : z i ∈ S i := ⟨acl_extensive _ (Set.mem_singleton _),out i⟩
  have gen (i : ℕ) : tupleType L (fun _ : Unit => z i) = tupleType L (fun _ : Unit => z 0) := by
    let x : Empty → M := Empty.elim
    have base : tupleClosure L x = C := by rw [← acl_range,Set.range_eq_empty x]
    have m := generic_type min (x := x) (a := z i) (b := z 0)
      (fun h => out i (base.subset h)) (fun h => out 0 (base.subset h))
    exact match_subtuple m Sum.inr
  have sc (i : ℕ) : (S i).ncard = (S 0).ncard := by
    have eq := closure_card fin (gen i)
    rw [one,one] at eq
    have ci (j : ℕ) : C ⊆ acl L {z j} := acl_mono (Set.empty_subset _)
    rw [Set.ncard_def,Set.ncard_def]
    simp only [S,Set.encard_sdiff (ci _) cf,eq]
  let D (i : ℕ) := (sf i).toFinset
  let width := (D 0).card
  have wc (i : ℕ) : (D i).card = width := by
    simpa only [D,width,← Set.ncard_eq_toFinset_card] using sc i
  let e (i : ℕ) := (D i).equivFinOfCardEq (wc i)
  let R (i : ℕ) (j : Fin width) := ((e i).symm j).val
  have re (i : ℕ) : Set.range (R i) = S i := by
    ext a
    constructor
    · rintro ⟨j,rfl⟩
      exact (sf i).mem_toFinset.mp ((e i).symm j).property
    · intro h
      let w : D i := ⟨a,(sf i).mem_toFinset.mpr h⟩
      exact ⟨e i w,by simp [R,w]⟩
  have distinct {i j : ℕ} {x : M} (hx : x ∈ S i) (hy : x ∈ S j) : i = j := by
    have eq := (equal_cl fin min hx.1 hx.2).symm.trans (equal_cl fin min hy.1 hy.2)
    rcases lt_trichotomy i j with lt|rfl|gt
    · exact (apart i j lt (eq.symm.subset (si j).1)).elim
    · rfl
    · exact (apart j i gt (eq.subset (si i).1)).elim
  have rin (i) (j) : R i j ∈ S i := (re i).subset (Set.mem_range_self j)
  have wp : 0 < width := Finset.card_pos.mpr ⟨z 0,(sf 0).mem_toFinset.mpr (si 0)⟩
  refine ⟨Cset.card,width,⟨0,wp⟩,core,R,ce,?_,?_⟩
  · rintro (a|⟨i,t⟩) (b|⟨j,u⟩) eq
    · exact congrArg Sum.inl (Cset.equivFin.symm.injective (Subtype.ext eq))
    · change core a = R j u at eq
      exact ((rin j u).2 (eq ▸ ce.subset (Set.mem_range_self a))).elim
    · change R i t = core b at eq
      exact ((rin i t).2 (eq.symm ▸ ce.subset (Set.mem_range_self b))).elim
    · change R i t = R j u at eq
      have ij := distinct (rin i t) (eq.symm ▸ rin j u)
      subst j
      exact congrArg (fun p => Sum.inr (i,p)) ((e i).symm.injective (Subtype.ext eq))
  · intro i j
    rw [ce,re,equal_cl fin min (rin i j).1 (rin i j).2]
    exact (Set.union_sdiff_cancel (acl_mono (L := L) (Set.empty_subset _))).symm

end ProjectiveIndiscernibles
