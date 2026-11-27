module

public import SolvedProblems.ProjectiveStage
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ : Type}

/-- Every finite tuple of distinct enumerated blocks in the new sequence has
the complete joint type of a tuple of distinct original enumerated blocks. -/
def BasedOn (L : Language) {M : Type*} [L.Structure M] (c : κ → M)
    (R : ℕ → Fin d → M) (B : ℚ → Fin d → M) : Prop :=
  ∀ {n : ℕ} (p : Fin n → ℚ), Injective p → ∃ t : Fin n → ℕ, Injective t ∧ Matched L c (B ∘ p) (R ∘ t)

private theorem from_prefix (c : κ → M) (R : ℕ → Fin d → M) (H : ℕ → Set ℕ) (down : Antitone H)
    (name : ℕ ≃ ℚ) (B : ℚ → Fin d → M) (st : ∀ n, Stage L c R H name n (fun i : Fin n => B (name i.val)))
    {n : ℕ} (p : Fin n → ℚ) : ∃ t : Fin n → ℕ, (∀ i, t i ∈ H n) ∧ SameOrder p t ∧ Matched L c (B ∘ p) (R ∘ t) := by
  classical
  let idx (i : Fin n) := name.symm (p i)
  let N := max n (Finset.univ.sup idx + 1)
  have bound (i : Fin n) : idx i < N := (Nat.lt_succ_of_le (Finset.le_sup (s := Finset.univ) (Finset.mem_univ i))).trans_le (le_max_right _ _)
  let pos (i : Fin n) : Fin N := ⟨idx i,bound i⟩
  obtain ⟨t,ins,ord,match'⟩ := st N
  have matchProof := restrict_match match' pos
  have shape : (fun i : Fin N => B (name i.val)) ∘ pos = B ∘ p := by funext i; simp [pos,idx]
  rw [shape] at matchProof
  refine ⟨t ∘ pos,fun i => down (le_max_left _ _) (ins (pos i)),?_,matchProof⟩
  intro i j
  simpa [pos,idx] using ord (pos i) (pos j)

/-- Construct rationally indexed order indiscernibles over the finite core.
Finite Ramsey thinning determines compatible joint types. Finite-type
extension then realizes the enumeration one new block at a time in the
source structure. -/
theorem extractOrderSequence [Finite κ] (fin : FiniteTypes L M) (core : κ → M) (R : ℕ → Fin d → M) :
    ∃ B : ℚ → Fin d → M, OrderIndiscernible L core B ∧ BasedOn L core R B := by
  classical
  let name := (Denumerable.eqv ℚ).symm
  obtain ⟨H,down,inf,hom⟩ := homogeneous_levels fin core R
  obtain ⟨B,st⟩ := assemble_stages fin core R H down inf hom name
  have realize {n : ℕ} (p : Fin n → ℚ) := from_prefix core R H down name B st p
  refine ⟨B,?_,?_⟩
  · intro ι hι m f hf
    let := Fintype.ofFinite ι
    let D := Finset.univ.image m
    let p (i : Fin D.card) : ℚ := (D.equivFin.symm i).val
    let r (i : ι) := D.equivFin ⟨m i,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    have cut : p ∘ r = m := by funext i; simp [p,r]
    obtain ⟨t,ti,ord,mb⟩ := realize p
    obtain ⟨u,ui,ord',mb'⟩ := realize (f ∘ p)
    have pinj : Injective p := Subtype.val_injective.comp D.equivFin.symm.injective
    have oo : SameOrder t u := fun i j => (ord i j).symm.trans (hf.lt_iff_lt.symm.trans (ord' i j))
    have mm : Matched L core (B ∘ p) (B ∘ (f ∘ p)) := mb.trans ((hom _ t u (order_inj pinj ord) oo ti ui).trans mb'.symm)
    have small := restrict_match mm r
    change Matched L core (B ∘ m) (B ∘ f ∘ m)
    simpa only [Function.comp_assoc,cut] using small
  · intro n p hp
    obtain ⟨t,_,ord,mat⟩ := realize p
    exact ⟨t,order_inj hp ord,mat⟩

end ProjectiveIndiscernibles
