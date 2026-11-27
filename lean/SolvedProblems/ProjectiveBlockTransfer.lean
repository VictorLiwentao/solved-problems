module

public import SolvedProblems.ProjectiveBlocks
public import SolvedProblems.ProjectiveTransfer
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Set.Finite.Range

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveBlocks Function

/-- Permuting the blocks positionwise in the second structure preserves every
named first-order graph predicate. The core is pointwise fixed. -/
def BlockModel (c d k : ℕ) [(graphLanguage k).Structure (Point c d)] : Prop :=
  ∀ (σ : _root_.Equiv.Perm ℕ) {n : ℕ} (r : (graphLanguage k).Relations n) (v : Fin n → Point c d),
    Structure.RelMap r (relabel σ ∘ v) ↔ Structure.RelMap r v

private def blockAut {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k)
    (σ : _root_.Equiv.Perm ℕ) : Point c d ≃[graphLanguage k] Point c d where
  toEquiv := relabel σ
  map_fun' := fun f => nomatch f
  map_rel' := s σ

private def small {c d n : ℕ} : Fin c ⊕ (Fin n × Fin d) → Point c d :=
  Sum.map id fun a => (a.1.val, a.2)

/-- Every finite tuple lies in the permutation orbit of one using only as many
block indices as the length of the tuple. -/
private theorem normalize {c d : ℕ} {ι : Type} [Fintype ι] (v : ι → Point c d) :
    ∃ (σ : _root_.Equiv.Perm ℕ) (w : ι → Fin c ⊕ (Fin (Fintype.card ι) × Fin d)),
      relabel σ ∘ v = small ∘ w := by
  classical
  let tag (x : Point c d) : ℕ := Sum.elim (fun _ => 0) Prod.fst x
  let U := Finset.univ.image (tag ∘ v)
  have card : U.card ≤ Fintype.card ι := by simpa [U] using (Finset.card_image_le (f := tag ∘ v) (s := Finset.univ))
  let e := U.equivFin
  obtain ⟨σ,hσ⟩ := _root_.Equiv.Perm.exists_extending_pair (fun a : U => a.val)
    (fun a : U => (e a).val) Subtype.val_injective (Fin.val_injective.comp e.injective)
  have bound (i : ι) : σ (tag (v i)) < Fintype.card ι := by
    let a : U := ⟨_,Finset.mem_image_of_mem (tag ∘ v) (Finset.mem_univ i)⟩
    exact (hσ a).symm ▸ Nat.lt_of_lt_of_le (e a).isLt card
  have position (i : ι) : ∃ w, relabel σ (v i) = small (n := Fintype.card ι) w := by
    cases hx : v i with
    | inl t => exact ⟨.inl t,rfl⟩
    | inr t =>
      have h := bound i
      rw [hx] at h
      exact ⟨.inr (⟨σ t.1,h⟩,t.2),rfl⟩
  exact ⟨σ,fun i => (position i).choose, funext fun i => (position i).choose_spec⟩

private theorem blockTypes {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k) :
    FiniteTypes (graphLanguage k) (Point c d) := by
  intro ι _
  classical
  let := Fintype.ofFinite ι
  let T := Fin c ⊕ (Fin (Fintype.card ι) × Fin d)
  let ts (w : ι → T) := tupleType (graphLanguage k) (small ∘ w)
  apply (Set.finite_range ts).subset
  rintro _ ⟨v,rfl⟩
  obtain ⟨σ,w,hσ⟩ := normalize v
  refine ⟨w,?_⟩
  change tupleType _ (small ∘ w) = tupleType _ v
  rw [← hσ]
  ext φ
  exact StrongHomClass.realize_formula (blockAut s σ) φ

private theorem rename_decode {c d k : ℕ} (σ : _root_.Equiv.Perm ℕ) (x : Code c d k) :
    rename σ x = decode (relabel σ) x := by
  funext j
  apply Prod.ext
  · rfl
  · ext a
    simp only [rename,decode,Finset.mem_map,Finset.mem_image]
    rfl

private theorem rel_invariant {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k)
    (σ : _root_.Equiv.Perm ℕ) {x y : Code c d k} (h : recorded x y) : recorded (rename σ x) (rename σ y) := by
  obtain ⟨n,p,q,v,rfl,rfl,r⟩ := h
  exact ⟨n,p,q,relabel σ ∘ v, (rename_decode σ _ ▸ decode_comp _ _ _).symm,
    (rename_decode σ _ ▸ decode_comp _ _ _).symm, (s σ _ _).mpr r⟩

/-- The obstruction after passing to a countable symmetric block model. If a
surjection's graph structure is elementarily equivalent to such a model, the
original map is injective. No check on the number of tuple types or on the
lengths of the finite parts is assumed. -/
theorem obstructionOfBlockModel {M : Type*} (c d k : ℕ) (f : Codes M k → Codes M k)
    [(graphLanguage k).Structure (Point c d)] (model : BlockModel c d k) :
    letI := graphStructure f
    M ≅[graphLanguage k] (Point c d) → Surjective f → Injective f := by
  let := graphStructure f
  intro eq surj
  have finB := blockTypes model
  have fin : FiniteTypes (graphLanguage k) M := fun ι _ =>
    (realizedTypes_eq _ (Eq.symm eq) (finB ι)) ▸ finB ι
  obtain ⟨g,isGraph,sg,ig⟩ := transferGraph k f eq fin
  have equiv : Equivariant g := by
    intro σ x
    exact (isGraph _ _).mpr (rel_invariant model σ ((isGraph x _).mp rfl))
  exact ig.mpr <| (equivariantSurjection g equiv (sg.mp surj)).2

end ProjectiveTransfer
