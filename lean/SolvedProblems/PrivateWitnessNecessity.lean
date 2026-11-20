module

public import SolvedProblems.PrivateWitnessTransfer
public import SolvedProblems.PrivateWitnessError

public section
namespace PrivateWitness
open scoped NNReal ENNReal

/-- Finite families always admit a finite negative witness once any member is in the support. -/
private theorem finite_witness (Ls : List (Set Nat)) (p : Law) :
    ∃ T : Finset Nat, (∀ x ∈ T, x ∉ p.support) ∧ ∀ L ∈ Ls, ¬ L ⊆ p.support → ∃ x ∈ T, x ∈ L := by
  classical
  induction Ls with
  | nil => exact ⟨∅,by simp,by simp⟩
  | cons L tl ih =>
    obtain ⟨T,out,hits⟩ := ih
    by_cases inside : L ⊆ p.support
    · refine ⟨T,out,?_⟩
      intro J h nsub
      rcases List.mem_cons.mp h with rfl|h
      · exact (nsub inside).elim
      · exact hits _ h nsub
    · obtain ⟨x,hL,hx⟩ := Set.not_subset.mp inside
      refine ⟨insert x T,?_,?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl|ha
        · exact hx
        · exact out _ ha
      · intro J hj nsub
        rcases List.mem_cons.mp hj with rfl|hj
        · exact ⟨x,Finset.mem_insert_self ..,hL⟩
        · obtain ⟨a,ha,hJ⟩ := hits J hj nsub
          exact ⟨a,Finset.mem_insert_of_mem ha,hJ⟩

/-- All points not belonging to every processed language. -/
private def bad (part : List (Set Nat)) : Set Nat := {x | ∃ L ∈ part, x ∉ L}

theorem common_infinite (Ls : List (Set Nat)) (ne : Ls ≠ []) (inf : ∀ L ∈ Ls, L.Infinite)
    {G : Rule} {k : ℝ≥0} (priv : Private G k)
    (success : ∀ p, Admissible Ls p → Exponential (error G p)) :
    {x | ∀ L ∈ Ls, x ∈ L}.Infinite := by
  classical
  obtain ⟨L0,h0⟩ := List.exists_mem_of_ne_nil Ls ne
  obtain ⟨p0,eq0⟩ := supported (inf L0 h0).nonempty
  let familyLaw (p : Law) := ∃ L ∈ Ls, L ⊆ p.support
  have process (part : List (Set Nat)) (sub : ∀ L ∈ part, L ∈ Ls) :
      ∃ p : Law, familyLaw p ∧ Exponential (output G p (bad part)) := by
    induction part with
    | nil =>
      exact ⟨p0,⟨L0,h0,eq0 ▸ Set.Subset.rfl⟩,by simpa [bad] using exp_empty G p0⟩
    | cons L tl ih =>
      obtain ⟨p,⟨J,hJ,jsub⟩,hold⟩ := ih (fun K hk => sub K (List.mem_cons_of_mem _ hk))
      have memL := sub L (List.mem_cons_self ..)
      obtain ⟨q,qs,finite,hq⟩ := transferSupport priv p ((inf J hJ).mono jsub) L (bad tl)
        (inf L memL).nonempty hold
      have hp := success q ⟨⟨L,memL,qs⟩,finite_witness _ _⟩
      refine ⟨q,⟨L,memL,qs⟩,?_⟩
      apply subevent _ (exp_union (exp_outside priv q hp L finite) hq)
      rintro x ⟨K,hk,notK⟩
      rcases List.mem_cons.mp hk with rfl|hk
      · exact Or.inl notK
      · exact Or.inr ⟨K,hk,notK⟩
  obtain ⟨p,⟨J,hJ,jsub⟩,out⟩ := process Ls (fun _ h => h)
  intro finite
  have hp := success p ⟨⟨J,hJ,jsub⟩,finite_witness _ _⟩
  have inner := exp_finite priv p hp finite (fun _ hx => jsub (hx J hJ))
  apply not_exp_univ G p
  apply subevent _ (exp_union inner out)
  intro x _
  by_cases hx : ∀ L ∈ Ls, x ∈ L
  · exact Or.inl hx
  · push Not at hx
    exact Or.inr hx

end PrivateWitness
