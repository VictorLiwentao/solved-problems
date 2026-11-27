module

public import SolvedProblems.ProjectiveIndiscernibleModel
import SolvedProblems.ProjectiveCodeMatch
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {d : ℕ} {M : Type*} [L.Structure M] {κ ι : Type} [Finite κ] [Finite ι]

/-- Once a marked tuple is held fixed, all generic new distinguished points
can be matched to the same point. Their full enumerations then have only
finitely many possible images, bounded independently of the markers. -/
theorem markedTypeBound (fin : FiniteTypes L M) (min : Minimal L M)
    (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) (indep : IndependentBlocks L core B i₀)
    (alg : AlgebraicBlocks L B i₀) (m : ι → ℚ) (s : ℚ) (fresh : s ∉ Set.range m)
    {n : ℕ} (t : Fin n → ℚ) (free : ∀ i, t i ∉ Set.range m)
    (diff : Injective fun i => overMarks L core B m (t i)) :
    n ≤ (tupleClosure L (fun _ : Unit => B s i₀)).ncard ^ d := by
  classical
  let p := marked core B m
  let A := tupleClosure L (fun _ : Unit => B s i₀)
  have move (i : Fin n) : ∃ v : Fin d → M, (∀ j, v j ∈ A) ∧
      overMarks L core B m (t i) = tupleType L (Sum.elim p v) := by
    have same := generic_type min (indep m _ (free i)) (indep m _ fresh)
    obtain ⟨v,joint⟩ := extendTuple L (Eq.refl _) (fin (((κ ⊕ (ι × Fin d)) ⊕ Unit) ⊕ Fin d)) same (B (t i))
    refine ⟨v,?_,?_⟩
    · intro j
      let keep : Unit ⊕ Unit → ((κ ⊕ (ι × Fin d)) ⊕ Unit) ⊕ Fin d :=
        Sum.elim (fun _ => Sum.inl (Sum.inr ())) (fun _ => Sum.inr j)
      have h := match_subtuple joint keep
      have cut (u : M) (v : Fin d → M) : Sum.elim (point p u) v ∘ keep = point (fun _ : Unit => u) (v j) := by
        funext q; cases q <;> rfl
      rw [cut,cut] at h
      exact (algebraic_match fin h).mp (alg _ j)
    · let keep : (κ ⊕ (ι × Fin d)) ⊕ Fin d → ((κ ⊕ (ι × Fin d)) ⊕ Unit) ⊕ Fin d :=
        Sum.map Sum.inl id
      have h := match_subtuple joint keep
      have cut (u : M) (v : Fin d → M) : Sum.elim (point p u) v ∘ keep = Sum.elim p v := by
        funext q; cases q <;> rfl
      rwa [cut,cut] at h
  choose v inside hv using move
  let tag (i : Fin n) (j : Fin d) : A := ⟨v i j,inside i j⟩
  have inj : Injective tag := by
    intro i j h
    have eq : v i = v j := funext fun l => congrArg Subtype.val (congrFun h l)
    apply diff
    change overMarks L core B m (t i) = overMarks L core B m (t j)
    rw [hv i,hv j,eq]
  let := (finite_tupleClosure fin (fun _ : Unit => B s i₀)).fintype
  have le := Fintype.card_le_of_injective tag inj
  simpa only [Fintype.card_fin,Fintype.card_fun,Set.fintypeCard_eq_ncard,A] using le

end ProjectiveIndiscernibles
