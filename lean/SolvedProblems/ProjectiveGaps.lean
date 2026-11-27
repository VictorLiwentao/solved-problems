module

public import SolvedProblems.ProjectiveMarkedTypes
import SolvedProblems.ProjectiveOrderSeparation
import SolvedProblems.ProjectiveCodeMatch
import Mathlib.Data.Fintype.Option

public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {d : ℕ} {M : Type*} [L.Structure M] {κ ι : Type} [Finite κ] [Finite ι]

omit [Finite κ] in
private theorem over_moves {core : κ → M} {B : ℚ → Fin d → M} (oi : OrderIndiscernible L core B)
    (m : ι → ℚ) (s : ℚ) (f : ℚ → ℚ) (hf : StrictMono f) :
    overMarks L core B m s = overMarks L core B (f ∘ m) (f s) := by
  let aug (v : ι → ℚ) (u : ℚ) : Option ι → ℚ := fun | .none => u | .some j => v j
  let keep : (κ ⊕ (ι × Fin d)) ⊕ Fin d → κ ⊕ (Option ι × Fin d) :=
    Sum.elim (Sum.map id fun e => (some e.1,e.2)) fun j => Sum.inr (none,j)
  have cut (v : ι → ℚ) (u : ℚ) : marked core B (aug v u) ∘ keep = Sum.elim (marked core B v) (B u) := by
    funext p
    rcases p with (c|p)|j <;> rfl
  have cmap : f ∘ aug m s = aug (f ∘ m) (f s) := by funext p; cases p <;> rfl
  have h := match_subtuple (oi (aug m s) f hf) keep
  rwa [cmap,cut,cut] at h

omit [Finite κ] [Finite ι] in
private theorem over_restrict {β : Type} {core : κ → M} {B : ℚ → Fin d → M} (m : β → ℚ)
    {s t : ℚ} (eq : overMarks L core B m s = overMarks L core B m t) (subset : ι → β) :
    overMarks L core B (m ∘ subset) s = overMarks L core B (m ∘ subset) t := by
  let keep : (κ ⊕ (ι × Fin d)) ⊕ Fin d → (κ ⊕ (β × Fin d)) ⊕ Fin d :=
    Sum.map (Sum.map id (Prod.map subset id)) id
  have cut (u : ℚ) : Sum.elim (marked core B m) (B u) ∘ keep = Sum.elim (marked core B (m ∘ subset)) (B u) := by
    funext p; rcases p with (c|p)|j <;> rfl
  have h := match_subtuple eq keep
  rwa [cut,cut] at h

private theorem no_gaps_lt (fin : FiniteTypes L M) (min : Minimal L M)
    (core : κ → M) (B : ℚ → Fin d → M) (i₀ : Fin d) (oi : OrderIndiscernible L core B)
    (indep : IndependentBlocks L core B i₀) (alg : AlgebraicBlocks L B i₀)
    (m : ι → ℚ) {u v : ℚ} (uv : u < v) (fu : u ∉ Set.range m) (fv : v ∉ Set.range m) :
    overMarks L core B m u = overMarks L core B m v := by
  classical
  by_contra different
  let bound := (tupleClosure L (fun _ : Unit => B (center 0) i₀)).ncard ^ d
  let I := Fin (bound+1)
  let allMarks (p : I × I × ι) := movePair u v p.1.val p.2.1.val (m p.2.2)
  have fresh (l : ℕ) : center l ∉ Set.range allMarks := by
    rintro ⟨p,eq⟩
    exact movePair_avoids (i := p.1.val) (j := p.2.1.val)
      (fun e => fu ⟨p.2.2,e⟩) (fun e => fv ⟨p.2.2,e⟩) eq
  have distinct {i j : I} (ij : i < j) :
      overMarks L core B allMarks (center i.val) ≠ overMarks L core B allMarks (center j.val) := by
    intro eq
    let f := movePair u v i.val j.val
    have rest := over_restrict allMarks eq (fun l : ι => (i,j,l))
    change overMarks L core B (f ∘ m) (center i.val) = overMarks L core B (f ∘ m) (center j.val) at rest
    have m₁ := over_moves oi m u f (movePair_strict ij)
    have m₂ := over_moves oi m v f (movePair_strict ij)
    rw [show f u = center i.val from movePair_left uv _ _] at m₁
    rw [show f v = center j.val from movePair_right _ _ _ _] at m₂
    exact different (m₁.trans (rest.trans m₂.symm))
  have inj : Injective (fun i : I => overMarks L core B allMarks (center i.val)) := by
    intro i j h
    rcases lt_trichotomy i j with lt | eq | gt
    · exact (distinct lt h).elim
    · exact eq
    · exact (distinct gt h.symm).elim
  have contradiction := markedTypeBound fin min core B i₀ indep alg allMarks (center 0) (fresh 0)
    (fun i : I => center i.val) (fun i => fresh i.val) inj
  exact Nat.not_succ_le_self bound contradiction

/-- With a finite core and algebraic enumerations of blocks, order-indiscernible
blocks in independent positions have the same type over any finite set of
other marked blocks, regardless of which gaps in the order they occupy. -/
theorem sameOverMarks (fin : FiniteTypes L M) (min : Minimal L M) (core : κ → M) (B : ℚ → Fin d → M)
    (i₀ : Fin d) (oi : OrderIndiscernible L core B) (indep : IndependentBlocks L core B i₀)
    (alg : AlgebraicBlocks L B i₀) (m : ι → ℚ) {u v : ℚ} (hu : u ∉ Set.range m) (hv : v ∉ Set.range m) :
    overMarks L core B m u = overMarks L core B m v := by
  rcases lt_trichotomy u v with lt | rfl | gt
  · exact no_gaps_lt fin min core B i₀ oi indep alg m lt hu hv
  · rfl
  · exact (no_gaps_lt fin min core B i₀ oi indep alg m gt hv hu).symm

end ProjectiveIndiscernibles
