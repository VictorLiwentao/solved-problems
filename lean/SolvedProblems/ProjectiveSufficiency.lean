module

public import SolvedProblems.ProjectivePowerCodes
public import SolvedProblems.ProjectiveDifference

@[expose] public section

namespace ProjectiveSupports

open Function ProjectiveTransfer

variable {A : Type*} {G : Subgroup (Equiv.Perm A)}

/-- Internal dual Dedekind infinity of the finite power, expressed by the
existence of a supported surjective noninjective self-map. -/
def DuallyInfinitePower (G : Subgroup (Equiv.Perm A)) (k : ℕ) : Prop :=
  ∃ F : (Fin k → Power G) → (Fin k → Power G), (∃ E, SupportedPowerMap G F E) ∧ Surjective F ∧ ¬ Injective F

private theorem of_code (am : Amorphous G) {k : ℕ} (f : Codes A k → Codes A k) (E : Finset A)
    (support : SupportedCodeMap G f E) (onto : Surjective f) (collision : ¬ Injective f) : DuallyInfinitePower G k := by
  let e := powersEquiv G am k
  let F (x : Fin k → Power G) := e (f (e.symm x))
  refine ⟨F,⟨E,?_⟩,e.surjective.comp (onto.comp e.symm.surjective),?_⟩
  · intro σ hg fix x y eq j
    have perm (u : Codes A k) (i : Fin k) : (e (decode σ u) i).val = σ '' (e u i).val := by
      classical
      change interpret (decode σ u i) = σ '' interpret (u i)
      obtain ⟨b,s,cut⟩ : ∃ b s, u i = (b,s) := ⟨_,_,rfl⟩
      cases b <;> simp [decode,cut,interpret,Finset.coe_image,Set.image_compl_eq σ.bijective]
    have move : e.symm y = decode σ (e.symm x) := by
      apply e.injective
      rw [e.apply_symm_apply]
      funext i
      apply Subtype.ext
      rw [perm,e.apply_symm_apply,eq]
    change (e (f (e.symm y)) j).val = σ '' (e (f (e.symm x)) j).val
    rw [move,support _ hg fix,perm]
  · intro inj
    apply collision
    intro a b eq
    apply e.injective
    apply inj
    simp [F,eq]

/-- A single supported map on finite subsets acts on the finite part of the
chosen coordinate and keeps its flag and the remaining coordinates. -/
private def updatePart {k : ℕ} (j : Fin k) (g : Finset A → Finset A) (x : Codes A k) : Codes A k :=
  Function.update x j ((x j).1,g (x j).2)

/-- Projective type implies dual Dedekind infinity of every positive finite
power of the internal powerset. The explicit map replaces one finite part
`S` by `cl(S) \\ S`, preserving that coordinate's finite/cofinite flag. -/
theorem allPositivePowers (am : Amorphous G) {cl : Set A → Set A} (geom : Geometry G cl)
    (k : ℕ) (pos : 0 < k) : DuallyInfinitePower G k := by
  classical
  let := am.1
  let j : Fin k := ⟨0,pos⟩
  let g := flatDifference geom
  obtain ⟨⟨E,hs⟩,onto,collision⟩ := differenceSurjection geom
  apply of_code am (updatePart j g) E
  · intro σ hm fix x
    funext i
    by_cases eq : i = j
    · subst i
      apply Prod.ext
      · simp [updatePart,decode]
      · simpa [updatePart,decode,g,Finset.map_eq_image] using hs σ hm fix (x j).2
    · simp [updatePart,decode,eq]
  · intro y
    obtain ⟨s,hs⟩ := onto (y j).2
    refine ⟨Function.update y j ((y j).1,s),?_⟩
    funext i
    by_cases eq : i = j
    · subst i
      simp [updatePart,g,hs]
    · simp [updatePart,eq]
  · intro inj
    apply collision
    intro s t h
    let x (u : Finset A) : Codes A k := Function.update (fun _ => (false,∅)) j (false,u)
    have eq : updatePart j g (x s) = updatePart j g (x t) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [updatePart,x,g,h]
      · simp [updatePart,x,hi]
    have read := congrArg (fun v : Codes A k => (v j).2) (inj eq)
    simpa [x] using read

end ProjectiveSupports
