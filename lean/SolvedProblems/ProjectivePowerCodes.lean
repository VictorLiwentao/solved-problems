module

public import SolvedProblems.ProjectiveSupportedModel

@[expose] public section

namespace ProjectiveSupports

open ProjectiveTransfer Set Function

variable {A : Type*} (G : Subgroup (Equiv.Perm A))

/-- The interpreted power set of the atoms. -/
abbrev Power := {S : Set A // Supported G S}

/-- Decode one flag and finite set as an actual subset. `true` denotes the
complement of the finite set. -/
def interpret : Bool × Finset A → Set A
  | (false,s) => s
  | (true,s) => (s : Set A)ᶜ

theorem fixed_mem (σ : Equiv.Perm A) (s : Finset A) (fix : Fixes σ s) (a : A) : σ a ∈ s ↔ a ∈ s := by
  constructor
  · intro h
    have eq := σ.injective (fix _ h)
    rwa [eq] at h
  · intro h
    rwa [fix _ h]

/-- Every finite or cofinite set has finite support. -/
theorem interpret_supported (x : Bool × Finset A) : Supported G (interpret x) := by
  rcases x with ⟨b,s⟩
  refine ⟨s,fun σ _ fix a => ?_⟩
  cases b
  · exact fixed_mem σ s fix a
  · exact not_congr (fixed_mem σ s fix a)

theorem interpret_inj [Infinite A] : Injective (interpret (A := A)) := by
  rintro ⟨b,s⟩ ⟨c,t⟩ eq
  have impossible (u v : Finset A) (h : (u : Set A) = (v : Set A)ᶜ) : False :=
    (v.finite_toSet.infinite_compl (h ▸ u.finite_toSet))
  cases b <;> cases c
  · exact congrArg (Prod.mk false) (Finset.coe_injective eq)
  · exact (impossible s t eq).elim
  · exact (impossible t s eq.symm).elim
  · exact congrArg (Prod.mk true) (Finset.coe_injective (compl_injective eq))

theorem interpret_surj (am : Amorphous G) (S : Power G) : ∃ x : Bool × Finset A, interpret x = S.val := by
  rcases am.2 S.val S.property with finite | cofin
  · exact ⟨(false,finite.toFinset),finite.coe_toFinset⟩
  · exact ⟨(true,cofin.toFinset),by simp [interpret,cofin.coe_toFinset]⟩

/-- Under internal amorphousness the code is unique. This equivalence concerns
the internal power set and commutes with permutations of the atoms. -/
noncomputable def powerEquiv (am : Amorphous G) : (Bool × Finset A) ≃ Power G := by
  let := am.1
  apply Equiv.ofBijective (fun x => ⟨interpret x,interpret_supported G x⟩)
  refine ⟨fun _ _ h => interpret_inj (congrArg Subtype.val h),?_⟩
  intro S
  obtain ⟨x,h⟩ := interpret_surj G am S
  exact ⟨x,Subtype.ext h⟩

/-- The componentwise version for finite powers. -/
noncomputable def powersEquiv (am : Amorphous G) (k : ℕ) : Codes A k ≃ (Fin k → Power G) :=
  Equiv.piCongrRight fun _ => powerEquiv G am

/-- The entire map graph is invariant when a finite support is fixed.
The image formulation uses actual subsets on both sides. -/
def SupportedPowerMap {k : ℕ} (F : (Fin k → Power G) → (Fin k → Power G)) (E : Finset A) : Prop :=
  ∀ σ ∈ G, Fixes σ E → ∀ x y, (∀ j, (y j).val = σ '' (x j).val) →
    ∀ j, (F y j).val = σ '' (F x j).val

private theorem natural {k : ℕ} (σ : Equiv.Perm A) (x : Codes A k) (j : Fin k) :
    interpret (decode σ x j) = σ '' interpret (x j) := by
  classical
  obtain ⟨b,s,eq⟩ : ∃ b s, x j = (b,s) := ⟨_,_,rfl⟩
  cases b
  · simp [decode,eq,interpret,Finset.coe_image]
  · simp [decode,eq,interpret,Finset.coe_image,Set.image_compl_eq σ.bijective]

/-- Transfer a supported map on the actual internal power set to a supported
map on finite/cofinite codes. -/
theorem supports_conjugate (am : Amorphous G) {k : ℕ} (F : (Fin k → Power G) → (Fin k → Power G))
    (E : Finset A) (supp : SupportedPowerMap G F E) :
    let e := powersEquiv G am k
    SupportedCodeMap G (fun x => e.symm (F (e x))) E := by
  let e := powersEquiv G am k
  change SupportedCodeMap G (fun x => e.symm (F (e x))) E
  intro σ hg fix x
  have perm (u : Codes A k) (j : Fin k) : (e (decode σ u) j).val = σ '' (e u j).val := natural σ u j
  have rel := supp σ hg fix (e x) (e (decode σ x)) (perm x)
  apply e.injective
  rw [e.apply_symm_apply]
  funext j
  apply Subtype.ext
  rw [perm,e.apply_symm_apply]
  exact rel j

end ProjectiveSupports
