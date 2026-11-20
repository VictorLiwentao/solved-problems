module

public import SolvedProblems.WellOrderUnionModel
import SolvedProblems.WellOrderUnionMatching
import SolvedProblems.WellOrderUnionGroup
import Mathlib.Logic.Equiv.Sigma
import Mathlib.Data.Nat.Pairing

public section
namespace WellOrderUnion

open Equiv Function

private abbrev Cell {A : Type u} (P : A → ℕ) (i : ℕ) := {x // P x = i}

private def assemble {A : Type u} {P : A → ℕ} (v : ∀ i, Perm (Cell P i)) : Perm A :=
  (sigmaFiberEquiv P).permCongr (sigmaCongrRight v)

private theorem assemble_at {A : Type u} {P : A → ℕ} (v : ∀ i, Perm (Cell P i))
    {i : ℕ} (x : Cell P i) : assemble v x.val = (v i x).val := by
  obtain ⟨x,rfl⟩ := x
  rfl

private theorem assemble_preserves {A : Type u} {P : A → ℕ} (v : ∀ i, Perm (Cell P i)) :
    Preserves P (assemble v) :=
  fun x => (v (P x) ⟨x,rfl⟩).prop

private def restrict {A : Type u} {P : A → ℕ} (g : Perm A) (hg : Preserves P g) (i : ℕ) :
    Perm (Cell P i) := g.subtypePerm (fun x => by rw [hg x])

private theorem restrict_val {A : Type u} {P : A → ℕ} (g : Perm A) (hg : Preserves P g)
    {i : ℕ} (x : Cell P i) : (restrict g hg i x).val = g x.val := rfl

/-- This second color singles out every atom in every countable block simultaneously. -/
private noncomputable def label {A : Type u} (P : A → ℕ) (i : ℕ) : Cell P i → ℕ :=
  open Classical in
  if h : Countable (Cell P i) then (@Countable.exists_injective_nat (Cell P i) h).choose
    else fun _ => 0

private theorem label_inj {A : Type u} {P : A → ℕ} {i : ℕ} (h : Countable (Cell P i)) :
    Injective (label P i) := by
  simpa only [label, dite_eq_left h] using (@Countable.exists_injective_nat (Cell P i) h).choose_spec

private def Hidden {A : Type u} (P Q : A → ℕ) (g : Perm A) : Prop :=
  ∃ s : Perm A, Preserves P s ∧ ∀ x, Q (s (g x)) = Q (s x)

/-- Conjugators can be chosen in every block in the ambient universe and assembled
into one permutation. The number of factors is uniform across the blocks. -/
private theorem assemble_hidden {A : Type u} {P Q : A → ℕ} (v : ∀ i, Perm (Cell P i))
    (hv : ∀ i, Hides (fun x : Cell P i => Q x.val) (v i)) : Hidden P Q (assemble v) := by
  classical
  simp only [Hides] at hv
  choose h hh using hv
  refine ⟨assemble h,assemble_preserves h, fun x => ?_⟩
  let y : Cell P (P x) := ⟨x,rfl⟩
  change Q (assemble h (assemble v y.val)) = Q (assemble h y.val)
  rw [assemble_at, assemble_at, assemble_at]
  exact hh _ _

/-- The refinement depends only on P. For every further coloring Q its stabilizer
is large enough, after taking conjugates inside the original block stabilizer,
to generate every permutation preserving the refinement. -/
private theorem common_support {A : Type u} (P : A → ℕ) :
    ∃ R : A → ℕ, ∀ (g : Perm A), Preserves R g → ∀ Q : A → ℕ,
      ∃ a b c d : Perm A, Hidden P Q a ∧ Hidden P Q b ∧ Hidden P Q c ∧ Hidden P Q d ∧
        g = (a*b)*(c*d) := by
  classical
  let R (x : A) := Nat.pair (P x) (label P (P x) ⟨x,rfl⟩)
  refine ⟨R,fun g hr Q => ?_⟩
  have pieces (x : A) := Nat.pair_eq_pair.mp (hr x)
  have hg : Preserves P g := fun x => (pieces x).1
  let p := restrict g hg
  have pin (i : ℕ) (h : Countable (Cell P i)) : p i = 1 := by
    apply Equiv.ext
    intro y
    apply label_inj h
    change label P i (p i y) = label P i y
    obtain ⟨x,rfl⟩ := y
    have aux (j : ℕ) (z : Cell P j) : label P (P z.val) ⟨z.val,rfl⟩ = label P j z := by
      obtain ⟨u,rfl⟩ := z
      rfl
    exact (aux _ (p _ ⟨x,rfl⟩)).symm.trans (pieces x).2
  have parts (i : ℕ) :
      ∃ a b c d : Perm (Cell P i), Hides (fun x => Q x.val) a ∧ Hides (fun x => Q x.val) b ∧
       Hides (fun x => Q x.val) c ∧ Hides (fun x => Q x.val) d ∧ p i = (a*b)*(c*d) := by
    by_cases h : Countable (Cell P i)
    · have one : Hides (fun x : Cell P i => Q x.val) 1 := ⟨1,fun _ => rfl⟩
      exact ⟨1,1,1,1,one,one,one,one,by simp [pin i h]⟩
    · have : Uncountable (Cell P i) := not_countable_iff.mp h
      obtain ⟨e,he⟩ := coloredTriples (fun x : Cell P i => Q x.val)
      exact four_hidden _ e he _
  choose a b c d ha hb hc hd factor using parts
  refine ⟨assemble a,assemble b,assemble c,assemble d,assemble_hidden _ ha,
    assemble_hidden _ hb,assemble_hidden _ hc,assemble_hidden _ hd,?_⟩
  ext x
  let y : Cell P (P x) := ⟨x,rfl⟩
  change (p _ y).val = (assemble a * assemble b * (assemble c * assemble d)) y.val
  rw [factor (P x)]
  simp only [Perm.mul_apply,assemble_at]

theorem simultaneous_fixing {A : Type u} {X : Type v} (act : Perm A →* Perm X) (P : A → ℕ) :
    ∃ R : A → ℕ, ∀ S : Set X,
      (∀ g : Perm A, Preserves P g → act g '' S = S) →
      (∃ Q : A → ℕ, ∀ g : Perm A, Preserves Q g → ∀ x ∈ S, act g x = x) →
        ∀ g : Perm A, Preserves R g → ∀ x ∈ S, act g x = x := by
  obtain ⟨R,hr⟩ := common_support P
  refine ⟨R, fun S closed ⟨Q,hQ⟩ g hg => ?_⟩
  have fixes (v : Perm A) (good : Hidden P Q v) (x : X) (hx : x ∈ S) : act v x = x := by
    obtain ⟨s,hp,hs⟩ := good
    have hq : Preserves Q (s*v*s⁻¹) := by
      intro y
      obtain ⟨z,rfl⟩ := s.surjective y
      simpa using hs z
    have mem : act s x ∈ S := closed s hp ▸ Set.mem_image_of_mem (act s) hx
    have fixed := hQ _ hq _ mem
    apply (act s).injective
    simpa using fixed
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hg'⟩ := hr g hg Q
  intro x hx
  rw [hg']
  simp only [map_mul, Perm.mul_apply, fixes d hd x hx, fixes c hc x hx, fixes b hb x hx,
    fixes a ha x hx]

end WellOrderUnion
