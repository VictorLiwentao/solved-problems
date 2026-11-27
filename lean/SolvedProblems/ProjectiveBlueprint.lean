module

public import SolvedProblems.ProjectiveIndiscernibleModel
public import SolvedProblems.ProjectiveRamsey
import SolvedProblems.ProjectiveCodeMatch
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ ι J : Type}

/-- A block tuple, with the named finite core. The entries may have any finite index type. -/
def layout (core : κ → M) (v : ι → Fin d → M) := Sum.elim core fun ij : ι × Fin d => v ij.1 ij.2

/-- Equality of the complete joint block types, keeping the core fixed. -/
def Matched (L : Language) {M : Type*} [L.Structure M] (core : κ → M) (v w : ι → Fin d → M) :=
  tupleType L (layout core v) = tupleType L (layout core w)

theorem restrict_match {c : κ → M} {a b : ι → Fin d → M} (h : Matched L c a b) (f : J → ι) :
    Matched L c (a ∘ f) (b ∘ f) := by
  have m := match_subtuple h (Sum.map id (Prod.map f id))
  have cut (v : ι → Fin d → M) : layout c v ∘ Sum.map id (Prod.map f id) = layout c (v ∘ f) := by
    funext i; cases i <;> rfl
  rwa [cut,cut] at m

/-- The labels have identical order relations. -/
def SameOrder {A B : Type*} [LT A] [LT B] {ι : Type*} (p : ι → A) (q : ι → B) : Prop :=
  ∀ i j, p i < p j ↔ q i < q j

/-- Realize any prescribed ordering of a finite tuple inside an infinite subset of ℕ. -/
theorem ordered_labels {A : Type*} [LinearOrder A] {n : ℕ} (p : Fin n → A) (inj : Injective p)
    {S : Set ℕ} (inf : S.Infinite) : ∃ t : Fin n → ℕ, (∀ i, t i ∈ S) ∧ SameOrder p t := by
  classical
  let perm := Tuple.sort p
  have strict : StrictMono (p ∘ perm) := (Tuple.monotone_sort p).strictMono_of_injective (inj.comp perm.injective)
  let t (i : Fin n) := Nat.nth (· ∈ S) (perm.symm i).val
  refine ⟨t,fun i => Nat.nth_mem_of_infinite inf _,?_⟩
  intro i j
  have h := strict.lt_iff_lt (a := perm.symm i) (b := perm.symm j)
  simp only [Function.comp_apply,_root_.Equiv.apply_symm_apply] at h
  exact h.trans (Nat.nth_strictMono inf).lt_iff_lt.symm

private theorem matching_palette [Finite κ] (fin : FiniteTypes L M) (core : κ → M)
    (R : ℕ → Fin d → M) (n : ℕ) (S : Set ℕ) (inf : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∀ t u : Fin n → ℕ, Injective t → SameOrder t u →
      (∀ i, t i ∈ T) → (∀ i, u i ∈ T) → Matched L core (R ∘ t) (R ∘ u) := by
  classical
  let palette := typesIn L M (κ ⊕ (Fin n × Fin d))
  let := (fin _).to_subtype (s := palette)
  let col (t : Fin n → ℕ) : palette := ⟨tupleType L (layout core (R ∘ t)),⟨_,rfl⟩⟩
  obtain ⟨T,sub,large,c,h⟩ := ramseyTuples n col S inf
  refine ⟨T,sub,large,?_⟩
  intro t u inj order ti ui
  let perm := Tuple.sort t
  have st : StrictMono (t ∘ perm) := (Tuple.monotone_sort t).strictMono_of_injective (inj.comp perm.injective)
  have su : StrictMono (u ∘ perm) := fun i j ij => (order (perm i) (perm j)).mp (st ij)
  have eq := (h _ st (fun i => ti _)).trans (h _ su (fun i => ui _)).symm
  have m : Matched L core (R ∘ t ∘ perm) (R ∘ u ∘ perm) := congrArg Subtype.val eq
  have undo := restrict_match m perm.symm
  have cancel (v : Fin n → ℕ) : (R ∘ v ∘ perm) ∘ perm.symm = R ∘ v := by funext i; simp
  rwa [cancel,cancel] at undo

/-- A descending sequence of infinite sets, with the complete type of each
finite length determined by the order on its corresponding set. -/
theorem homogeneous_levels [Finite κ] (fin : FiniteTypes L M) (core : κ → M) (R : ℕ → Fin d → M) :
    ∃ H : ℕ → Set ℕ, Antitone H ∧ (∀ n, (H n).Infinite) ∧
      ∀ n (t u : Fin n → ℕ), Injective t → SameOrder t u → (∀ i, t i ∈ H n) → (∀ i, u i ∈ H n) →
        Matched L core (R ∘ t) (R ∘ u) := by
  classical
  let Host := {S : Set ℕ // S.Infinite}
  have step (n : ℕ) (S : Host) : ∃ T : Host, T.val ⊆ S.val ∧
      ∀ t u : Fin n → ℕ, Injective t → SameOrder t u → (∀ i, t i ∈ T.val) → (∀ i, u i ∈ T.val) →
        Matched L core (R ∘ t) (R ∘ u) := by
    obtain ⟨T,sub,large,h⟩ := matching_palette fin core R n S.val S.property
    exact ⟨⟨T,large⟩,sub,h⟩
  choose next sub same using step
  let seq : ℕ → Host := Nat.rec ⟨Set.univ,Set.infinite_univ⟩ (fun n s => next (n+1) s)
  refine ⟨fun n => (seq n).val,antitone_nat_of_succ_le fun n => sub _ _,fun n => (seq n).property,?_⟩
  intro n
  cases n with
  | zero => intro t u _ _ _ _; exact (Subsingleton.elim t u) ▸ rfl
  | succ n => exact same _ (seq n)

end ProjectiveIndiscernibles
