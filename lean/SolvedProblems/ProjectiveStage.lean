module

public import SolvedProblems.ProjectiveBlueprint
import SolvedProblems.ProjectiveCodeMatch
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Fintype.Prod

public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ : Type}

/-- Complete type of the first `n` enumerated positions, modeled by labels on the `n`th level. -/
@[expose] def Stage (L : Language) {M : Type*} [L.Structure M] (c : κ → M)
    (R : ℕ → Fin d → M) (H : ℕ → Set ℕ) (name : ℕ ≃ ℚ) (n : ℕ) (v : Fin n → Fin d → M) : Prop :=
  ∃ t : Fin n → ℕ, (∀ i, t i ∈ H n) ∧ SameOrder (fun i : Fin n => name i.val) t ∧ Matched L c v (R ∘ t)

theorem order_inj {A B ι : Type*} [LinearOrder A] [LinearOrder B] {p : ι → A} {t : ι → B}
    (inj : Injective p) (eq : SameOrder p t) : Injective t := by
  intro i j h
  apply inj
  rcases lt_trichotomy (p i) (p j) with lt|eq'|gt
  · exact (h.not_lt ((eq i j).mp lt)).elim
  · exact eq'
  · exact (h.symm.not_lt ((eq j i).mp gt)).elim

/-- Replace the last position in an encoded block tuple by a new tuple of point matches. -/
private theorem put_last {n : ℕ} (c : κ → M) {s t : Fin (n+1) → Fin d → M}
    (m : tupleType L (Sum.elim (layout c (s ∘ Fin.castSucc)) (s (Fin.last n))) =
      tupleType L (Sum.elim (layout c (t ∘ Fin.castSucc)) (t (Fin.last n)))) : Matched L c s t := by
  let keep : κ ⊕ (Fin (n+1) × Fin d) → (κ ⊕ (Fin n × Fin d)) ⊕ Fin d :=
    Sum.elim (fun x => .inl (.inl x)) fun ij =>
      Fin.lastCases (.inr ij.2) (fun i => .inl (.inr (i,ij.2))) ij.1
  have cut (v : Fin (n+1) → Fin d → M) :
      Sum.elim (layout c (v ∘ Fin.castSucc)) (v (Fin.last n)) ∘ keep = layout c v := by
    funext i
    rcases i with j|⟨j,t⟩
    · rfl
    · refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp [keep,layout]
  have h := match_subtuple m keep
  rwa [cut,cut] at h

private theorem step_stage [Finite κ] (fin : FiniteTypes L M) (c : κ → M) (R : ℕ → Fin d → M)
    (H : ℕ → Set ℕ) (down : Antitone H) (inf : ∀ n, (H n).Infinite)
    (hom : ∀ n (t u : Fin n → ℕ), Injective t → SameOrder t u → (∀ i, t i ∈ H n) →
      (∀ i, u i ∈ H n) → Matched L c (R ∘ t) (R ∘ u))
    (name : ℕ ≃ ℚ) (n : ℕ) (v : Fin n → Fin d → M) (stage : Stage L c R H name n v) :
    ∃ w : Fin (n+1) → Fin d → M, Stage L c R H name (n+1) w ∧ ∀ i, w i.castSucc = v i := by
  classical
  obtain ⟨t,ti,ord,mat⟩ := stage
  obtain ⟨u,ui,ordU⟩ := ordered_labels (fun i : Fin (n+1) => name i.val)
    (name.injective.comp Fin.val_injective) (inf (n+1))
  let old := u ∘ Fin.castSucc
  have oo : SameOrder t old := fun i j => (ord i j).symm.trans (ordU i.castSucc j.castSucc)
  have eq := hom n t old (order_inj (name.injective.comp Fin.val_injective) ord) oo ti
    (fun i => down (Nat.le_succ n) (ui i.castSucc))
  have base : Matched L c (R ∘ old) v := Eq.symm (mat.trans eq)
  obtain ⟨z,all⟩ := extendTuple L (Eq.refl _) (fin ((κ ⊕ (Fin n × Fin d)) ⊕ Fin d)) base (R (u (Fin.last n)))
  let w : Fin (n+1) → Fin d → M := Fin.snoc v z
  have pre : w ∘ Fin.castSucc = v := by funext i; simp [w]
  have end' : w (Fin.last n) = z := by simp [w]
  refine ⟨w,⟨u,ui,ordU,?_⟩,fun i => congrFun pre i⟩
  apply Eq.symm
  apply put_last
  rw [pre,end']
  exact all

/-- Assemble coherent stages in the original homogeneous structure. Every
finite prefix agrees with a tuple from the corresponding homogeneous level. -/
theorem assemble_stages [Finite κ] (fin : FiniteTypes L M) (c : κ → M) (R : ℕ → Fin d → M)
    (H : ℕ → Set ℕ) (down : Antitone H) (inf : ∀ n, (H n).Infinite)
    (hom : ∀ n (t u : Fin n → ℕ), Injective t → SameOrder t u → (∀ i, t i ∈ H n) →
      (∀ i, u i ∈ H n) → Matched L c (R ∘ t) (R ∘ u)) (name : ℕ ≃ ℚ) :
    ∃ B : ℚ → Fin d → M, ∀ n, Stage L c R H name n (fun i : Fin n => B (name i.val)) := by
  classical
  let Good (n : ℕ) := {v : Fin n → Fin d → M // Stage L c R H name n v}
  have start : Stage L c R H name 0 Fin.elim0 := by
    refine ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,?_⟩
    exact congrArg (fun g => tupleType L (layout c g)) (Subsingleton.elim _ _)
  have succ (n : ℕ) (v : Good n) : ∃ w : Good (n+1), ∀ i, w.val i.castSucc = v.val i := by
    obtain ⟨w,good,pre⟩ := step_stage fin c R H down inf hom name n v.val v.property
    exact ⟨⟨w,good⟩,pre⟩
  choose next extends' using succ
  let stages : (n : ℕ) → Good n := Nat.rec ⟨Fin.elim0,start⟩ next
  have prev (n : ℕ) (i : Fin n) : (stages (n+1)).val i.castSucc = (stages n).val i := extends' _ _ _
  let B (q : ℚ) := (stages (name.symm q+1)).val (Fin.last _)
  have atIndex (n : ℕ) (i : Fin n) : B (name i.val) = (stages n).val i := by
    induction n with
    | zero => exact i.elim0
    | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact congrArg (fun r => (stages (r+1)).val (Fin.last r)) (name.symm_apply_apply n)
      · exact (ih j).trans (prev n j).symm
  exact ⟨B,fun n => (funext (atIndex n)) ▸ (stages n).property⟩

end ProjectiveIndiscernibles
