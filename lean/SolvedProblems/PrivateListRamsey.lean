module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Finset.Card

@[expose] public section

namespace PrivateList

open Filter Set
open scoped Classical

/-- Take the value attained on an ultrafilter-large fiber of a finite coloring. -/
theorem majority_exists {C : Type} [Finite C] (f : ℕ → C) :
    ∃ c, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = c := by
  have h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ c ∈ (univ : Set C), f n = c :=
    .of_forall (fun n => ⟨_,mem_univ _,rfl⟩)
  obtain ⟨c,_,hc⟩ := (Ultrafilter.eventually_exists_mem_iff finite_univ).mp h
  exact ⟨c,hc⟩

noncomputable def preference {C : Type} [Finite C] (color : Finset ℕ → C) :
    ℕ → Finset ℕ → C
  | 0, p => color p
  | k+1, p => (majority_exists (fun x => preference color k (insert x p))).choose

theorem homogeneous {C : Type} [Finite C] (color : Finset ℕ → C) (k L : ℕ) :
    ∃ S : Finset ℕ, S.card = L ∧ ∀ T ⊆ S, T.card = k → color T = preference color k ∅ := by
  classical
  let c := preference color k ∅
  have build (n : ℕ) : ∃ S : Finset ℕ, S.card = n ∧
      ∀ T ⊆ S, T.card ≤ k → preference color (k-T.card) T = c := by
    induction n with
    | zero => exact ⟨∅,rfl,fun T hT _ => by simp [Finset.subset_empty.mp hT,c]⟩
    | succ n ih =>
      obtain ⟨S,hS,good⟩ := ih
      have all : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), ∀ T ∈ S.powerset,
          T.card < k → preference color (k-T.card-1) (insert x T) = preference color (k-T.card) T := by
        apply (Filter.eventually_all_finset _).mpr
        intro T _
        by_cases h : T.card < k
        · have hk : k-T.card = (k-T.card-1)+1 := by omega
          have y := (majority_exists (fun x => preference color (k-T.card-1) (insert x T))).choose_spec
          filter_upwards [y] with x hx h'
          conv_rhs => rw [hk]
          exact hx
        · exact .of_forall (fun _ h' => (h h').elim)
      have fresh : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), x ∉ S :=
        S.finite_toSet.compl_mem_hyperfilter
      obtain ⟨x,hx,keep⟩ := (fresh.and all).exists
      refine ⟨insert x S, by simp [hx,hS], ?_⟩
      intro T sub size
      by_cases hxt : x ∈ T
      · let U := T.erase x
        have subU : U ⊆ S := by
          intro a ha
          exact (Finset.mem_insert.mp (sub (Finset.mem_erase.mp ha).2)).resolve_left (Finset.mem_erase.mp ha).1
        have hU : U.card+1 = T.card := Finset.card_erase_add_one hxt
        have hk : U.card < k := by omega
        have eq := keep U (Finset.mem_powerset.mpr subU) hk
        rw [show insert x U = T from Finset.insert_erase hxt] at eq
        rw [show k-T.card = k-U.card-1 by omega]
        exact eq.trans (good U subU hk.le)
      · apply good T _ size
        intro a ha
        exact (Finset.mem_insert.mp (sub ha)).resolve_left (fun e => hxt (e ▸ ha))
  obtain ⟨S,hS,good⟩ := build L
  refine ⟨S,hS,fun T sub card => ?_⟩
  simpa [card,preference] using good T sub card.le

theorem preference_step {C : Type} [Finite C] (color : Finset ℕ → C) (k : ℕ) (T : Finset ℕ) :
    ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), preference color k (insert x T) = preference color (k+1) T :=
  (majority_exists (fun x => preference color k (insert x T))).choose_spec

theorem preference_map {C D : Type} [Finite C] [Finite D] (f : C → D)
    (color : Finset ℕ → C) (k : ℕ) (T : Finset ℕ) :
    preference (fun A => f (color A)) k T = f (preference color k T) := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x,ha,hb⟩ := ((preference_step (fun A => f (color A)) k T).and
      (preference_step color k T)).exists
    rw [← ha, ih, hb]

/-- A product Ramsey rectangle for two independently chosen ordered axes. -/
theorem rectangle {C : Type} [Finite C] (color : Finset ℕ → Finset ℕ → C) (k L : ℕ) :
    ∃ A B : Finset ℕ, A.card = L ∧ B.card = L ∧ ∃ c, ∀ S ⊆ A, S.card = k →
      ∀ T ⊆ B, T.card = k → color S T = c := by
  classical
  let rows S := preference (color S) k ∅
  obtain ⟨A,ha,hA⟩ := homogeneous rows k L
  let joint (T : Finset ℕ) (S : A.powerset) := color S T
  obtain ⟨B,hb,hB⟩ := homogeneous joint k L
  refine ⟨A,B,ha,hb,preference rows k ∅,?_⟩
  intro S subS cardS T subT cardT
  let I : A.powerset := ⟨S, Finset.mem_powerset.mpr subS⟩
  have h := congrFun (hB T subT cardT) I
  have ev := preference_map (fun f : A.powerset → C => f I) joint k ∅
  exact h.trans (ev.symm.trans (hA S subS cardS))

end PrivateList
