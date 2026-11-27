module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Range

public section

namespace ProjectiveIndiscernibles

open Set Function

/-- Infinite Ramsey for a fixed tuple length and a finite palette. Restricting
to increasing tuples gives a single colour on an infinite subset of any
prescribed infinite set of natural numbers. -/
theorem ramseyTuples {C : Type*} [Finite C] (n : ℕ) (color : (Fin n → ℕ) → C)
    (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ c : C, ∀ t : Fin n → ℕ, StrictMono t → (∀ i, t i ∈ T) → color t = c := by
  classical
  induction n generalizing S with
  | zero =>
    exact ⟨S,Set.Subset.rfl,hS,color Fin.elim0,fun t _ _ => congrArg color (funext fun j => j.elim0)⟩
  | succ n ih =>
    let Host := {s : Set ℕ // s.Infinite}
    let p (s : Host) := s.property.nonempty.choose
    have mem (s : Host) : p s ∈ s.val := s.property.nonempty.choose_spec
    have step (s : Host) : ∃ t : Host, (t.val ⊆ s.val ∧ ∀ z ∈ t.val, p s < z) ∧
        ∃ c : C, ∀ v : Fin n → ℕ, StrictMono v → (∀ i, v i ∈ t.val) → color (Fin.cons (p s) v) = c := by
      have tail := s.property.sdiff (Set.finite_Iic (p s))
      obtain ⟨T,ht,large,c,hc⟩ := ih (fun v => color (Fin.cons (p s) v)) _ tail
      exact ⟨⟨_,large⟩,⟨ht.trans Set.sdiff_subset,fun z hz => lt_of_not_ge (ht hz).2⟩,c,hc⟩
    choose next spec using step
    let set : ℕ → Host := Nat.rec ⟨S,hS⟩ (fun _ s => next s)
    let v (i : ℕ) := p (set i)
    have decrease : Antitone fun i => (set i).val := antitone_nat_of_succ_le fun i => (spec (set i)).1.1
    have strict : StrictMono v := strictMono_nat_of_lt_succ fun i => (spec (set i)).1.2 _ (mem (set (i+1)))
    let col (i : ℕ) := (spec (set i)).2.choose
    obtain ⟨c,large⟩ := Finite.exists_infinite_fiber col
    let idx := {i | col i = c}
    have inf : idx.Infinite := Set.infinite_coe_iff.mp large
    refine ⟨v '' idx, ?_, inf.image strict.injective.injOn,c,?_⟩
    · rintro _ ⟨j,_,rfl⟩
      exact decrease (Nat.zero_le j) (mem (set j))
    · intro t mono inside
      choose pos hpos ep using inside
      let j := pos 0
      have eq (i : Fin n) : t i.succ ∈ (set (j+1)).val := by
        have lt : j < pos i.succ := strict.lt_iff_lt.mp (by rw [show v j = t 0 from ep 0, ep]; exact mono (Fin.succ_pos i))
        rw [← ep i.succ]
        exact decrease (Nat.succ_le_of_lt lt) (mem (set _))
      have hom := (spec (set j)).2.choose_spec (Fin.tail t) (mono.comp (fun _ _ h => Nat.succ_lt_succ h)) eq
      have reassemble : Fin.cons (p (set j)) (Fin.tail t) = t := by rw [show p (set j) = t 0 from ep 0,Fin.cons_self_tail]
      exact ((congrArg color reassemble).symm.trans hom).trans (hpos 0)

end ProjectiveIndiscernibles
