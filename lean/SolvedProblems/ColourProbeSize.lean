module

public import SolvedProblems.ColourProbeRows
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace ColourProbe

open SimpleGraph

private theorem reach_rainbow {V : Type*} (G : SimpleGraph V) (r : Row G) : (probe G).Reachable r (rainbow G) := by
  classical
  by_cases hs : r.1.val.Nonempty
  · obtain ⟨i,hi⟩ := hs
    let T := r.1.val.erase i
    have hsub : T ⊆ r.1.val := Finset.erase_subset ..
    let q : Row G := ⟨⟨T,(Finset.card_le_card hsub).trans r.1.property.1,
      fun x hx y hy => r.1.property.2 x (hsub hx) y (hsub hy)⟩,fun x => r.2 ⟨x.val,hsub x.property⟩⟩
    have adj : (probe G).Adj r q := by
      refine ⟨i,?_,?_⟩
      · rw [word_in r i hi,word_out q i (by simp [q,T])]
        simp
      · intro j hji
        by_cases hj : j ∈ r.1.val
        · rw [word_in r j hj,word_in q j (by simp [q,T,hj,hji])]
        · rw [word_out r j hj,word_out q j (fun h => hj (hsub h))]
    exact adj.reachable.trans (reach_rainbow G q)
  · have empty := Finset.not_nonempty_iff_eq_empty.mp hs
    have h : r = rainbow G := word_injective G (funext (fun i => by rw [word_out r i (by simp [empty]),word_rainbow]))
    subst r
    exact Reachable.refl _
termination_by r.1.val.card
decreasing_by classical exact Finset.card_erase_lt_of_mem hi

theorem connected {V : Type*} (G : SimpleGraph V) : (probe G).Connected := by
  have _ : Nonempty (Row G) := ⟨rainbow G⟩
  exact ⟨fun v w => (reach_rainbow G v).trans (reach_rainbow G w).symm⟩

private theorem fixed_support_count {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Fintype.card {S : Allowed G // S.val.card = k} ≤ (Fintype.card V).choose k := by
  classical
  let f : {S : Allowed G // S.val.card = k} → ↥((Finset.univ : Finset V).powersetCard k) :=
    fun S => ⟨S.val.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,S.property⟩⟩
  have inj : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥((Finset.univ : Finset V).powersetCard k) => x.val) h))
  simpa [Finset.card_powersetCard] using Fintype.card_le_of_injective f inj

theorem card_bound {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype.card (Row G) ≤ 1 + Fintype.card V * (Fintype.card V+1) +
      (Fintype.card V).choose 2 * (Fintype.card V+1)^2 := by
  classical
  let n := Fintype.card V
  have count (k : ℕ) : ∑ S ∈ (Finset.univ : Finset (Allowed G)).filter (fun S => S.val.card = k),
      (n+1)^S.val.card ≤ n.choose k * (n+1)^k := by
    calc
      _ = Fintype.card {S : Allowed G // S.val.card = k} * (n+1)^k := by
        rw [Fintype.card_subtype]
        exact Finset.sum_const_nat fun S h => by rw [(Finset.mem_filter.mp h).2]
      _ ≤ _ := Nat.mul_le_mul_right _ (fixed_support_count G k)
  change Fintype.card ((S : Allowed G) × (S.val → Option V)) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun,Fintype.card_coe,Fintype.card_option]
  change ∑ S : Allowed G, (n+1)^S.val.card ≤ 1+n*(n+1)+n.choose 2*(n+1)^2
  have h₁ := count 0
  have h₂ := count 1
  have h₃ := count 2
  have hsum := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Allowed G))) (t := Finset.range 3)
    (g := fun S => S.val.card) (fun S _ => Finset.mem_range.mpr (by have := S.property.1; omega))
    (fun S => (n+1)^S.val.card)
  simp [Finset.sum_range_succ] at hsum h₁ h₂ h₃
  omega

end ColourProbe
