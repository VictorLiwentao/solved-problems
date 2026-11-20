module

public import SolvedProblems.RationalReturnsGeometry

@[expose] public section

namespace RationalReturns

/-- Removing one indistinguishable north step at each required column. -/
def freeBag (R : ℕ) (A B : Finset ℕ) (D : ℕ → ℕ) (L U : ℕ) (s : Multiset ℕ) : Prop :=
  s.card = R ∧ (∀ x ∈ s, x ∈ A) ∧
    ∀ c ∈ Finset.Icc L U, D c ≤ before B c + less s c

theorem necessary_bounds {T A B D L U s} (ok : BagGood T A B D L U s) :
    B.card ≤ T ∧ ∀ c ∈ Finset.Icc L U, D c ≤ before B c + (T-B.card) := by
  obtain ⟨size,_,contains,all⟩ := ok
  have bsize := Multiset.card_le_card contains
  rw [size] at bsize
  refine ⟨bsize, fun c hc => ?_⟩
  have bound := all c hc
  have split : less (s-B.val) c + before B c = less s c := by
    rw [←less_val,←less_add,Multiset.sub_add_cancel contains]
  have limit := less_le_card (s-B.val) c
  rw [Multiset.card_sub contains,size] at limit
  change less (s - B.val) c ≤ T-B.card at limit
  omega

noncomputable def removeBag {T} (A B : Finset ℕ) (D : ℕ → ℕ) (L U : ℕ)
    (sub : B ⊆ A) (room : B.card ≤ T) :
    {s : Multiset ℕ // BagGood T A B D L U s} ≃
    {s : Multiset ℕ // freeBag (T-B.card) A B D L U s} where
  toFun s := ⟨s.val-B.val, by
    obtain ⟨size,col,contains,all⟩ := s.property
    refine ⟨by rw [Multiset.card_sub contains,size]; rfl,?_,?_⟩
    · exact fun x hx => col x ((Multiset.subset_of_le (Multiset.sub_le_self _ _)) hx)
    · intro c hc
      rw [←less_val, add_comm, ←less_add, Multiset.sub_add_cancel contains]
      exact all c hc⟩
  invFun s := ⟨s.val+B.val,by
    obtain ⟨size,col,all⟩ := s.property
    refine ⟨by rw [Multiset.card_add,size]; exact Nat.sub_add_cancel room,?_,?_,?_⟩
    · intro x hx
      exact (Multiset.mem_add.mp hx).elim (col x) (fun h => sub h)
    · exact le_add_self
    · intro c hc
      rw [less_add,less_val,add_comm]
      exact all c hc⟩
  left_inv s := Subtype.ext (Multiset.sub_add_cancel s.property.2.2.1)
  right_inv s := Subtype.ext (by simp)

noncomputable def sortFree (R : ℕ) (A B : Finset ℕ) (D : ℕ → ℕ) (L U : ℕ) :
    {s : Multiset ℕ // freeBag R A B D L U s} ≃
      {w : Fin R → ℕ // Monotone w ∧ (∀ q, w q ∈ A) ∧
        ∀ c ∈ Finset.Icc L U, D c ≤ before B c + less (bag w) c} where
  toFun s := ⟨sortedWord s.val s.property.1, sorted_mono _ _, fun q => by
    apply s.property.2.1
    have e := (mem_bag (w:=sortedWord s.val s.property.1)).mpr ⟨q,rfl⟩
    simpa only [bag_sorted] using e, by simpa only [bag_sorted] using s.property.2.2⟩
  invFun w := ⟨bag w.val,card_bag _, fun x hx => by
    obtain ⟨q,rfl⟩ := mem_bag.mp hx
    exact w.property.2.1 q, w.property.2.2⟩
  left_inv s := Subtype.ext (bag_sorted s.val s.property.1)
  right_inv w := Subtype.ext (bag_inj (sorted_mono (bag w.val) (card_bag w.val)) w.property.1
    (bag_sorted (bag w.val) (card_bag w.val)))

noncomputable def residualWords {T} (A B : Finset ℕ) (D : ℕ → ℕ) (L U : ℕ)
    (sub : B ⊆ A) (room : B.card ≤ T) :
    {s : Multiset ℕ // BagGood T A B D L U s} ≃
      {w : Fin (T-B.card) → ℕ // Monotone w ∧ (∀ q, w q ∈ A) ∧
        ∀ c ∈ Finset.Icc L U, D c ≤ before B c + less (bag w) c} :=
  (removeBag A B D L U sub room).trans (sortFree _ _ _ _ _ _)

end RationalReturns
