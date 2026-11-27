module

public import SolvedProblems.MISCube
public import SolvedProblems.MISCharge

@[expose] public section

namespace MISQueries

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def miss (Q : Fin t → Finset V) (e S : Finset V) : Prop := ∀ i, ¬e ⊆ Q i ∨ ¬Disjoint S (Q i \ e)

noncomputable def cost (p : ℝ) (Q : Fin t → Finset V) (e : Finset V) : ℝ :=
  ∑ i, if e ⊆ Q i then charge p (Q i).card else 0

/-- All unordered pairs, and those left over after removing explicit pair queries. -/
def pairs (V : Type*) [Fintype V] : Finset (Finset V) := Finset.univ.powersetCard 2

def remaining (Q : Fin t → Finset V) : Finset (Finset V) := pairs V \ Finset.univ.image Q

omit [DecidableEq V] in
theorem pair_mem {e : Finset V} : e ∈ pairs V ↔ e.card = 2 := by simp [pairs]

theorem product_bits {I : Type*} (T : Finset I) (P : I → Prop) :
    ∏ i ∈ T, bit (P i) = bit (∀ i ∈ T, P i) := by
  classical
  induction T using Finset.induction with
  | empty => simp [bit]
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, ih, Finset.forall_mem_insert]
    by_cases ha : P i <;> by_cases hb : ∀ j ∈ T, P j <;> simp [ha,hb,bit]

theorem miss_for_pair {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1) (Q : Fin t → Finset V)
    {e : Finset V} (he : e ∈ remaining Q) :
    Real.exp (-cost p Q e) ≤ average p Finset.univ.toList (fun S => bit (miss Q e S)) := by
  classical
  have hec := pair_mem.mp (Finset.mem_sdiff.mp he).1
  have hne (i : Fin t) : Q i ≠ e := fun h => (Finset.mem_sdiff.mp he).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h⟩)
  let F (i : Fin t) (S : Finset V) := bit (¬e ⊆ Q i ∨ ¬Disjoint S (Q i \ e))
  have hm (i : Fin t) : Monotone (F i) := by
    intro S T hST
    exact bit_mono (Or.imp id (fun hdis d => hdis (d.mono_left hST)))
  have hprod := average.harris_prod hp.le hp' Finset.univ.toList Finset.univ F hm (fun _ _ => bit_nonneg _)
  have ident (S : Finset V) : ∏ i, F i S = bit (miss Q e S) := by
    rw [show (∏ i, F i S) = _ from product_bits Finset.univ _]
    simp [miss]
  simp_rw [ident] at hprod
  apply le_trans _ hprod
  rw [cost, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
  intro i _
  by_cases hsub : e ⊆ Q i
  · have hcard : 2 < (Q i).card := hec ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, (hne i).symm⟩)
    simp only [hsub, ite_true, F, not_true_eq_false, false_or, charge]
    rw [hit_probability, Finset.card_sdiff_of_subset hsub, hec]
    exact hit_ge_exp hp hp' (by omega)
  · simp [F, hsub, average.const]

theorem remaining_card (Q : Fin t → Finset V) : (pairs V).card ≤ (remaining Q).card + t := by
  classical
  have sub : pairs V ⊆ remaining Q ∪ Finset.univ.image Q := by
    intro e he
    by_cases h : e ∈ Finset.univ.image Q
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_union_le (remaining Q) (Finset.univ.image Q)
  have h3 : (Finset.univ.image Q).card ≤ t := by simpa using (Finset.card_image_le (f := Q) (s := Finset.univ))
  omega

theorem cost_sum {p : ℝ} (hp : 0 < p) (Q : Fin t → Finset V) :
    (∑ e ∈ remaining Q, cost p Q e) ≤ t * (36/p^2) := by
  classical
  unfold cost
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : Fin t, (36/p^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      let E := (remaining Q).filter fun e => e ⊆ Q i
      have hsub : E ⊆ (Q i).powersetCard 2 := by
        intro e he
        obtain ⟨he,hq⟩ := Finset.mem_filter.mp he
        exact Finset.mem_powersetCard.mpr ⟨hq,pair_mem.mp (Finset.mem_sdiff.mp he).1⟩
      have hc : E.card ≤ (Q i).card.choose 2 := by simpa only [Finset.card_powersetCard] using Finset.card_le_card hsub
      have hc' : (E.card : ℝ) ≤ ((Q i).card.choose 2 : ℝ) := by exact_mod_cast hc
      apply (mul_le_mul_of_nonneg_right hc' (charge_nonneg p (Q i).card)).trans
      by_cases h : 3 ≤ (Q i).card
      · exact paid_per_query hp h
      · have hz : (Q i).card - 2 = 0 := by omega
        simp only [charge, hz, Nat.cast_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), div_zero, mul_zero]
        positivity
    _ = _ := by simp

end MISQueries
