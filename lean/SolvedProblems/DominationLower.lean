module

public import SolvedProblems.DominationHost

@[expose] public section

namespace DominationVC

/-- The disjoint union of two cliques cannot embed if each of the cliques is
too large for the point side: opposite target parts must have opposite tags. -/
theorem avoids_by_point_side {a b d : ℕ} (ha : d < a) (hb : d < b) :
    ¬Nonempty (twoCliques (fun (_ : Fin a) (_ : Fin b) => False) ↪g incomparability (Host d)) := by
  classical
  rintro ⟨e⟩
  have htag (x : Fin a) (y : Fin b) : (e (.inl x)).isPoint ≠ (e (.inr y)).isPoint := by
    intro h
    have hne : e (.inl x) ≠ e (.inr y) := e.injective.ne (by simp)
    exact e.map_rel_iff.mp (Host.same_side_adj h hne)
  by_cases all : ∀ x : Fin a, (e (.inl x)).isPoint = true
  · have h := Host.point_capacity (fun i : Fin a => e (.inl i))
      (e.injective.comp Sum.inl_injective) all
    omega
  · obtain ⟨x,hx⟩ := not_forall.mp all
    have all' (y : Fin b) : (e (.inr y)).isPoint = true := by
      have := htag x y
      cases he : (e (.inl x)).isPoint <;> cases he' : (e (.inr y)).isPoint <;> simp_all
    have h := Host.point_capacity (fun i : Fin b => e (.inr i)) (e.injective.comp Sum.inr_injective) all'
    omega

theorem avoids_by_size {a b d : ℕ} (h : d + 2^d < a+b) :
    ¬Nonempty (twoCliques (fun (_ : Fin a) (_ : Fin b) => False) ↪g incomparability (Host d)) := by
  rintro ⟨e⟩
  have hc := Fintype.card_le_of_embedding e.toEmbedding
  simp only [Fintype.card_sum, Fintype.card_fin, Host.card_host] at hc
  omega

def lowerSize (a b : ℕ) : ℕ := max (a-1) (Nat.log 2 (b+1) - 2)

theorem host_lower (d : ℕ) : d ≤ (closedFamily (incomparability (Host d))).vcDim := by
  have h := Finset.Shatters.card_le_vcDim (Host.points_shattered d)
  rw [Host.point_card] at h
  exact h

/-- A single explicit forbidden graph K_a ⊔ K_b and a height-two membership
host give the matching-order lower bound, with the stated finite additive constants. -/
theorem vc_lower {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (¬Nonempty (twoCliques (fun (_ : Fin a) (_ : Fin b) => False) ↪g incomparability (Host (lowerSize a b)))) ∧
    lowerSize a b ≤ (closedFamily (incomparability (Host (lowerSize a b)))).vcDim := by
  constructor
  · unfold lowerSize
    by_cases h : Nat.log 2 (b+1) - 2 ≤ a-1
    · rw [max_eq_left h]
      exact avoids_by_point_side (by omega) (by omega)
    · rw [max_eq_right (by omega)]
      apply avoids_by_size
      let n := Nat.log 2 (b+1) - 2
      have hn : n + 2 = Nat.log 2 (b+1) := by dsimp [n]; omega
      have hpow := Nat.pow_log_le_self 2 (Nat.succ_ne_zero b)
      rw [← hn, pow_add] at hpow
      have hl : n < 2^n := Nat.lt_two_pow_self
      change n + 2^n < a+b
      omega
  · exact host_lower _

end DominationVC
