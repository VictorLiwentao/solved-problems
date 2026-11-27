module

public import SolvedProblems.EMXModel
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Positivity

@[expose] public section

namespace EMX

open scoped Classical

/-- A finite uniform bound on the number of candidates to examine in each block
at approximation stage s. -/
def slots (s : ℕ) := 2^(2^width s * width s)

theorem width_le_slots (s : ℕ) : s+1 ≤ slots s := by
  have h : width s ≤ 2^width s * width s := Nat.le_mul_of_pos_left _ (by positivity)
  exact (show s+1 ≤ width s by simp [width]).trans
    (h.trans Nat.lt_two_pow_self.le)

noncomputable def enumerate {α : Type} [Fintype α] (fallback : α) (k : ℕ) : α :=
  if h : k < Fintype.card α then (Fintype.equivFin α).symm ⟨k,h⟩ else fallback

theorem enumerate_hits {α : Type} [Fintype α] (fallback : α) (x : α) :
    enumerate fallback ((Fintype.equivFin α) x).val = x := by
  simp [enumerate, ((Fintype.equivFin α) x).isLt]

def rowIndex {s j} (h : s ≤ j) (u : Fin (s+1)) : Row j :=
  ⟨u.val, u.isLt.trans_le ((show s+1 ≤ width j by simp [width]; omega).trans Nat.lt_two_pow_self.le)⟩

/-- Small blocks keep every possible mask. In every larger block the first s+1
disjoint rows provide all the required alternatives. -/
noncomputable def restricted (s j : ℕ) (k : Fin (slots s)) : Hyp :=
  if h : j < s then ⟨j, enumerate (omittedRow j 0) k.val⟩
  else ⟨j, omittedRow j (rowIndex (Nat.le_of_not_gt h) (enumerate (0 : Fin (s+1)) k.val))⟩

theorem restricted_block (s j) (k) : (restricted s j k).1 = j := by
  unfold restricted; split <;> rfl

theorem small_covered {s j} (h : j < s) (z : Holes j) :
    ∃ k, restricted s j k = Sigma.mk j z := by
  classical
  have hcard : Fintype.card (Holes j) ≤ slots s := by
    calc
      _ ≤ Fintype.card (Finset (Cell j)) := Fintype.card_subtype_le _
      _ = 2^(2^width j * width j) := by simp [Cell,Row,Col]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide) (by simp [width]; omega)) (by simp [width]; omega))
  let v := (Fintype.equivFin (Holes j)) z
  exact ⟨⟨v.val, v.isLt.trans_le hcard⟩, by
    simp only [restricted, dite_eq_left h]
    exact congrArg (Sigma.mk j) (enumerate_hits _ z)⟩

theorem large_covered {s j} (h : s ≤ j) (u : Fin (s+1)) :
    ∃ k, restricted s j k = Sigma.mk j (omittedRow j (rowIndex h u)) := by
  let v := (Fintype.equivFin (Fin (s+1))) u
  have hv : v.val < s+1 := by simpa using v.isLt
  exact ⟨⟨v.val, hv.trans_le (width_le_slots s)⟩, by
    simp only [restricted, dite_eq_right (Nat.not_lt_of_ge h)]
    rw [show enumerate (0 : Fin (s+1)) v.val = u from enumerate_hits _ u]⟩

def hits {m} (xs : Fin m → Point) (h : Hyp) :=
  (Finset.univ.filter fun i => xs i ∈ support h).card

theorem attainable (s : ℕ) {m} (xs : Fin m → Point) :
    ∃ n : ℕ, ∃ v : ℕ × Fin (slots s), m - hits xs (restricted s v.1 v.2) = n :=
  ⟨_, (0, ⟨0, Nat.two_pow_pos _⟩), rfl⟩

noncomputable def best (s : ℕ) {m} (xs : Fin m → Point) : ℕ × Fin (slots s) := by
  classical
  exact (Nat.find_spec (attainable s xs)).choose

theorem best_spec (s : ℕ) {m} (xs : Fin m → Point) (v : ℕ × Fin (slots s)) :
    hits xs (restricted s v.1 v.2) ≤ hits xs (restricted s (best s xs).1 (best s xs).2) := by
  classical
  have min := (Nat.find_spec (attainable s xs)).choose_spec.trans_le
    (Nat.find_min' (attainable s xs) ⟨v,rfl⟩)
  change m - hits xs (restricted s (best s xs).1 (best s xs).2) ≤ _ at min
  have l (z : Hyp) : hits xs z ≤ m := by simpa [hits] using
    (Finset.card_le_univ (Finset.univ.filter (fun i => xs i ∈ support z)))
  have := l (restricted s v.1 v.2)
  omega

end EMX
