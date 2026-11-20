module

public import SolvedProblems.UncountableGenerationModel
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

open MeasureTheory Set Function
namespace UncountableGeneration

/-- Any uniform modulus vanishing at zero yields arbitrarily small average probability
on a sufficiently large pool, by splitting the dummy probabilities at a small threshold. -/
theorem pool_size (ω : ℝ → ℝ) (hw : Vanishes ω) (e : ℝ) (he : 0 < e) :
    ∃ m : ℕ, ∀ p q : Fin (m+1) → ℝ, (∀ j, p j ≤ 1) →
      (∀ j, q j ∈ Icc (0 : ℝ) 1) → (∑ j, q j) ≤ 1 →
      (∀ j, p j ≤ ω (q j)) → (∑ j, p j) ≤ (m+1 : ℕ) * e := by
  obtain ⟨δ, hδ, hω⟩ := hw (e/2) (half_pos he)
  obtain ⟨m, hm⟩ := exists_nat_gt ((1/δ) / (e/2))
  refine ⟨m, fun p q hp hq hsum hpriv ↦ ?_⟩
  have hpq (j) : p j ≤ e/2 + q j / δ := by
    by_cases h : q j < δ
    · have hsmall := hω _ (hq j) h
      have hn := div_nonneg (hq j).1 hδ.le
      linarith [hpriv j]
    · have hh := (one_le_div hδ).mpr (le_of_not_gt h)
      linarith [hp j]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ hpq j
  rw [Finset.sum_add_distrib, ← Finset.sum_div Finset.univ q δ] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hd := (div_lt_iff₀ (half_pos he)).mp hm
  have hh := div_le_div_of_nonneg_right hsum hδ.le
  push_cast at *
  nlinarith

/-- The pools use separate first pairing coordinates; zero is a common dummy index. -/
def poolColumn (i a : ℕ) : ℕ := Nat.pair i a + 1

def sparse {m : ℕ → ℕ} (z : ∀ i, Fin (m i+1)) : Input :=
  fun i ↦ Nat.pair (poolColumn i (z i)) 0

def selected {m : ℕ → ℕ} (z : ∀ i, Fin (m i+1)) : Set ℕ :=
  range (fun i ↦ poolColumn i (z i))

def hit (t j : ℕ) : Set Output := {u | col (u t) = j}

theorem hit_measurable (t j : ℕ) : MeasurableSet (hit t j) :=
  measurableSet_eq_fun ((measurable_of_countable col).comp (measurable_pi_apply t)) measurable_const

theorem hit_prefix (t j : ℕ) : PrefixEvent (hit t j) (t+1) := by
  intro u v h
  change (col (u t) = j ↔ col (v t) = j)
  rw [h t (by omega)]

theorem sparse_injective {m : ℕ → ℕ} (z : ∀ i, Fin (m i+1)) :
    Injective (sparse z) := by
  intro i j h
  exact (Nat.pair_eq_pair.mp (Nat.succ.inj (Nat.pair_eq_pair.mp h).1)).1

/-- Replacing one pool entry by a common dummy removes its private column choice.
The probabilities of the disjoint column events under the common law sum to at most one. -/
theorem pool_sum {ω : ℝ → ℝ} {P : Rule} (hp : ProbLaw P) (hpriv : PrivateWith P ω)
    {m : ℕ → ℕ} {e : ℕ → ℝ}
    (hsize : ∀ i, ∀ p q : Fin (m i+1) → ℝ, (∀ j, p j ≤ 1) →
      (∀ j, q j ∈ Icc (0 : ℝ) 1) → (∑ j, q j) ≤ 1 →
      (∀ j, p j ≤ ω (q j)) → (∑ j, p j) ≤ (m i+1 : ℕ) * e i)
    (z : ∀ i, Fin (m i+1)) (t i : ℕ) :
    (∑ j : Fin (m i+1), (P (sparse (update z i j))).real (hit t (poolColumn i j)))
      ≤ (m i+1 : ℕ) * e i := by
  let dummy : Input := update (sparse z) i (Nat.pair 0 0)
  let := hp dummy
  let Q (j : Fin (m i+1)) := (P dummy).real (hit t (poolColumn i j))
  apply hsize i _ Q
  · intro j
    let := hp (sparse (update z i j))
    exact measureReal_le_one
  · exact fun _ ↦ ⟨measureReal_nonneg, measureReal_le_one⟩
  · have disj : Pairwise (Disjoint on (fun j : Fin (m i+1) ↦ hit t (poolColumn i j))) := by
      intro a b hab
      exact Set.disjoint_left.mpr fun u ha hb ↦ hab (Fin.ext (by
        have h : poolColumn i a = poolColumn i b := ha.symm.trans hb
        simpa [poolColumn] using h))
    dsimp [Q]
    rw [← measureReal_iUnion_fintype disj (fun _ ↦ hit_measurable ..)]
    exact measureReal_le_one
  · intro j
    apply hpriv _ dummy _ _ (hit_measurable ..)
    refine ⟨i, ?_, ?_⟩
    · simp [sparse, dummy, poolColumn]
    · intro n hn
      simp [sparse, dummy, update_of_ne hn]

end UncountableGeneration
