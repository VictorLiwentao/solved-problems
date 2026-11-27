module

public import SolvedProblems.SymmetricERMRate
public import SolvedProblems.SymmetricERMFinite
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace SymmetricERM

/-- The usual least finite realizable, distribution-free sample threshold for error
and failure probability one quarter. -/
def ExactThreshold {B r} (A : Learner B r) (n : ℕ) : Prop :=
  Threshold A n ∧ ∀ k, Threshold A k → n ≤ k

private theorem threshold_pos {B r} (hB : 0 < B) (hr : 0 < r) (A : Learner B r) :
    ¬Threshold A 0 := by
  classical
  intro h
  let z : Point B r := (⟨0,hB⟩, ⟨0,hr⟩)
  let c := A 0 (fun i => i.elim0)
  let u : Code B r := (Equiv.refl _, fun _ => {z.2})
  have hdis : ∃ t : Code B r, classify c z ≠ classify t z := by
    by_cases hv : classify c z = ∅
    · refine ⟨u, ?_⟩
      rw [hv]
      simp [u, classify]
    · exact ⟨emptyCode B r, by simpa [emptyCode, classify] using hv⟩
  obtain ⟨t, ht⟩ := hdis
  let p := fun x : Point B r => if x = z then (1:ℝ) else 0
  have hp : Law p := ⟨fun x => by dsimp [p]; split <;> norm_num, by simp [p]⟩
  have high : risk p t c = 1 := by
    unfold risk
    calc
      _ = ∑ x : Point B r, p x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = z
        · subst x; simp [ht]
        · simp [p, hx]
      _ = 1 := hp.2
  have eqc (xs : Fin 0 → Point B r) : A 0 (observe t xs) = c := by
    unfold c; congr 1; funext i; exact i.elim0
  have large (xs : Fin 0 → Point B r) : (1/4 : ℝ) < risk p t (A 0 (observe t xs)) := by
    rw [eqc, high]; norm_num
  have f : failure A 0 p t = 1 := by
    unfold failure
    change (∑ xs : Fin 0 → Point B r, if 1/4 < risk p t (A 0 (observe t xs)) then _ else _) = _
    simp only [ite_eq_left (large _)]
    exact sample_mass hp
  have hfail := h 0 le_rfl p hp t
  rw [f] at hfail
  norm_num at hfail

/-- Daniely–Sabato–Ben-David–Shalev-Shwartz's symmetric ERM gap at fixed error and
confidence 1/4. At parameter r the domain has 4^r blocks of r points. The two
proper deterministic ERMs have positive, least PAC sample thresholds g,b. Their
ratio b/g is at least log₂(d)/384, with d the actual Natarajan dimension rounded
by taking the integer logarithm. -/
theorem logarithmicGap (r : ℕ) (hr : 2 ≤ r) :
    let B := 4^r
    let d := dimension B r
    Symmetric B r ∧ B ≤ d ∧ d ≤ B*r ∧
      ∃ G H : Learner B r, ERM G ∧ ERM H ∧ ∃ g b : ℕ,
        ExactThreshold G g ∧ ExactThreshold H b ∧ 0 < g ∧
        g ≤ 64*B ∧ B*r < 2*b ∧ d.log2*g ≤ 384*b := by
  classical
  dsimp only
  let B := 4^r
  have hB : 0 < B := pow_pos (by decide) _
  have hr' : 0 < r := by omega
  obtain ⟨dlo, dhi⟩ := dimension_bounds (B := B) hr'
  let gex := finite_threshold (@good_erm B r)
  let bex := finite_threshold (@bad_erm B r)
  let g := Nat.find gex
  let b := Nat.find bex
  have hg : ExactThreshold (@good B r) g := ⟨Nat.find_spec gex, fun _ => Nat.find_min' gex⟩
  have hb : ExactThreshold (@bad B r) b := ⟨Nat.find_spec bex, fun _ => Nat.find_min' bex⟩
  have hgpos : 0 < g := by
    by_contra! hz
    exact threshold_pos hB hr' good (show Threshold _ 0 from (Nat.eq_zero_of_le_zero hz) ▸ hg.1)
  have hgle : g ≤ 64*B := hg.2 _ (good_upper r)
  have hbgt : B*r < 2*b := by
    by_contra! hm
    obtain ⟨p, hp, t, hf⟩ := bad_lower (Nat.mul_pos hB hr') hm
    have hfail := hb.1 b le_rfl p hp t
    rw [hf] at hfail
    norm_num at hfail
  have dlog : (dimension B r).log2 ≤ 3*r := by
    have hdpos := hB.trans_le dlo
    apply Nat.le_of_lt_succ
    apply (Nat.log2_lt hdpos.ne').mpr
    calc
      _ ≤ B*r := dhi
      _ ≤ B*2^r := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
      _ = 2^(3*r) := by dsimp [B]; rw [← Nat.mul_pow, Nat.pow_mul]
      _ < 2^(3*r+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨symmetry _ _, dlo, dhi, good, bad, good_erm, bad_erm, g, b, hg, hb, hgpos,
    hgle, hbgt, ?_⟩
  calc
    _ ≤ (3*r)*(64*B) := Nat.mul_le_mul dlog hgle
    _ = 192*(B*r) := by ring
    _ ≤ 192*(2*b) := Nat.mul_le_mul_left _ hbgt.le
    _ = 384*b := by ring

end SymmetricERM
