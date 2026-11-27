module

public import SolvedProblems.SymmetricERMConstruction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace SymmetricERM

open scoped Classical

theorem dimension_bounds {B r : ℕ} (hr : 0 < r) : B ≤ dimension B r ∧ dimension B r ≤ B*r := by
  classical
  let z : Fin r := ⟨0, hr⟩
  let S := Finset.univ.image (fun b : Fin B => (b,z))
  have hs : NShatters S := by
    refine ⟨fun _ => {z}, fun _ => ∅, fun _ _ => by simp, ?_⟩
    intro T hT
    refine ⟨(Equiv.refl _, fun b => if (b,z) ∈ T then {z} else ∅), ?_⟩
    intro x hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases hb : (b,z) ∈ T <;> simp [classify, hb]
  constructor
  · have hcard : S.card = B := by
      rw [show S = _ from rfl, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
      simp
    apply hcard.ge.trans
    exact Finset.le_sup (s := Finset.univ.filter (@NShatters B r)) (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  · apply Finset.sup_le
    intro T _
    simpa using Finset.card_le_univ T

def unseen {B r m} (s : Sample B r m) (b : Fin B) : Label r :=
  Finset.univ.filter fun j => ∀ i, (s i).1 ≠ (b,j)

noncomputable def bad {B r} (m : ℕ) (s : Sample B r m) : Code B r := by
  classical
  exact if ∀ i, (s i).2 = ∅ then (Equiv.refl _, unseen s) else minimizer m s

theorem bad_unseen {B r m} {s : Sample B r m} (h : ∀ i, (s i).2 = ∅) (x : Point B r) :
    classify (bad m s) x ≠ ∅ ↔ ∀ i, (s i).1 ≠ x := by
  classical
  by_cases hx : ∀ i, (s i).1 ≠ x
  · have hj : x.2 ∈ unseen s x.1 := by simpa [unseen] using hx
    simpa [bad, h, classify, hj, hx] using Finset.ne_empty_of_mem hj
  · simp [bad, h, classify, unseen, hx]

theorem bad_erm {B r} : ERM (@bad B r) := by
  intro m s c
  by_cases h : ∀ i, (s i).2 = ∅
  · have hf : Fits (bad m s) s := by
      intro i
      rw [h i]
      by_contra hn
      exact (bad_unseen h _ |>.mp hn) i rfl
    rw [no_mistakes.mpr hf]
    exact Nat.zero_le _
  · simpa [bad, h] using minimizer_erm m s c

theorem sample_mass {X : Type} [Fintype X] {p : X → ℝ} (hp : Law p) {ι : Type}
    [Fintype ι] [DecidableEq ι] : (∑ xs : ι → X, ∏ i, p (xs i)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : ι) (x : X) => p x)]
  simp [hp.2]

/-- On the uniform law and constant background target, at most one point per draw
can cease to be an error; this holds for each sample, including repeated draws. -/
theorem bad_lower {B r m : ℕ} (hpos : 0 < B*r) (hm : 2*m ≤ B*r) :
    ∃ p, Law p ∧ ∃ t : Code B r, failure bad m p t = 1 := by
  classical
  let N := B*r
  let p := fun _ : Point B r => 1/(N : ℝ)
  let t := emptyCode B r
  have hN : (0 : ℝ) < N := by exact_mod_cast hpos
  have hn : Fintype.card (Point B r) = N := by simp [N]
  have hp : Law p := ⟨fun _ => by dsimp [p]; positivity, by simp [p, hn, ne_of_gt hN]⟩
  have hz (x : Point B r) : classify t x = ∅ := by simp [t, emptyCode, classify]
  have excessive (xs : Fin m → Point B r) :
      (1/4 : ℝ) < risk p t (bad m (fun i => (xs i, classify t (xs i)))) := by
    let seen := Finset.univ.image xs
    let s : Sample B r m := fun i => (xs i, classify t (xs i))
    have hs (i) : (s i).2 = ∅ := hz _
    have pointwise (x : Point B r) :
        classify (bad m s) x = classify t x ↔ x ∈ seen := by
      rw [hz]
      simpa [seen, s] using not_congr (bad_unseen hs x)
    have hcard : seen.card ≤ m := by simpa [seen] using Finset.card_image_le (s := Finset.univ) (f := xs)
    have nmiss : N ≤ 2 * seenᶜ.card := by
      rw [Finset.card_compl, hn]
      change 2 * m ≤ N at hm
      omega
    have hrisk : risk p t (bad m s) = seenᶜ.card / (N : ℝ) := by
      unfold risk
      simp_rw [pointwise]
      rw [Finset.sum_ite]
      have he : (Finset.univ.filter fun x => x ∉ seen) = seenᶜ := by ext; simp
      simp [he, p, div_eq_mul_inv]
    change (1/4 : ℝ) < risk p t (bad m s)
    rw [hrisk, lt_div_iff₀ hN]
    have : (N : ℝ) ≤ 2 * (seenᶜ.card : ℝ) := by exact_mod_cast nmiss
    linarith
  refine ⟨p, hp, t, ?_⟩
  unfold failure
  simp only [ite_eq_left (excessive _)]
  exact sample_mass hp

end SymmetricERM
