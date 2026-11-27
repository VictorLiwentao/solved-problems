module

public import SolvedProblems.SymmetricERMGeometry
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

@[expose] public section

namespace SymmetricERM

open scoped Classical

noncomputable def hit {B r} (p : Point B r → ℝ) (t c : Code B r) (x : Point B r) : ℝ :=
  if classify c x = classify t x then p x else 0

theorem hit_nonnegative {B r} {p : Point B r → ℝ} (hp : Law p) (t c x) : 0 ≤ hit p t c x := by
  unfold hit
  split <;> simp [hp.1]

theorem hit_risk {B r} {p : Point B r → ℝ} (hp : Law p) (t c : Code B r) :
    (∑ x, hit p t c x) + risk p t c = 1 := by
  unfold risk hit
  rw [← Finset.sum_add_distrib, ← hp.2]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp

/-- Independent retained draws determine the reconstruction; other coordinates must
agree with it. -/
noncomputable def reconstructionTerm {B r m} (I : Finset (Fin m)) (p : Point B r → ℝ)
    (t : Code B r) (D : (I → Point B r) → Code B r)
    (a : I → Point B r) (v : {i : Fin m // i ∉ I} → Point B r) : ℝ :=
  if (1/4 : ℝ) < risk p t (D a) then
    (∏ i, p (a i)) * ∏ j, hit p t (D a) (v j) else 0

theorem term_nonnegative {B r m} (I : Finset (Fin m)) {p : Point B r → ℝ}
    (hp : Law p) (t D a v) : 0 ≤ reconstructionTerm I p t D a v := by
  unfold reconstructionTerm
  split
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => hp.1 _)
      (Finset.prod_nonneg fun _ _ => hit_nonnegative hp _ _ _)
  · exact le_rfl

theorem term_sum_le {B r m} (I : Finset (Fin m)) {p : Point B r → ℝ}
    (hp : Law p) (t D) :
    (∑ xs : Fin m → Point B r,
      reconstructionTerm I p t D (fun i => xs i) (fun j => xs j))
      ≤ (3/4 : ℝ)^(m - I.card) := by
  classical
  let splitSample := Equiv.piEquivPiSubtypeProd (· ∈ I) (fun _ => Point B r)
  rw [show (∑ xs : Fin m → Point B r, reconstructionTerm I p t D
          (fun i => xs i) (fun j => xs j)) =
      ∑ a, ∑ v, reconstructionTerm I p t D a v from
    (splitSample.sum_comp (fun av => reconstructionTerm I p t D av.1 av.2)).trans
      (Fintype.sum_prod_type' _)]
  have n : Fintype.card {i : Fin m // i ∉ I} = m - I.card := by
    rw [Fintype.card_subtype_compl]; simp
  calc
    _ ≤ ∑ a : I → Point B r, (∏ i, p (a i)) * (3/4 : ℝ) ^ (m - I.card) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases h : (1/4 : ℝ) < risk p t (D a)
      · simp only [reconstructionTerm, ite_eq_left h, ← Finset.mul_sum]
        rw [← Fintype.prod_sum (fun (_ : {i : Fin m // i ∉ I}) x => hit p t (D a) x)]
        simp only [Finset.prod_const, Finset.card_univ, n]
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => hp.1 _)
        apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hit_nonnegative hp _ _ _)
        linarith [hit_risk hp t (D a)]
      · simp only [reconstructionTerm, ite_eq_right h, Finset.sum_const_zero]
        exact mul_nonneg (Finset.prod_nonneg fun _ _ => hp.1 _) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, sample_mass hp, one_mul]

def observe {B r} {ι : Type} (t : Code B r) (xs : ι → Point B r) :
    ι → Point B r × Label r := fun i => (xs i, classify t (xs i))

theorem erm_fits {B r m} {A : Learner B r} (hA : ERM A) (t : Code B r) (xs : Fin m → Point B r) :
    Fits (A m (observe t xs)) (observe t xs) := by
  apply no_mistakes.mp
  apply Nat.eq_zero_of_le_zero
  exact (hA m _ t).trans (no_mistakes.mpr (fun _ => rfl)).le

/-- Union over reconstructions from all permutations and at most B retained sample indices. -/
theorem compression_bound {B r m} {p : Point B r → ℝ} (hp : Law p) (t : Code B r) :
    failure good m p t ≤ (Fintype.card (Equiv.Perm (Label r)) : ℝ) *
      ∑ I : Finset (Fin m), if I.card ≤ B then (3/4 : ℝ) ^ (m - I.card) else 0 := by
  classical
  let term (e : Equiv.Perm (Label r)) (I : Finset (Fin m)) (xs : Fin m → Point B r) : ℝ :=
    if I.card ≤ B then reconstructionTerm I p t (fun a => decode e (observe t a))
      (fun i => xs i) (fun j => xs j) else 0
  have nonneg e I xs : 0 ≤ term e I xs := by
    unfold term; split
    · exact term_nonnegative _ hp _ _ _ _
    · exact le_rfl
  unfold failure
  calc
    _ ≤ ∑ xs : Fin m → Point B r, ∑ e : Equiv.Perm (Label r), ∑ I : Finset (Fin m), term e I xs := by
      apply Finset.sum_le_sum
      intro xs _
      let s := observe t xs
      change (if (1/4 : ℝ) < risk p t (good m s) then _ else _) ≤ _
      split
      · rename_i big
        obtain ⟨e, I, hI, hd⟩ := compressed (s := s) ⟨t, fun _ => rfl⟩
        have hh : Fits (good m s) s := erm_fits good_erm t xs
        have key : term e I xs = ∏ i, p (xs i) := by
          unfold term reconstructionTerm
          simp only [ite_eq_left hI]
          change (if 1/4 < risk p t (decode e (fun i : I => s i)) then _ else _) = _
          rw [← hd, ite_eq_left big]
          have each (j : {i : Fin m // i ∉ I}) :
              hit p t (good m s) (xs j) = p (xs j) := by
            exact ite_eq_left (hh j)
          change (∏ i : I, p (xs i)) *
            (∏ j : {i : Fin m // i ∉ I}, hit p t (decode e (fun i : I => s i)) (xs j)) = _
          rw [← hd]
          simp_rw [each]
          have instEq : Finset.Subtype.fintype I = Subtype.fintype (· ∈ I) :=
            Subsingleton.elim _ _
          rw [instEq]
          exact Fintype.prod_subtype_mul_prod_subtype (· ∈ I) (fun i => p (xs i))
        rw [← key]
        exact (Finset.single_le_sum (fun I _ => nonneg e I xs) (Finset.mem_univ I)).trans
          (Finset.single_le_sum (fun e' _ => Finset.sum_nonneg (fun I _ => nonneg e' I xs))
            (Finset.mem_univ e))
      · exact Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun I _ => nonneg e I xs))
    _ = ∑ e : Equiv.Perm (Label r), ∑ I : Finset (Fin m), ∑ xs : Fin m → Point B r, term e I xs := by
      rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (f := fun xs I => term _ I xs)]
    _ ≤ ∑ _e : Equiv.Perm (Label r), ∑ I : Finset (Fin m),
        if I.card ≤ B then (3/4 : ℝ)^(m-I.card) else 0 := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro I _
      by_cases h : I.card ≤ B
      · simpa [term, h] using term_sum_le I hp t (fun a => decode e (observe t a))
      · simp [term, h]
    _ = _ := by simp

end SymmetricERM
