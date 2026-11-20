module

public import SolvedProblems.PrivateWitnessIID
import Mathlib.Tactic.NormNum

public section
namespace PrivateWitness
open scoped NNReal ENNReal

private theorem flat_total (F : Finset Nat) (a : ℝ≥0∞) :
    (∑' x : Nat, if x ∈ F then a else 0) = (F.card:ℝ≥0∞)*a := by
  rw [tsum_eq_sum (s := F) (fun x hx => by simp [hx])]
  simp

private noncomputable def flat (F : Finset Nat) (hne : F.card ≠ 0) : Law := by
  refine ⟨fun x => if x ∈ F then (F.card:ℝ≥0∞)⁻¹ else 0,?_⟩
  rw [flat_total,ENNReal.mul_inv_cancel (by exact_mod_cast hne) (by simp)]

private theorem iid_depth (p : Law) (f : List Nat → ℝ≥0∞) (b : Nat → ℝ≥0∞)
    (point : ∀ h, f h ≤ b h.length) (n : Nat) (h : List Nat) :
    iid p f n h ≤ b (n+h.length) := by
  induction n generalizing h with
  | zero => simpa [iid] using point h
  | succ n ih =>
    calc
      _ ≤ ∑' x, p x * b (n+(x::h).length) := ENNReal.tsum_le_tsum fun _ => mul_le_mul_right (ih _) _
      _ = _ := by simp only [List.length_cons,Nat.succ_add,Nat.add_succ,ENNReal.tsum_mul_right,p.total,one_mul]

/-- The rule samples uniformly from an appropriately large finite subset of the common
intersection. The number of observations is its only input. -/
theorem common_sampler (Ls : List (Set Nat)) (k : ℝ≥0) (budget : 1 ≤ k)
    (inf : {x | ∀ L ∈ Ls, x ∈ L}.Infinite) :
    ∃ G : Rule, Private G k ∧ ∀ p, Admissible Ls p → Exponential (error G p) := by
  classical
  let size (n : Nat) := (n+1)*2^n
  choose F sub card using fun n => inf.exists_subset_card_eq (size n)
  have pos (n) : (F n).card ≠ 0 := by rw [card]; simp [size]
  let G (h : List Nat) := flat (F h.length) (pos _)
  refine ⟨G,?_,?_⟩
  · intro u v a b E
    have same : G (u++a::v) = G (u++b::v) := by simp [G]
    rw [same]
    exact le_mul_of_one_le_left' (by exact_mod_cast budget)
  · rintro p ⟨⟨L,hL,inside⟩,_⟩
    let r : ℝ≥0 := 1/2
    have point (h : List Nat) : mass (G h) {x | x ∉ p.support ∨ x ∈ h} ≤ (r:ℝ≥0∞)^h.length := by
      let n := h.length
      let a := ((F n).card:ℝ≥0∞)⁻¹
      have subp : ∀ x ∈ F n, x ∈ p.support := fun x hx => inside (sub n hx L hL)
      have small : mass (G h) {x | x ∉ p.support ∨ x ∈ h} ≤
          ∑' x : Nat, if x ∈ h.toFinset then a else 0 := by
        apply ENNReal.tsum_le_tsum
        intro x
        simp only [Set.mem_ofPred_eq, G,flat]
        by_cases hx : x ∈ F n
        · simp [a,n] at hx ⊢
          simp [hx,subp x hx]
        · simp [a,n] at hx ⊢
          simp [hx]
      rw [flat_total] at small
      have hcard : h.toFinset.card ≤ n+1 := h.toFinset_card_le.trans (Nat.le_succ _)
      calc
        _ ≤ (h.toFinset.card:ℝ≥0∞)*a := small
        _ ≤ ((n+1:Nat):ℝ≥0∞)*a := mul_le_mul_left (by exact_mod_cast hcard) _
        _ = _ := by
          unfold a
          rw [card]
          simp only [size,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
          rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),← mul_assoc,ENNReal.mul_inv_cancel (by simp) (by simp),one_mul]
          simp [r,n,ENNReal.inv_pow]
    refine ⟨1,r,by norm_num [r],fun n => ?_⟩
    simpa [error] using iid_depth p _ (fun j => (r:ℝ≥0∞)^j) point n []

end PrivateWitness
