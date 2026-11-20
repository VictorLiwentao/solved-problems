module

public import SolvedProblems.RationalReturnsSplit
public import SolvedProblems.RationalReturnsInversion

@[expose] public section
namespace RationalReturns

open Finset
open scoped BigOperators
open Classical

/-- The strict upper triangle counts all segments between boundary rows. -/
noncomputable def segmentMatrix (m n d k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  fun i j => if i < j then (segmentCount m n d k i.val j.val : ℤ) else 0

private def rankWeight (S : Finset ℕ) (s a : ℕ) : ℤ :=
  (((S.filter (· < a)).card.choose s : ℕ) : ℤ)

private noncomputable def weight (m n d k i j s : ℕ) : ℤ :=
  ∑ w : Segment m n d k i j, ((contactRows w).card.choose s : ℤ)

/-- Splitting at a fixed last marked contact factors the count of all choices of earlier marks. -/
private theorem split_weight {m n d k i a j : ℕ} (strict : StrictMono (edge m n))
    (hia : i < a) (haj : a < j) (s : ℕ) :
    weight m n d k i a s * (segmentCount m n d k a j : ℤ) =
      ∑ w : Segment m n d k i j, if a ∈ contactRows w then rankWeight (contactRows w) s a else 0 := by
  classical
  let L := Segment m n d k i a
  let R := Segment m n d k a j
  let W := Segment m n d k i j
  let mark (w : W) := a ∈ contactRows w
  let f (w : W) := rankWeight (contactRows w) s a
  let fw (lr : L × R) : ℤ := ((contactRows lr.1).card.choose s : ℤ)
  let cut := splitAtContact (d:=d) (k:=k) strict hia haj
  have a1 : (∑ x : L × R, fw x) = weight m n d k i a s * (segmentCount m n d k a j : ℤ) := by
    rw [Fintype.sum_prod_type,weight,segmentCount,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    simp [fw,R,mul_comm]
  have a2 : (∑ z : {w : W // mark w}, f z.val) = ∑ x : L × R, fw x := by
    apply Fintype.sum_equiv cut
    intro z
    dsimp only [f,fw,rankWeight]
    rw [left_contacts strict hia haj z.prop]
  have a3 := (Finset.univ.filter mark).sum_subtype (p:=mark) (F := inferInstance) (fun z => by simp) f
  rw [← a1, ← a2, ← a3,Finset.sum_filter]

private theorem rank_sum {n : ℕ} (S : Finset ℕ) (hs : S ⊆ Finset.range (n+1)) (s : ℕ) :
    (∑ a : Fin (n+1), if a.val ∈ S then rankWeight S s a.val else 0) = (S.card.choose (s+1) : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a ∈ S then rankWeight S s a else 0)]
  rw [← Finset.sum_filter]
  have filter_eq : ((Finset.range (n+1)).filter (· ∈ S)) = S := by
    ext x
    exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨hs h,h⟩⟩
  rw [filter_eq]
  unfold rankWeight
  exact_mod_cast sum_rank_choose S s

private theorem power_weight {m n d k : ℕ} (strict : StrictMono (edge m n)) (s : ℕ) (i j : Fin (n+1)) :
    (segmentMatrix m n d k ^ (s+1)) i j =
      if i < j then weight m n d k i.val j.val s else 0 := by
  classical
  induction s generalizing i j with
  | zero =>
    by_cases h : i < j <;> simp [segmentMatrix,h,weight,segmentCount]
  | succ s ih =>
    rw [pow_succ,Matrix.mul_apply]
    by_cases ij : i < j
    · rw [ite_eq_left ij]
      let W := Segment m n d k i.val j.val
      let F (a : Fin (n+1)) (w : W) := if a.val ∈ contactRows w then rankWeight (contactRows w) s a.val else 0
      have term (a : Fin (n+1)) : (segmentMatrix m n d k ^ (s+1)) i a * segmentMatrix m n d k a j =
          ∑ w : W, F a w := by
        rw [ih,segmentMatrix]
        by_cases ia : i < a <;> by_cases aj : a < j
        · simp only [ia,aj,ite_true]
          exact split_weight strict ia aj s
        all_goals
          simp only [ia,aj,ite_true,ite_false,zero_mul,mul_zero]
          symm
          apply Finset.sum_eq_zero
          intro w hw
          dsimp [F]
          apply ite_eq_right
          intro mem
          have h := Finset.mem_Ioo.mp (contactRows_subset mem)
          omega
      simp_rw [term]
      rw [Finset.sum_comm,weight]
      apply Finset.sum_congr rfl
      intro w hw
      apply rank_sum
      intro a ha
      have h := Finset.mem_Ioo.mp (contactRows_subset ha)
      exact Finset.mem_range.mpr (h.2.trans j.isLt)
    · rw [ite_eq_right ij]
      apply Finset.sum_eq_zero
      intro a ha
      rw [ih,segmentMatrix]
      by_cases ia : i < a
      · have aj : ¬ a < j := fun h => ij (ia.trans h)
        simp [aj]
      · simp [ia]

/-- A binomial inversion converts the powers of the all-segment matrix into the
number of paths with a prescribed total number of returns (including the endpoint). -/
theorem count_by_powers {m n d k ℓ : ℕ} (hn : 0 < n) (hm : n ≤ m) (hℓ : 0 < ℓ) (hℓn : ℓ ≤ n) :
    (Fintype.card {w : Segment m n d k 0 n // (contactRows w).card+1=ℓ} : ℤ) =
      ∑ s ∈ Finset.Ico (ℓ-1) n, (-1:ℤ)^(s-(ℓ-1)) * (s.choose (ℓ-1):ℤ) *
        (segmentMatrix m n d k ^ (s+1)) 0 (Fin.last n) := by
  classical
  let W := Segment m n d k 0 n
  have weight_eq (s : ℕ) : (segmentMatrix m n d k ^ (s+1)) 0 (Fin.last n) =
      ∑ w : W, ((contactRows w).card.choose s : ℤ) := by
    rw [power_weight (edge_strict hn hm),ite_eq_left (by exact hn : (0 : Fin (n+1)) < Fin.last n)]
    rfl
  simp_rw [weight_eq,Finset.mul_sum]
  rw [Finset.sum_comm]
  let good (w : W) := (contactRows w).card + 1 = ℓ
  change (Fintype.card {w : W // good w} : ℤ) = _
  have num : (Fintype.card {w : W // good w} : ℤ) = ∑ w : W, if good w then 1 else 0 := by
    rw [Fintype.card_subtype,Finset.card_filter]
    push_cast
    rfl
  rw [num]
  apply Finset.sum_congr rfl
  intro w hw
  have ht := Finset.card_le_card (contactRows_subset (w:=w))
  rw [Nat.card_Ioo] at ht
  rw [binomial_inversion n (ℓ-1) (contactRows w).card (by omega) (by omega)]
  by_cases h : good w
  · have eq : (contactRows w).card = ℓ-1 := by dsimp [good] at h; omega
    simp [h,eq]
  · have ne : (contactRows w).card ≠ ℓ-1 := by dsimp [good] at h; omega
    simp [h,ne]

end RationalReturns
