module

public import SolvedProblems.FussModel
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Fintype.BigOperators

public section

namespace FussDyck

open Finset

theorem prefixN_total (v : Word n b) : prefixN v b = ∑ i, (v i).val := by
  unfold prefixN
  rw [List.take_of_length_le (by simp), List.sum_ofFn]

private def unitAt (u : Finset (Fin b)) (i : Fin b) : Nat := if i ∈ u then 1 else 0

private theorem sum_unitAt (u : Finset (Fin b)) : ∑ i, unitAt u i = u.card := by
  simp [unitAt]

private noncomputable def residual (v : Word n b) : Fin b →₀ Nat :=
  Finsupp.equivFunOnFinite.symm (fun i => (v i).val - 2)

private theorem split_value (v : Word n b) (i : Fin b) :
    unitAt (positions v 0) i + unitAt (positions v 1) i + residual v i = (v i).val := by
  simp only [unitAt,positions,mem_filter,mem_univ,true_and,residual,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  split <;> split <;> omega

private theorem split_sum (v : Word n b) :
    (positions v 0).card + (positions v 1).card + (∑ i, residual v i) = prefixN v b := by
  rw [← sum_unitAt, ← sum_unitAt, ← sum_add_distrib, ← sum_add_distrib, prefixN_total]
  exact sum_congr rfl (fun i _ => split_value v i)

private abbrev Config (n b k j : Nat) :=
  (p : (univ : Finset (Fin b)).powersetCard k) ×
  (l : p.val.powersetCard j) × ↥(l.val.finsuppAntidiag (n-k-j))

private def value {n b k j : Nat} (c : Config n b k j) (i : Fin b) : Nat :=
  unitAt c.1.val i + unitAt c.2.1.val i + c.2.2.val i

private theorem config_sum {n b k j : Nat} (c : Config n b k j) (hkj : k+j ≤ n) :
    ∑ i, value c i = n := by
  have hp := (mem_powersetCard.mp c.1.property).2
  have hl := (mem_powersetCard.mp c.2.1.property).2
  have he := (mem_finsuppAntidiag'.mp c.2.2.property).1
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at he
  simp only [value,sum_add_distrib,sum_unitAt,hp,hl]
  omega

private theorem value_positive {n b k j : Nat} (c : Config n b k j) (i : Fin b) :
    (0 < value c i ↔ i ∈ c.1.val) ∧ (1 < value c i ↔ i ∈ c.2.1.val) := by
  have hl := (mem_powersetCard.mp c.2.1.property).1
  have he := (mem_finsuppAntidiag.mp c.2.2.property).2
  by_cases hi : i ∈ c.2.1.val
  · simp [value,unitAt,hi,hl hi]; omega
  · have hz : c.2.2.val i = 0 := Finsupp.notMem_support_iff.mp (fun hm => hi (he hm))
    by_cases hp : i ∈ c.1.val <;> simp [value,unitAt,hi,hp,hz]

private def decode {n b k j : Nat} (hkj : k+j ≤ n) (c : Config n b k j) :
    {v : Word n b // Stats v k j} := by
  let v : Word n b := fun i => ⟨value c i,by
    have := single_le_sum (f := value c) (fun i _ => Nat.zero_le _) (mem_univ i)
    rw [config_sum c hkj] at this
    omega⟩
  have p : positions v 0 = c.1.val := by
    ext i; simpa [positions,v] using (value_positive c i).1
  have l : positions v 1 = c.2.1.val := by
    ext i; simpa [positions,v] using (value_positive c i).2
  exact ⟨v,by rw [Stats,prefixN_total,p,l]; exact ⟨config_sum c hkj,
    (mem_powersetCard.mp c.1.property).2,(mem_powersetCard.mp c.2.1.property).2⟩⟩

private theorem decode_bijective {n b k j : Nat} (hkj : k+j ≤ n) :
    Function.Bijective (decode (b := b) hkj) := by
  constructor
  · rintro ⟨⟨P,hP⟩,⟨L,hL⟩,⟨e,he⟩⟩ ⟨⟨P',hP'⟩,⟨L',hL'⟩,⟨e',he'⟩⟩ eq
    let c : Config n b k j := ⟨⟨P,hP⟩,⟨L,hL⟩,⟨e,he⟩⟩
    let c' : Config n b k j := ⟨⟨P',hP'⟩,⟨L',hL'⟩,⟨e',he'⟩⟩
    have same (i : Fin b) : value c i = value c' i :=
      congrArg (fun u : {v : Word n b // Stats v k j} => (u.val i).val) eq
    have ep : P = P' := by
      ext i
      exact (value_positive c i).1.symm.trans ((same i) ▸ (value_positive c' i).1)
    have el : L = L' := by
      ext i
      exact (value_positive c i).2.symm.trans ((same i) ▸ (value_positive c' i).2)
    subst P'; subst L'
    have ee : e = e' := by
      ext i
      exact Nat.add_left_cancel (same i)
    subst e'
    rfl
  · rintro ⟨v,hv⟩
    obtain ⟨ht,hp,hl⟩ := hv
    let P := positions v 0
    let L := positions v 1
    have sub : L ⊆ P := by
      intro i hi
      simp [L,positions] at hi
      simpa [P,positions] using (show 0 < (v i).val by omega)
    let e := residual v
    have hsum := split_sum v
    rw [hp,hl,ht] at hsum
    have hmem : e ∈ L.finsuppAntidiag (n-k-j) := by
      apply mem_finsuppAntidiag'.mpr
      constructor
      · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        change (∑ i, residual v i) = _
        omega
      · intro i hi
        simp [e,residual] at hi
        simp [L,positions]
        omega
    let c : Config n b k j := ⟨⟨P,mem_powersetCard.mpr ⟨subset_univ _,hp⟩⟩,
       ⟨L,mem_powersetCard.mpr ⟨sub,hl⟩⟩,⟨e,hmem⟩⟩
    exact ⟨c,Subtype.ext (funext (fun i => Fin.ext (split_value v i)))⟩

private theorem free_feasible (v : Word n b) (h : Stats v k j) :
    k+j ≤ n ∧ j ≤ k ∧ (0 < n → 0 < k) := by
  obtain ⟨ht,hp,hl⟩ := h
  have hsum := split_sum v
  rw [hp,hl,ht] at hsum
  have sub : positions v 1 ⊆ positions v 0 := by
    intro i hi
    simp only [positions, mem_filter, mem_univ, true_and] at hi ⊢
    omega
  refine ⟨by omega,hp ▸ hl ▸ card_le_card sub,?_⟩
  intro hn
  by_contra! hz
  have all : ∀ i, (v i).val = 0 := by
    intro i
    have empty : positions v 0 = ∅ := card_eq_zero.mp (by omega)
    have := (show i ∉ positions v 0 by simp [empty])
    simp only [positions, mem_filter, mem_univ, true_and] at this
    omega
  rw [prefixN_total] at ht
  simp [all] at ht
  omega

theorem free_zero {n b k j : Nat} (hbad : n < k ∨ (0 < n ∧ k = 0) ∨ n < k+j ∨ k < j) :
    freeCount n b k j = 0 := by
  classical
  unfold freeCount
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun ⟨v,h⟩ => ?_⟩
  obtain ⟨hkj,hjk,hpos⟩ := free_feasible v h
  rcases hbad with h | ⟨h,rfl⟩ | h | h <;> omega

theorem free_formula {n b k : Nat} (hk : k ≤ n) (j : Nat) :
    freeCount n b k j = b.choose k * hCoeff k (n-k) j := by
  classical
  by_cases hkj : k+j ≤ n
  · have eq := Fintype.card_congr (Equiv.ofBijective _ (decode_bijective (b := b) hkj))
    change Fintype.card {v : Word n b // Stats v k j} = _
    rw [← eq, Fintype.card_sigma]
    have inner (p : (univ : Finset (Fin b)).powersetCard k) :
        Fintype.card ((l : p.val.powersetCard j) × ↥(l.val.finsuppAntidiag (n-k-j))) =
          k.choose j * (j+(n-k-j)-1).choose (n-k-j) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_coe,card_finsuppAntidiag_nat_eq_choose,
        (mem_powersetCard.mp (Subtype.prop _)).2]
      simp [card_powersetCard, (mem_powersetCard.mp p.property).2]
    simp only [inner, sum_const, card_univ, Fintype.card_coe, card_powersetCard,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    by_cases hs : n-k = 0
    · have hj : j = 0 := by omega
      simp [hs,hj,hCoeff]
    by_cases hj : j = 0
    · simp [hCoeff,hs,hj,Nat.choose_eq_zero_of_lt (show n-k-1<n-k by omega)]
    have he : j+(n-k-j)-1 = n-k-1 := by omega
    rw [he]
    have hj' : j-1 ≤ n-k-1 := by omega
    rw [show n-k-j = (n-k-1)-(j-1) by omega,Nat.choose_symm hj']
    simp [hCoeff,hs,hj]
  · rw [free_zero (Or.inr (Or.inr (Or.inl (by omega))))]
    by_cases hs : n-k = 0
    · have hj : j ≠ 0 := by omega
      simp [hCoeff,hs,hj]
    have hj : j ≠ 0 := by omega
    have small : n-k-1 < j-1 := by omega
    simp [hCoeff,hs,hj,Nat.choose_eq_zero_of_lt small]

end FussDyck
