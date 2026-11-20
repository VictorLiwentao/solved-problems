module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace RationalReturns

private abbrev FlagWords {n} (b : Fin n → ℕ) :=
  {z : (i : Fin n) → Fin (b i) // Monotone (fun i ↦ (z i).val)}

private def flagEntry (b i j : ℕ) : ℤ :=
  if i ≤ j+1 then (b.choose (j+1-i) : ℤ) else 0

private def flagMatrix {n} (b : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦ flagEntry (b i) i.val j.val

private theorem entry_pascal (b i j : ℕ) :
    flagEntry (b+1) i (j+1) = flagEntry b i (j+1) + flagEntry b i j := by
  unfold flagEntry
  by_cases h : i ≤ j+1
  · have h' : i ≤ j+1+1 := by omega
    have e : j+1+1-i = (j+1-i)+1 := by omega
    simp only [ite_eq_left h, ite_eq_left h', e, Nat.choose_succ_succ, Nat.cast_add, Nat.succ_eq_add_one]
    exact add_comm _ _
  · by_cases h' : i = j+1+1
    · subst i
      simp
    · have e : ¬ i ≤ j+1+1 := by omega
      simp [h, e]

private theorem entry_zero (b i : ℕ) :
    flagEntry (b+1) i 0 = flagEntry b i 0 + (if i = 0 then 1 else 0) := by
  cases i with
  | zero => simp [flagEntry]
  | succ i => cases i <;> simp [flagEntry]

/-- Pascal's identity lifts the columns one level. The column-zero correction contributes the
trailing principal minor. -/
private theorem det_succ_flag {n} (b : Fin (n+1) → ℕ) :
    (flagMatrix (fun i ↦ b i + 1)).det =
      (flagMatrix b).det + (flagMatrix (fun i : Fin n ↦ b i.succ + 1)).det := by
  let D := flagMatrix b
  let A := flagMatrix (fun i ↦ b i + 1)
  let e : Fin (n+1) → ℤ := fun i ↦ if i = 0 then 1 else 0
  let col : Fin (n+1) → ℤ := fun i ↦ D i 0
  have first : col + e = (fun i ↦ A i 0) := by
    funext i
    change flagEntry (b i) i.val 0 + (if i = 0 then 1 else 0) =
      flagEntry (b i + 1) i.val 0
    rw [entry_zero]
    simp
  have same : D.det = (A.updateCol 0 col).det := by
    apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ ↦ -1)
    · simp [col]
    · intro i j
      rw [Matrix.updateCol_ne j.succ_ne_zero]
      change flagEntry (b i) i.val (j.val+1) =
        flagEntry (b i + 1) i.val (j.val+1) + (-1) * flagEntry (b i) i.val j.val
      rw [entry_pascal]; ring
  have minor : (A.updateCol 0 e).det = (flagMatrix (fun i : Fin n ↦ b i.succ + 1)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Matrix.updateCol_self, one_mul, e,
      Fin.succ_ne_zero, ite_false, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      Fin.succAbove_zero]
    simp only [ite_true, one_mul]
    congr 1
    ext i j
    rw [Matrix.submatrix_apply, Matrix.updateCol_ne j.succ_ne_zero]
    simp [A, flagMatrix, flagEntry]
  change A.det = D.det + _
  calc
    _ = (A.updateCol 0 (col+e)).det := by rw [first, A.updateCol_eq_self]
    _ = _ := by rw [Matrix.det_updateCol_add, ← same, minor]

private def succWord {n} {b : Fin (n+1) → ℕ} (z : FlagWords b) :
    FlagWords (fun i ↦ b i+1) :=
  ⟨fun i ↦ (z.val i).succ, fun _ _ h ↦ Nat.succ_le_succ (z.property h)⟩

private def zeroWord {n} {b : Fin (n+1) → ℕ} (z : FlagWords (fun i : Fin n ↦ b i.succ+1)) :
    FlagWords (fun i ↦ b i+1) := by
  refine ⟨Fin.cons (0 : Fin (b 0 + 1)) z.val, ?_⟩
  intro i j hij
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim ((not_lt_of_ge hij) (Fin.succ_pos i))
    | succ j => exact z.property (Fin.succ_le_succ_iff.mp hij)

private def predWord {n} {b : Fin (n+1) → ℕ} (z : FlagWords (fun i ↦ b i+1))
    (h : (z.val 0).val ≠ 0) : FlagWords b := by
  have pos (i) : 0 < (z.val i).val := (Nat.pos_of_ne_zero h).trans_le (z.property (Fin.zero_le i))
  exact ⟨fun i ↦ ⟨(z.val i).val - 1, by have hv : (z.val i).val < b i + 1 := (z.val i).isLt; have := pos i; omega⟩,
    fun _ _ hij ↦ Nat.sub_le_sub_right (z.property hij) _⟩

private def flagSplit {n} (b : Fin (n+1) → ℕ) :
    FlagWords (fun i ↦ b i+1) ≃ FlagWords b ⊕ FlagWords (fun i : Fin n ↦ b i.succ+1) where
  toFun z := if h : (z.val 0).val = 0 then Sum.inr
      ⟨fun i ↦ z.val i.succ, fun _ _ hij ↦ z.property (Fin.succ_le_succ_iff.mpr hij)⟩
    else Sum.inl (predWord z h)
  invFun := Sum.elim succWord zeroWord
  left_inv z := by
    dsimp only
    split
    next hz =>
      apply Subtype.ext
      funext i
      induction i using Fin.cases with
      | zero => exact Fin.ext hz.symm
      | succ i => rfl
    next hz =>
      apply Subtype.ext; funext i
      apply Fin.ext
      change (z.val i).val - 1 + 1 = _
      have hi : (z.val 0).val ≤ (z.val i).val := z.property (Fin.zero_le i)
      exact Nat.sub_add_cancel (by omega)
  right_inv z := by
    cases z with
    | inl a =>
      simp only [Sum.elim_inl, succWord, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte]
      congr 1
    | inr a =>
      simp only [Sum.elim_inr, zeroWord, Fin.cons_zero, Fin.val_zero, ↓reduceDIte]
      rfl

/-- The binomial determinant counts weakly increasing choices below nondecreasing flags.
Each entry is the zero-based rank of a chosen column. -/
theorem flagged_count {n} (b : Fin n → ℕ) (hb : Monotone b) :
    (Fintype.card {z : (i : Fin n) → Fin (b i) // Monotone (fun i ↦ (z i).val)} : ℤ) =
      (Matrix.of fun i j : Fin n ↦ if i.val ≤ j.val+1 then ((b i).choose (j.val+1-i.val) : ℤ)
        else 0).det := by
  classical
  change (Fintype.card (FlagWords b) : ℤ) = (flagMatrix b).det
  induction n with
  | zero =>
    let : Unique (FlagWords b) := ⟨⟨⟨fun i ↦ i.elim0, fun {i} ↦ Fin.elim0 i⟩⟩,
      fun _ ↦ Subtype.ext (funext fun i ↦ i.elim0)⟩
    simp [Matrix.det_fin_zero]
  | succ n ih =>
    generalize hk : b 0 = k
    induction k generalizing b with
    | zero =>
      have : IsEmpty (FlagWords b) := ⟨fun z ↦ by have := (z.val 0).isLt; omega⟩
      rw [Fintype.card_eq_zero, Nat.cast_zero]
      symm
      apply Matrix.det_eq_zero_of_row_eq_zero 0
      intro j
      simp [flagMatrix, flagEntry, hk]
    | succ k ih' =>
      let a (i : Fin (n+1)) := b i-1
      have pos (i) : 0 < b i := by have := hb (Fin.zero_le i); omega
      have eqv : b = fun i ↦ a i+1 := by
        funext i; dsimp [a]; have := pos i; omega
      have mono : Monotone a := fun _ _ h ↦ Nat.sub_le_sub_right (hb h) 1
      have hfirst : a 0 = k := by simp [a, hk]
      have tailMono : Monotone (fun i : Fin n ↦ a i.succ+1) :=
        fun _ _ h ↦ Nat.succ_le_succ (mono (Fin.succ_le_succ_iff.mpr h))
      have first := ih' a mono hfirst
      have tail := ih (fun i ↦ a i.succ+1) tailMono
      rw [eqv, Fintype.card_congr (flagSplit a), Fintype.card_sum, Nat.cast_add,
        first, tail, det_succ_flag]

end RationalReturns
