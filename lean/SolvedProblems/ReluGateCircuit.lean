module

public import SolvedProblems.ReluLineRegions
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace ReluMoments

/-- One affine form in the real input and all previous hidden coordinates. -/
structure GateAffine (n : ℕ) where
  direct : Line
  weight : Fin n → ℝ

noncomputable def GateAffine.eval {n : ℕ} (a : GateAffine n) (x : ℝ) (v : Fin n → ℝ) : ℝ :=
  a.direct.value x + ∑ i, a.weight i * v i

noncomputable def GateAffine.onLines {n : ℕ} (a : GateAffine n) (v : Fin n → Line) : Line :=
  (a.direct.1 + ∑ i, a.weight i * (v i).1,a.direct.2 + ∑ i, a.weight i * (v i).2)

theorem GateAffine.eval_onLines {n : ℕ} (a : GateAffine n) (v : Fin n → Line) (x : ℝ) :
    a.eval x (fun i => (v i).value x) = (a.onLines v).value x := by
  simp only [eval,onLines,Line.value,add_mul,Finset.sum_mul,mul_add,Finset.sum_add_distrib,mul_assoc]
  ring

/-- A feedforward computation in a topological order. One constructor adds exactly
one scalar ReLU; later gates may reuse its output any number of times. -/
inductive Circuit : ℕ → Type where
  | empty : Circuit 0
  | append {n : ℕ} (prev : Circuit n) (a : GateAffine n) : Circuit (n+1)

noncomputable def Circuit.values {n : ℕ} (b : Circuit n) (x : ℝ) : Fin n → ℝ :=
  match b with
  | .empty => Fin.elim0
  | .append b a => Fin.snoc (α:=fun _ => ℝ) (b.values x) (max (a.eval x (b.values x)) 0)

noncomputable def Circuit.maskLines {n : ℕ} (b : Circuit n) (σ : Fin n → Bool) : Fin n → Line :=
  match b with
  | .empty => Fin.elim0
  | @append k prev a =>
    let v := prev.maskLines (Fin.init σ)
    Fin.snoc (α:=fun _ => Line) v (if σ (Fin.last k) then a.onLines v else Line.zero)

noncomputable def Circuit.tests {n : ℕ} (b : Circuit n) : Finset Line :=
  match b with
  | .empty => ∅
  | @append k prev a => prev.tests ∪ Finset.univ.image (fun σ : Fin k → Bool => a.onLines (prev.maskLines σ))

theorem Circuit.card_tests {n : ℕ} (b : Circuit n) : b.tests.card + 1 ≤ 2^n := by
  induction b with
  | empty => simp [tests]
  | @append k prev a ih =>
    have h : (Finset.univ.image (fun σ : Fin k → Bool => a.onLines (prev.maskLines σ))).card ≤ 2^k := by
      simpa using (Finset.card_image_le (s:=Finset.univ) (f:=fun σ : Fin k → Bool => a.onLines (prev.maskLines σ)))
    have hu := Finset.card_union_le prev.tests (Finset.univ.image (fun σ : Fin k → Bool => a.onLines (prev.maskLines σ)))
    simp only [tests]
    rw [pow_succ]
    omega

def Circuit.realizesMaskAt {n : ℕ} (b : Circuit n) (σ : Fin n → Bool) (x : ℝ) : Prop :=
  ∀ i, b.values x i = (b.maskLines σ i).value x

theorem Circuit.append_mask {n : ℕ} (b : Circuit n) (a : GateAffine n)
    (σ : Fin n → Bool) (x : ℝ) (h : b.realizesMaskAt σ x) (active : Bool)
    (he : max ((a.onLines (b.maskLines σ)).value x) 0 =
      (if active then a.onLines (b.maskLines σ) else Line.zero).value x) :
    (b.append a).realizesMaskAt (Fin.snoc (α:=fun _ => Bool) σ active) x := by
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [values,maskLines,Fin.snoc_last,Fin.init_snoc]
    have hv : b.values x = fun i => (b.maskLines σ i).value x := funext h
    rw [hv,a.eval_onLines]
    exact he
  | cast i =>
    simpa only [values,maskLines,Fin.snoc_castSucc,Fin.init_snoc] using h i

theorem Circuit.common_mask {n : ℕ} (b : Circuit n) {x y : ℝ}
    (ht : ∀ l ∈ b.tests, 0 ≤ l.value x ↔ 0 ≤ l.value y) :
    ∃ σ, b.realizesMaskAt σ x ∧ b.realizesMaskAt σ y := by
  induction b with
  | empty => exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | @append k prev a ih =>
    obtain ⟨σ,hx,hy⟩ := ih (fun l hl => ht l (Finset.mem_union_left _ hl))
    let l := a.onLines (prev.maskLines σ)
    have hs : 0 ≤ l.value x ↔ 0 ≤ l.value y := ht l
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ σ)))
    by_cases hp : 0 ≤ l.value x
    · exact ⟨Fin.snoc σ true,prev.append_mask a σ x hx true (max_eq_left hp),
        prev.append_mask a σ y hy true (max_eq_left (hs.mp hp))⟩
    · refine ⟨Fin.snoc σ false,prev.append_mask a σ x hx false ?_,prev.append_mask a σ y hy false ?_⟩
      · rw [max_eq_right (le_of_not_ge hp)]; simp [Line.zero,Line.value]
      · rw [max_eq_right (le_of_not_ge (mt hs.mpr hp))]; simp [Line.zero,Line.value]

noncomputable def Circuit.out {n : ℕ} (b : Circuit n) (a : GateAffine n) (x : ℝ) : ℝ :=
  a.eval x (b.values x)

theorem Circuit.out_on_mask {n : ℕ} (b : Circuit n) (a : GateAffine n)
    {σ : Fin n → Bool} {x : ℝ} (h : b.realizesMaskAt σ x) :
    b.out a x = (a.onLines (b.maskLines σ)).value x := by
  have hh : b.values x = fun i => (b.maskLines σ i).value x := funext h
  rw [out,hh,a.eval_onLines]

/-- The cut count is uniform in all real weights and counts shared gates once. -/
theorem Circuit.sign_cuts {n m : ℕ} (b : Circuit n) (c : Circuit m) (a : GateAffine n) (a' : GateAffine m) :
    ∃ s : Finset ℝ, s.card ≤ 2^n + 2^m + 2^n*2^m ∧
      ∀ x y, SameCell s x y → 0 ≤ (b.out a x - c.out a' x) * (b.out a y - c.out a' y) := by
  let l (σ : Fin n → Bool) := a.onLines (b.maskLines σ)
  let l' (τ : Fin m → Bool) := a'.onLines (c.maskLines τ)
  let diffs := Finset.image₂ (fun σ τ => (l σ).sub (l' τ)) Finset.univ Finset.univ
  let all := b.tests ∪ c.tests ∪ diffs
  refine ⟨all.image lineRoot,Finset.card_image_le.trans ?_,?_⟩
  · have hdiff : diffs.card ≤ 2^n * 2^m := by simpa [diffs] using
        (Finset.card_image₂_le (fun σ τ => (l σ).sub (l' τ)) Finset.univ Finset.univ)
    exact (Finset.card_union_le ..).trans (Nat.add_le_add ((Finset.card_union_le ..).trans
      (Nat.add_le_add ((Nat.le_succ _).trans b.card_tests) ((Nat.le_succ _).trans c.card_tests))) hdiff)
  · intro x y hxy
    obtain ⟨σ,hx,hy⟩ := b.common_mask (fun l hl => line_same_sign hxy l
      (Finset.mem_union_left _ (Finset.mem_union_left _ hl)))
    obtain ⟨τ,hx',hy'⟩ := c.common_mask (fun l hl => line_same_sign hxy l
      (Finset.mem_union_left _ (Finset.mem_union_right _ hl)))
    have hd := line_same_sign hxy ((l σ).sub (l' τ)) (Finset.mem_union_right _
      (Finset.mem_image₂_of_mem (Finset.mem_univ σ) (Finset.mem_univ τ)))
    have hval (z : ℝ) : ((l σ).sub (l' τ)).value z = (l σ).value z - (l' τ).value z := by
      simp [Line.value,Line.sub]; ring
    rw [hval,hval,←b.out_on_mask a hx,←c.out_on_mask a' hx',←b.out_on_mask a hy,←c.out_on_mask a' hy'] at hd
    by_cases h : 0 ≤ b.out a x - c.out a' x
    · exact mul_nonneg h (hd.mp h)
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h) (le_of_not_ge (mt hd.mpr h))

end ReluMoments
