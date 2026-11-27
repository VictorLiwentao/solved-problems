module

public import SolvedProblems.PrivateListGridModel
import SolvedProblems.PrivateListRamsey
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

namespace PrivateList

open Set MeasureTheory
open scoped Classical

noncomputable def bucket (D : ℕ) (x : ℝ) : Fin (D+1) :=
  ⟨min D ⌊D*x⌋₊,Nat.lt_succ_of_le (min_le_left ..)⟩

theorem bucket_accuracy {D : ℕ} (hD : 0 < D) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    |x - ((bucket D x).val : ℝ)/D| ≤ 1/D := by
  have pos : (0:ℝ) < D := by exact_mod_cast hD
  have lower : (⌊(D:ℝ)*x⌋₊ : ℝ) ≤ D*x := Nat.floor_le (mul_nonneg pos.le hx)
  have upper := Nat.lt_floor_add_one ((D:ℝ)*x)
  have cap : ⌊(D:ℝ)*x⌋₊ ≤ D := by
    exact_mod_cast lower.trans (by nlinarith : (D:ℝ)*x ≤ D)
  change |x - (min D ⌊(D:ℝ)*x⌋₊ : ℕ)/ (D:ℝ)| ≤ _
  rw [min_eq_right cap, abs_of_nonneg (by apply sub_nonneg.mpr; apply (div_le_iff₀ pos).mpr; linarith)]
  apply (le_div_iff₀ pos).mpr
  rw [sub_mul,div_mul_cancel₀ _ pos.ne']
  linarith

theorem order_image {l : ℕ} (g : Fin l ↪o ℕ) :
    let S := Finset.univ.image g
    ∃ h : S.card = l, S.orderEmbOfFin h = g := by
  let S := Finset.univ.image g
  have h : S.card = l := by simp [S,Finset.card_image_of_injective _ g.injective]
  refine ⟨h,?_⟩
  ext i
  exact congrFun (Finset.orderEmbOfFin_unique h (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i))
    g.strictMono).symm i

/-- Rank cells can be made simultaneously homogeneous to a prescribed mesh on
arbitrarily long independent axes. -/
theorem homogeneousRanks {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (T : Template k m)
    (L D : ℕ) (hD : 0 < D) :
    ∃ X Y : Fin L ↪o ℕ, ∃ v : Cell m → Label k → ℝ,
      (∀ i y, 0 ≤ v i y ∧ v i y ≤ 1) ∧
      ∀ a b : Fin (m+1) ↪o Fin L, ∀ i y,
        |lookup A T (fun n => X (a n)) (fun n => Y (b n)) i y - v i y| ≤ 1/D := by
  classical
  let color (S U : Finset ℕ) : Cell m → Label k → Fin (D+1) := fun i y =>
    if hS : S.card=m+1 then if hU : U.card=m+1 then
      bucket D (lookup A T (S.orderEmbOfFin hS) (U.orderEmbOfFin hU) i y) else 0 else 0
  obtain ⟨S,U,hS,hU,c,mono⟩ := rectangle color (m+1) L
  let X := S.orderEmbOfFin hS
  let Y := U.orderEmbOfFin hU
  have pos : (0:ℝ) < D := by exact_mod_cast hD
  refine ⟨X,Y,fun i y => ((c i y).val : ℝ)/D,?_,?_⟩
  · intro i y
    exact ⟨div_nonneg (Nat.cast_nonneg _) pos.le, (div_le_one pos).mpr (by exact_mod_cast Nat.le_of_lt_succ (c i y).isLt)⟩
  intro a b i y
  let f := a.trans X
  let g := b.trans Y
  let R := Finset.univ.image f
  let V := Finset.univ.image g
  have rs : R ⊆ S := by rintro _ h; obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h; exact S.orderEmbOfFin_mem hS _
  have vs : V ⊆ U := by rintro _ h; obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h; exact U.orderEmbOfFin_mem hU _
  obtain ⟨fr,ef⟩ := order_image f
  obtain ⟨gr,eg⟩ := order_image g
  change R.card = m+1 at fr
  change V.card = m+1 at gr
  change R.orderEmbOfFin fr = f at ef
  change V.orderEmbOfFin gr = g at eg
  have eq := congrFun (congrFun (mono R rs fr V vs gr) i) y
  simp only [color,dite_eq_left fr,dite_eq_left gr,ef,eg] at eq
  have law (s : Sample k m) := A.normalized s
  have pos' : 0 ≤ lookup A T f g i y := measureReal_nonneg
  have neg' : lookup A T f g i y ≤ 1 := by
    unfold lookup omission
    apply measureReal_le_one
  have est := bucket_accuracy hD pos' neg'
  rw [eq] at est
  exact est

end PrivateList
