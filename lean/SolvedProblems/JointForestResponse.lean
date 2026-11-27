module

public import SolvedProblems.JointForestCurrent
public import SolvedProblems.JointForestSheets
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace JointForest

open SimpleGraph Matrix

attribute [local instance] Classical.propDecidable

/-- The two real (here rational-valued) characters of the deck involution use
the sheet factors +1 and −1. -/
def polarity (b : Bool) : ℚ := if b then -1 else 1

@[simp] theorem polarity_false : polarity false = 1 := rfl
@[simp] theorem polarity_true : polarity true = -1 := rfl

@[simp] theorem polarity_square (b : Bool) : polarity b * polarity b = 1 := by cases b <;> norm_num [polarity]

theorem polarity_xor (a b : Bool) : polarity (a ^^ b) = polarity a * polarity b := by
  cases a <;> cases b <;> norm_num [polarity]

/-- The grounded, signed base operator is the identity plus the signed Laplacian. -/
noncomputable def signedShift {V : Type*} [Fintype V] (B : SimpleGraph V) (s : Signing V) (p : V → ℚ) (x : V) : ℚ :=
  p x + ∑ y, if B.Adj x y then p x - polarity (s.neg x y) * p y else 0

theorem max_principle {V : Type*} [Fintype V] (B : SimpleGraph V) (p : V → ℚ)
    (h : ∀ x, p x + current B p x = 0) (x : V) : p x ≤ 0 := by
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ p ⟨x, Finset.mem_univ x⟩
  have hc : 0 ≤ current B p v := by
    apply Finset.sum_nonneg
    intro y _
    split <;> first | exact sub_nonneg.mpr (hv y (Finset.mem_univ y)) | rfl
  linarith [h v, hv x (Finset.mem_univ x)]

/-- Every finite unsigned base graph has a grounded response. The maximum
principle gives injectivity even when the base is disconnected. -/
theorem unsigned_green_exists {V : Type*} [Fintype V] (B : SimpleGraph V) :
    ∃ P : V → V → ℚ, ∀ s x, P s x + current B (P s) x = pulse x s := by
  classical
  let L : (V → ℚ) →ₗ[ℚ] (V → ℚ) := LinearMap.id + (B.lapMatrix ℚ).mulVecLin
  have hL (p : V → ℚ) (x : V) : L p x = p x + current B p x := by
    change p x + ((B.lapMatrix ℚ) *ᵥ p) x = _
    rw [lap_current]
  have hinj : Function.Injective L := by
    intro p q h
    funext x
    have hsub (p q : V → ℚ) (h : L p = L q) (x : V) : p x - q x ≤ 0 := by
      apply max_principle B (fun y => p y - q y) _ x
      intro y
      rw [current_sub]
      have he := congrFun h y
      rw [hL, hL] at he
      linarith
    linarith [hsub p q h x, hsub q p h.symm x]
  have hsur := LinearMap.surjective_of_injective hinj
  choose P hp using (fun s : V => hsur (fun x => pulse x s))
  exact ⟨P, fun s x => (hL _ _).symm.trans (congrFun (hp s) x)⟩

def sheetGreen {V : Type*} (P Q : V → V → ℚ) (a x : V × Bool) : ℚ :=
  (P a.1 x.1 + polarity a.2 * polarity x.2 * Q a.1 x.1) / 2

theorem current_pair {V : Type*} [Fintype V] (B : SimpleGraph V) (s : Signing V)
    (P Q : V → V → ℚ) (a x : V × Bool) :
    sheetGreen P Q a x + current (signedLift B s) (sheetGreen P Q a) x =
      ((P a.1 x.1 + current B (P a.1) x.1) + polarity a.2 * polarity x.2 * signedShift B s (Q a.1) x.1) / 2 := by
  classical
  obtain ⟨x,xe⟩ := x
  obtain ⟨a,ae⟩ := a
  have row (y : V) : (∑ e : Bool, if (signedLift B s).Adj (x,xe) (y,e)
      then sheetGreen P Q (a,ae) (x,xe) - sheetGreen P Q (a,ae) (y,e) else 0) =
    ((if B.Adj x y then P a x - P a y else 0) + polarity ae * polarity xe *
      (if B.Adj x y then Q a x - polarity (s.neg x y) * Q a y else 0)) / 2 := by
    rw [Fintype.sum_bool]
    cases ae <;> cases xe <;> cases h : s.neg x y <;> by_cases he : B.Adj x y <;>
      simp [signedLift, sheetGreen, h, he] <;> ring
  unfold current signedShift
  rw [Fintype.sum_prod_type]
  simp only [row, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold sheetGreen
  dsimp only
  ring

theorem sheetGreen_solve {V : Type*} [Fintype V] (B : SimpleGraph V) (s : Signing V)
    (P Q : V → V → ℚ) (hP : ∀ a x, P a x + current B (P a) x = pulse x a)
    (hQ : ∀ a x, signedShift B s (Q a) x = pulse x a) (a x : V × Bool) :
    sheetGreen P Q a x + current (signedLift B s) (sheetGreen P Q a) x = pulse x a := by
  rw [current_pair, hP, hQ]
  obtain ⟨a,ae⟩ := a
  obtain ⟨x,xe⟩ := x
  cases ae <;> cases xe <;> by_cases h : x = a <;> simp [pulse, h]

end JointForest
