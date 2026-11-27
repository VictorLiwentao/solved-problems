module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Sum

public section

namespace ProjectiveSupports

open Function

/-- In a finite transitive action, some translate of `X` misses `S` whenever
`|X| |S|` is smaller than the underlying set. Count the equal-size fibres of
the evaluation map; a group consisting entirely of bad translates would
inject into the fibres indexed by pairs in `X × S`. -/
theorem translate_avoids (H R : Type*) [Group H] [MulAction H R] [MulAction.IsPretransitive H R]
    [Fintype H] [Fintype R] (X S : Finset R) (bound : X.card * S.card < Fintype.card R) :
    ∃ h : H, ∀ x ∈ X, h • x ∉ S := by
  classical
  have pos : 0 < Fintype.card R := (Nat.zero_le _).trans_lt bound
  let := Fintype.card_pos_iff.mp pos
  let base : R := Classical.choice (inferInstance : Nonempty R)
  let fiber (x y : R) := {h : H // h • x = y}
  let m := Fintype.card (fiber base base)
  have eqCard (x y z : R) : Fintype.card (fiber x y) = Fintype.card (fiber x z) := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H y z
    apply Fintype.card_congr
    exact {
      toFun := fun h => ⟨g * h.val,by rw [mul_smul,h.property,hg]⟩
      invFun := fun h => ⟨g⁻¹ * h.val,by rw [mul_smul,h.property,← hg,inv_smul_smul]⟩
      left_inv := fun h => Subtype.ext (inv_mul_cancel_left _ _)
      right_inv := fun h => Subtype.ext (mul_inv_cancel_left _ _) }
  have total (x : R) : Fintype.card H = Fintype.card R * Fintype.card (fiber x base) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv fun g : H => g • x), Fintype.card_sigma]
    change ∑ y : R, Fintype.card (fiber x y) = _
    simp [fun y => eqCard x y base]
  have fiberSize (x y : R) : Fintype.card (fiber x y) = m :=
    (eqCard x y base).trans (Nat.eq_of_mul_eq_mul_left pos ((total x).symm.trans (total base)))
  by_contra! bad
  choose hit hx meets using bad
  let hitPair (g : H) : X × S := (⟨hit g,hx g⟩,⟨g • hit g,meets g⟩)
  let cert (g : H) : Σ p : X × S, fiber p.1.val p.2.val := ⟨hitPair g,⟨g,rfl⟩⟩
  have inj : Injective cert := fun a b h => congrArg (fun z : Σ p : X × S, fiber p.1.val p.2.val => z.2.val) h
  have card := Fintype.card_le_of_injective cert inj
  rw [Fintype.card_sigma] at card
  have count : Fintype.card H ≤ (X.card * S.card) * m := by simpa [fiberSize] using card
  have nonzero : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨1,one_smul _ _⟩⟩
  exact (Nat.mul_lt_mul_of_pos_right bound nonzero).not_ge ((total base) ▸ count)

end ProjectiveSupports
