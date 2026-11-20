module

public import SolvedProblems.ClosureSupportAtoms
import Mathlib.GroupTheory.Perm.Cycle.Basic

public section

namespace ClosureSupport

open Equiv

/-- Pick an origin on each cycle and reflect the integer coordinate about it. The
reflection is independent of the coordinate even on a finite cycle. -/
private theorem cycle_reflection (p : Perm ℕ) :
    ∃ r : Perm ℕ, (∀ x, r (r x) = x) ∧ (∀ x, r (p x) = p.symm (r x)) ∧
      ∀ x, p.SameCycle x (r x) := by
  classical
  let cls (x : ℕ) := Quotient.mk (Perm.SameCycle.setoid p) x
  let base (x : ℕ) := (cls x).out
  have repr (x : ℕ) : p.SameCycle (base x) x := Quotient.exact (cls x).out_eq
  let idx (x : ℕ) := (repr x).choose
  have atIdx (x : ℕ) : (p ^ idx x) (base x) = x := (repr x).choose_spec
  have origin {x y : ℕ} (h : p.SameCycle x y) : base x = base y :=
    congrArg Quotient.out (show cls x = cls y from Quotient.sound h)
  let rev (x : ℕ) := (p ^ (-idx x)) (base x)
  have atNeg (x : ℕ) (j : ℤ) : rev ((p^j) (base x)) = (p^(-j)) (base x) := by
    let y := (p^j) (base x)
    have common : base y = base x := (origin ((repr x).symm.trans ⟨j,rfl⟩)).symm
    have h := atIdx y
    rw [common] at h
    change (p ^ idx y) (base x) = (p ^ j) (base x) at h
    have eq := congrArg (fun t : ℕ => (p ^ (-idx y-j)) t) h
    change (p ^ (-idx y)) (base y) = _
    rw [common]
    simpa only [← Perm.mul_apply, ← zpow_add, sub_add_cancel,
      show -idx y-j+idx y = -j by omega] using eq.symm
  have inv (x : ℕ) : rev (rev x) = x := by
    calc
      rev (rev x) = (p ^ (-(-idx x))) (base x) := atNeg x (-idx x)
      _ = x := by simpa using atIdx x
  let r : Perm ℕ := ⟨rev,rev,inv,inv⟩
  refine ⟨r, inv, fun x => ?_, fun x => (repr x).symm.trans ⟨-idx x,rfl⟩⟩
  change rev (p x) = p.symm ((p ^ (-idx x)) (base x))
  have step : p x = (p ^ (1 + idx x)) (base x) := by simp [zpow_add, atIdx]
  rw [step, atNeg]
  change (p ^ (-(1+idx x))) (base x) = (p⁻¹ * p ^ (-idx x)) (base x)
  rw [show -(1+idx x) = -1 + (-idx x) by omega, zpow_add, zpow_neg_one]

theorem factors (P : Support) (p : stabilizer P) :
    ∃ a b : stabilizer P, a*a = 1 ∧ b*b = 1 ∧ p = a*b := by
  obtain ⟨r,hinv,conj,orb⟩ := cycle_reflection p.val
  have hr : r ∈ stabilizer P := by
    intro S hs x
    obtain ⟨i,hi⟩ := orb x
    rw [← hi]
    exact (show Fixes P (p.val ^ i) from (stabilizer P).zpow_mem p.property i) S hs x
  let b : stabilizer P := ⟨r,hr⟩
  refine ⟨p*b,b,?_,?_,?_⟩
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    change p.val (r (p.val (r x))) = x
    rw [conj, hinv, Equiv.apply_symm_apply]
  · apply Subtype.ext
    exact Equiv.ext hinv
  · apply Subtype.ext
    exact Equiv.ext fun x => by change p.val x = p.val (r (r x)); rw [hinv]

end ClosureSupport
