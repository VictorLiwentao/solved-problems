module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

public section

namespace ClosureSupport

open Polynomial

private theorem quadratic_root {K : Type*} [Field K] [IsAlgClosed K] (a : K) :
    ∃ z : K, z^2 + z = a := by
  let q : K[X] := C 1 * X^2 + C 1 * X + C (-a)
  have hd : q.degree = 2 := degree_quadratic one_ne_zero
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root q (by rw [hd]; decide)
  refine ⟨z, ?_⟩
  simpa [q, IsRoot.def, sub_eq_add_neg, ← eq_neg_iff_add_eq_zero] using hz

/-- In characteristic two, a nontrivial involution would interchange the roots u, u+1
of a quadratic but also force that quadratic to have a fixed root. -/
private theorem characteristic_two {K : Type*} [Field K] [IsAlgClosed K]
    (σ : K ≃+* K) (inv : ∀ x, σ (σ x) = x) (two : (2 : K) = 0) (x : K) : σ x = x := by
  by_contra moved
  -- Dividing the moved element by its nonzero trace makes the involution translate it by one.
  let d := σ x + x
  have hd : d ≠ 0 := by
    intro zero
    apply moved
    change σ x + x = 0 at zero
    linear_combination zero - x * two
  have fixed : σ d = d := by simp [d,inv,add_comm]
  let u := x / d
  have shift : σ u = u + 1 := by
    change σ (x / d) = x / d + 1
    rw [map_div₀, fixed]
    field_simp
    dsimp [d]
    linear_combination -x * two
  obtain ⟨z,hz⟩ := quadratic_root (u^3 + u)
  -- This trace is fixed; the cubic forces it to be either u or u+1, which are interchanged.
  let y := σ z + z
  have fy : σ y = y := by simp [y,inv,add_comm]
  have transformed := congrArg σ hz
  simp only [map_add, map_pow, shift] at transformed
  have hy : y^2 + y = u^2 + u := by
    dsimp [y]
    linear_combination transformed + hz + (σ z * z + u^3 + u^2 + 2*u + 1) * two
  have factor : (y-u)*(y-(u+1)) = 0 := by
    linear_combination hy + (u^2 + u - y*u - y) * two
  rcases mul_eq_zero.mp factor with a | b
  · have eq := sub_eq_zero.mp a
    rw [eq,shift] at fy
    exact (one_ne_zero : (1:K) ≠ 0) (by linear_combination fy)
  · have eq := sub_eq_zero.mp b
    rw [eq,map_add,map_one,shift] at fy
    exact (one_ne_zero : (1:K) ≠ 0) (by linear_combination fy)

/-- An involution of an algebraically closed field fixing a square root of -1 fixes every point. -/
theorem fixed_by_involution {K : Type*} [Field K] [IsAlgClosed K]
    (σ : K ≃+* K) (inv : ∀ x, σ (σ x) = x) (i : K) (hi : i^2 = -1) (fix : σ i = i)
    (x : K) : σ x = x := by
  by_cases two : (2 : K) = 0
  · exact characteristic_two σ inv two x
  by_contra moved
  -- The involution negates this nonzero difference. Its square roots are sent to ±i times themselves.
  let y := σ x - x
  have hy : y ≠ 0 := sub_ne_zero.mpr moved
  have flipped : σ y = -y := by simp [y,inv]
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq y (by decide : 0 < 2)
  have sz : (σ z)^2 = -z^2 := by rw [← map_pow, hz, flipped]
  have factor : (σ z - i*z)*(σ z + i*z) = 0 := by
    linear_combination sz - z^2 * hi
  have impossible : z = -z := by
    rcases mul_eq_zero.mp factor with a | b
    · have e := sub_eq_zero.mp a
      have h := congrArg σ e
      rw [inv,map_mul,fix,e] at h
      linear_combination h + z * hi
    · have e : σ z = -(i*z) := eq_neg_iff_add_eq_zero.mpr b
      have h := congrArg σ e
      rw [inv,map_neg,map_mul,fix,e] at h
      linear_combination h + z * hi
  have zero : (2:K)*z = 0 := by linear_combination impossible
  exact hy (by rw [← hz, (mul_eq_zero.mp zero).resolve_left two]; simp)

end ClosureSupport
