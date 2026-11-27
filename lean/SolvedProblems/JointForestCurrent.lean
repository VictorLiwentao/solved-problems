module

public import SolvedProblems.JointForestCone
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace JointForest

open SimpleGraph Matrix

attribute [local instance] Classical.propDecidable

/-- Net current leaving a vertex in the unit-resistor graph. -/
noncomputable def current {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) (x : V) : ℚ :=
  ∑ y, if G.Adj x y then p x - p y else 0

noncomputable def pulse {V : Type*} (x a : V) : ℚ := if x = a then 1 else 0

theorem lap_current {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) (x : V) :
    ((G.lapMatrix ℚ) *ᵥ p) x = current G p x := by
  rw [G.lapMatrix_mulVec_apply', G.neighborFinset_eq_filter, Finset.sum_filter]
  rfl

theorem current_sub {V : Type*} [Fintype V] (G : SimpleGraph V) (p q : V → ℚ) (x : V) :
    current G (fun y => p y - q y) x = current G p x - current G q x := by
  rw [← lap_current, ← lap_current, ← lap_current]
  exact congrFun (Matrix.mulVec_sub (G.lapMatrix ℚ) p q) x

theorem current_offset {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) (c : ℚ) (x : V) :
    current G (fun y => p y - c) x = current G p x := by
  simp [current, sub_sub_sub_cancel_right]

theorem current_zero {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) :
    current G (fun _ => 0) x = 0 := by simp [current]

theorem current_sum {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V → ℚ) :
    ∑ x, current G p x = 0 := by
  let z (x y : V) : ℚ := if G.Adj x y then p x - p y else 0
  have h (x y : V) : z y x = -z x y := by
    dsimp [z]
    rw [G.adj_comm y]
    split <;> ring
  have e : (∑ x, ∑ y, z x y) = -(∑ x, ∑ y, z x y) := by
    calc _ = ∑ x, ∑ y, z y x := Finset.sum_comm
         _ = ∑ x, ∑ y, -(z x y) := by apply Finset.sum_congr rfl; intro x _; exact Finset.sum_congr rfl (fun _ _ => h ..)
         _ = _ := by simp
  change (∑ x, ∑ y, z x y) = 0
  linarith

/-- A full set of unit-current responses gives a right inverse to the grounded
Laplacian at `b`. Thus the computed voltage drop is the resistance defined by
the matrix inverse, independent of the arbitrary additive voltage constants. -/
theorem resistance_of_responses {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V)
    (P : V → V → ℚ) (hP : ∀ s x, x ≠ b → current G (P s) x = pulse x s) :
    resistance G a b = P a a - P a b := by
  classical
  by_cases hab : a = b
  · subst a; simp [resistance]
  let A : Matrix {x // x ≠ b} {x // x ≠ b} ℚ := (G.lapMatrix ℚ).submatrix Subtype.val Subtype.val
  let B : Matrix {x // x ≠ b} {x // x ≠ b} ℚ := fun i j => P j.val i.val - P j.val b
  have hAB : A * B = 1 := by
    ext i j
    have h0 := hP j.val i.val i.property
    rw [← current_offset G (P j.val) (P j.val b), ← lap_current] at h0
    change ∑ x : V, (G.lapMatrix ℚ) i.val x * (P j.val x - P j.val b) = _ at h0
    rw [Fintype.sum_eq_add_sum_subtype_ne _ b] at h0
    simp only [sub_self, mul_zero, zero_add] at h0
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [A, B, Matrix.submatrix_apply, pulse, Subtype.ext_iff] using h0
  have h := Matrix.inv_eq_right_inv hAB
  rw [resistance, dite_eq_right hab]
  exact congrArg (fun M : Matrix {x // x ≠ b} {x // x ≠ b} ℚ => M ⟨a,hab⟩ ⟨a,hab⟩) h

/-- Every column may share an arbitrary common return-current distribution.
Subtract its `b`-column to drive a unit of current from `a` to `b`. -/
theorem resistance_of_green {V : Type*} [Fintype V] (G : SimpleGraph V) (P : V → V → ℚ)
    (sink : V → ℚ) (hP : ∀ s x, current G (P s) x = pulse x s - sink x) (a b : V) :
    resistance G a b = (P a a - P b a) - (P a b - P b b) := by
  apply resistance_of_responses G a b (fun s x => P s x - P b x)
  intro s x hx
  rw [current_sub, hP, hP]
  simp [pulse, hx]

/-- Ground the cone apex at zero. -/
def coneGreen {V : Type*} (C : V → V → ℚ) : Option V → Option V → ℚ
  | some a, some b => C a b
  | _, _ => 0

theorem rim_current {V : Type*} [Fintype V] (A : SimpleGraph V) (p : V → ℚ) (x : V) :
    current (cone A) (Option.elim' 0 p) (some x) = p x + current A p x := by
  rw [current, Fintype.sum_option]
  simp only [cone, Option.elim'_none, Option.elim'_some, ite_true, sub_zero]
  rfl

/-- Full cone resistance from any solution to its grounded rim equation.
The apex equation follows by conservation of current. -/
theorem cone_resistance_of_green {V : Type*} [Fintype V] (A : SimpleGraph V) (C : V → V → ℚ)
    (hC : ∀ s x, C s x + current A (C s) x = pulse x s) (a b : Option V) :
    resistance (cone A) a b = (coneGreen C a a - coneGreen C b a) - (coneGreen C a b - coneGreen C b b) := by
  apply resistance_of_green (cone A) (coneGreen C) (fun x => pulse x none)
  intro s x
  cases s with
  | none =>
    change current (cone A) (fun z => coneGreen C none z) x = _
    have h : coneGreen C none = (fun _ => 0) := by funext z; cases z <;> rfl
    rw [h, current_zero, sub_self]
  | some s =>
    have he (y : V) : current (cone A) (coneGreen C (some s)) (some y) = pulse y s := by
      have h : coneGreen C (some s) = Option.elim' 0 (C s) := by funext z; cases z <;> rfl
      rw [h, rim_current, hC]
    cases x with
    | some y => simpa [pulse] using he y
    | none =>
      have h := current_sum (cone A) (coneGreen C (some s))
      rw [Fintype.sum_option] at h
      simp only [he, pulse, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
      simp [pulse]; linarith

end JointForest
