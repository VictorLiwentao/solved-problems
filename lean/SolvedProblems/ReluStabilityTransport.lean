module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

open Set Filter
open scoped Topology

namespace ReluStability

/-- Clamp a value to the closed interval between two possibly unordered endpoints. -/
def middle (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

theorem middle_left (a b : ℝ) : middle a b a = a := by
  unfold middle
  rcases le_total a b with h|h <;> simp [h]

theorem middle_right (a b : ℝ) : middle a b b = b := by
  unfold middle
  rcases le_total a b with h|h <;> simp [h]

theorem middle_self (a c : ℝ) : middle a a c = a := by simp [middle]

theorem middle_bounds (a b c : ℝ) :
    min a b ≤ middle a b c ∧ middle a b c ≤ max a b :=
  ⟨le_max_left ..,max_le ((min_le_left ..).trans (le_max_left ..)) (min_le_left ..)⟩

theorem middle_abs (a b c : ℝ) : |middle a b c - a| ≤ |b-a| := by
  obtain ⟨hl,hr⟩ := middle_bounds a b c
  rcases le_total a b with h|h <;> simp [h] at hl hr <;> rw [abs_le] <;> simp [abs_of_nonneg,abs_of_nonpos,h] <;> constructor <;> linarith

theorem middle_strict {a b c d e f : ℝ} (hab : a < b) (hcd : c < d) (hef : e < f) :
    middle a c e < middle b d f := by
  unfold middle
  exact max_lt_max (min_lt_min hab hcd) (min_lt_min (max_lt_max hab hcd) hef)

theorem middle_continuous {B : Type*} [TopologicalSpace B] {a b c : B → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous fun t => middle (a t) (b t) (c t) :=
  (ha.min hb).max ((ha.max hb).min hc)

/-- A moving root keeps the same strict order and equalities with a fixed root. -/
def SameSide (t u s : ℝ) : Prop := (t<s ↔ u<s) ∧ (t=s ↔ u=s)

noncomputable def oneMove (t u s z : ℝ) : ℝ :=
  middle z (z+(u-t)) (s + ((u-s)/(t-s))*(z-s))

theorem oneMove_start (t u s : ℝ) (h : SameSide t u s) : oneMove t u s t = u := by
  by_cases he : t = s
  · have he' := h.2.mp he
    subst s; subst u; simp [oneMove,middle]
  rw [oneMove,div_mul_cancel₀ _ (sub_ne_zero.mpr he)]
  rw [show s+(u-s)=u by ring,show t+(u-t)=u by ring,middle_right]

theorem oneMove_fixed (t u s : ℝ) : oneMove t u s s = s := by simp [oneMove,middle_left]

theorem oneMove_abs (t u s z : ℝ) : |oneMove t u s z-z| ≤ |u-t| := by
  simpa [oneMove] using middle_abs z (z+(u-t)) (s+((u-s)/(t-s))*(z-s))

theorem oneMove_mono {t u s : ℝ} (h : SameSide t u s) : StrictMono (oneMove t u s) := by
  by_cases he : t=s
  · have he' := h.2.mp he
    subst s; subst u
    intro a b hlt
    simpa [oneMove,middle_self] using hlt
  have hu : u ≠ s := mt h.2.mpr he
  have hp : 0 < (u-s)/(t-s) := by
    rcases lt_or_gt_of_ne he with hl|hr
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (h.1.mp hl)) (sub_neg.mpr hl)
    · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt (mt h.1.mpr hr.not_gt)) hu.symm)) (sub_pos.mpr hr)
  intro a b hab
  exact middle_strict hab (by linarith) (by nlinarith only [mul_pos hp (sub_pos.mpr hab)])

theorem oneMove_continuous {B : Type*} [TopologicalSpace B] {t u s z : B → ℝ}
    (ht : Continuous t) (hu : Continuous u) (hs : Continuous s) (hz : Continuous z)
    (h : ∀ b, SameSide (t b) (u b) (s b)) :
    Continuous fun b => oneMove (t b) (u b) (s b) (z b) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  by_cases he : t b = s b
  · have hu' : u b - t b = 0 := sub_eq_zero.mpr ((h b).2.mp he |>.trans he.symm)
    have hlim : Tendsto (fun v => oneMove (t v) (u v) (s v) (z v) - z v) (𝓝 b) (𝓝 0) := by
      apply squeeze_zero_norm (fun v => oneMove_abs ..)
      simpa [hu'] using ((hu.sub ht).abs.continuousAt (x:=b)).tendsto
    have hv : oneMove (t b) (u b) (s b) (z b) = z b := by simp [oneMove,hu',middle_self]
    rw [ContinuousAt,hv]
    simpa only [sub_add_cancel,zero_add] using hlim.add (hz.continuousAt (x:=b)).tendsto
  · apply ((hz.continuousAt.min (hz.add (hu.sub ht)).continuousAt).max
      ((hz.continuousAt.max (hz.add (hu.sub ht)).continuousAt).min ?_))
    exact hs.continuousAt.add (((hu.sub hs).continuousAt.div (ht.sub hs).continuousAt (sub_ne_zero.mpr he)).mul (hz.sub hs).continuousAt)

end ReluStability
