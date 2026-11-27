module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Topology.InductiveDimension.Functions

@[expose] public section

/-! Constructive generic stability of the full ternary activation complex. -/

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

open Set Filter
open scoped Topology

namespace ReluStability

noncomputable def move (t u : ℝ) : List ℝ → ℝ → ℝ
  | [], z => z + (u-t)
  | s :: ss, z => middle (move t u ss z) (oneMove t u s z) z

theorem move_abs (t u : ℝ) (ss : List ℝ) (z : ℝ) : |move t u ss z - z| ≤ |u-t| := by
  induction ss with
  | nil => simp [move]
  | cons s ss ih =>
    obtain ⟨hl,hr⟩ := middle_bounds (move t u ss z) (oneMove t u s z) z
    obtain ⟨ha,hb⟩ := abs_le.mp ih
    obtain ⟨hc,hd⟩ := abs_le.mp (oneMove_abs t u s z)
    apply abs_le.mpr
    change min _ _ ≤ move t u (s::ss) z at hl
    change move t u (s::ss) z ≤ max _ _ at hr
    constructor
    · have := (le_min (show z-|u-t| ≤ move t u ss z by linarith) (by linarith : z-|u-t| ≤ oneMove t u s z)).trans hl
      linarith
    · have := hr.trans (max_le (show move t u ss z ≤ z+|u-t| by linarith) (by linarith : oneMove t u s z ≤ z+|u-t|))
      linarith

theorem move_start (t u : ℝ) (ss : List ℝ) (h : ∀ s ∈ ss, SameSide t u s) : move t u ss t = u := by
  induction ss with
  | nil => simp [move]
  | cons s ss ih => rw [move,ih (fun l hl => h l (List.mem_cons_of_mem _ hl)),oneMove_start _ _ _ (h s (by simp)),middle_self]

theorem move_fixed (t u : ℝ) (ss : List ℝ) {s : ℝ} (hs : s ∈ ss) : move t u ss s = s := by
  induction ss with
  | nil => simp at hs
  | cons k ks ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · rw [move,oneMove_fixed,middle_right]
    · rw [move,ih hs,middle_left]

theorem move_mono {t u : ℝ} (ss : List ℝ) (h : ∀ s ∈ ss, SameSide t u s) : StrictMono (move t u ss) := by
  induction ss with
  | nil => intro x y hxy; change x+(u-t) < y+(u-t); linarith
  | cons s ss ih =>
    intro a b hxy
    exact middle_strict
      (ih (fun l hl => h l (List.mem_cons_of_mem _ hl)) hxy)
      (oneMove_mono (h s (by simp)) hxy) hxy

theorem move_same (t : ℝ) (ss : List ℝ) (z : ℝ) : move t t ss z = z := by
  have h := move_abs t t ss z
  simpa only [sub_self,abs_zero,abs_nonpos_iff,sub_eq_zero] using h

theorem move_continuous {B : Type*} [TopologicalSpace B] {t u z : B → ℝ} (ss : List (B → ℝ))
    (ht : Continuous t) (hu : Continuous u) (hz : Continuous z)
    (hs : ∀ s ∈ ss, Continuous s) (h : ∀ b s, s ∈ ss → SameSide (t b) (u b) (s b)) :
    Continuous fun b => move (t b) (u b) (ss.map (fun s => s b)) (z b) := by
  induction ss with
  | nil => exact hz.add (hu.sub ht)
  | cons s ss ih =>
    exact middle_continuous
      (ih (fun k hk => hs k (List.mem_cons_of_mem _ hk)) (fun b k hk => h b k (List.mem_cons_of_mem _ hk)))
      (oneMove_continuous ht hu (hs s (by simp)) hz (fun b => h b s (by simp))) hz

theorem move_surjective {t u : ℝ} (ss : List ℝ) (h : ∀ s ∈ ss, SameSide t u s) : Function.Surjective (move t u ss) := by
  have hc : Continuous (move t u ss) := by
    have hh := move_continuous (ss.map fun s => fun _ : ℝ => s) (t:=fun _ => t) (u:=fun _ => u) (z:=id)
      continuous_const continuous_const continuous_id (by simp only [List.mem_map,forall_exists_index,and_imp]; rintro _ s _ rfl; exact continuous_const) (by simpa using fun (_ : ℝ) => h)
    simpa [List.map_map,Function.comp_def] using hh
  intro y
  let low := y-|u-t|
  let high := y+|u-t|
  have h₁ := (abs_le.mp (move_abs t u ss low)).2
  have h₂ := (abs_le.mp (move_abs t u ss high)).1
  have hl : move t u ss low ≤ y := by dsimp [low] at *; linarith
  have hr : y ≤ move t u ss high := by dsimp [high] at *; linarith
  exact intermediate_value_univ low high hc ⟨hl,hr⟩

/-- Simultaneous transport of any finite set of real landmarks, allowing ties
that persist between the two configurations. The base space may itself contain
both parameters and lower-dimensional input coordinates. -/
theorem ordered_transport {B : Type*} [TopologicalSpace B] (xs : List ((B → ℝ) × (B → ℝ)))
    (hc : ∀ f ∈ xs, Continuous f.1 ∧ Continuous f.2)
    (ho : ∀ b, ∀ f ∈ xs, ∀ g ∈ xs, (f.1 b < g.1 b ↔ f.2 b < g.2 b) ∧ (f.1 b = g.1 b ↔ f.2 b = g.2 b)) :
    ∃ F : B → ℝ ≃o ℝ, Continuous (fun z : B×ℝ => F z.1 z.2) ∧
      (∀ b, ∀ f ∈ xs, F b (f.1 b) = f.2 b) ∧ (∀ b, (∀ f ∈ xs, f.1 b = f.2 b) → ∀ x, F b x = x) := by
  induction xs with
  | nil => exact ⟨fun _ => OrderIso.refl _,continuous_snd,by simp,by simp⟩
  | cons f xs ih =>
    have hin (g) (hg : g ∈ xs) := List.mem_cons_of_mem f hg
    obtain ⟨F,hF,hland,hid⟩ := ih (fun g hg => hc g (hin g hg)) (fun b g hg k hk => ho b g (hin _ hg) k (hin _ hk))
    let t := fun b => F b (f.1 b)
    let u := f.2
    let old := xs.map Prod.snd
    have same (b) (g) (hg : g ∈ xs) : SameSide (t b) (u b) (g.2 b) := by
      obtain ⟨hl,he⟩ := ho b f (by simp) g (hin _ hg)
      have hlt : t b < g.2 b ↔ f.1 b < g.1 b := by rw [←hland b g hg]; exact (F b).lt_iff_lt
      have heq : t b = g.2 b ↔ f.1 b = g.1 b := by rw [←hland b g hg]; exact (F b).injective.eq_iff
      exact ⟨hlt.trans hl,heq.trans he⟩
    have oldSide b : ∀ s ∈ old.map (fun s => s b), SameSide (t b) (u b) s := by
      simp only [old,List.map_map,List.mem_map,forall_exists_index,and_imp,Function.comp_apply]
      rintro _ g hg rfl
      exact same b g hg
    let G (b : B) : ℝ ≃o ℝ := (F b).trans
      ((move_mono _ (oldSide b)).orderIsoOfSurjective _ (move_surjective _ (oldSide b)))
    refine ⟨G,?_,?_,?_⟩
    · let Y := xs.map (fun g => fun z : B×ℝ => g.2 z.1)
      have ht : Continuous t := hF.comp (continuous_id.prodMk (hc f (by simp)).1)
      have hY : ∀ s ∈ Y, Continuous s := by
        simp only [Y,List.mem_map,forall_exists_index,and_imp]
        rintro _ g hg rfl
        exact (hc g (hin _ hg)).2.comp continuous_fst
      have hY' (z : B×ℝ) : ∀ s ∈ Y, SameSide (t z.1) (u z.1) (s z) := by
        simp only [Y,List.mem_map,forall_exists_index,and_imp]
        rintro _ g hg rfl
        exact same _ _ hg
      have HH := move_continuous Y (ht.comp continuous_fst) ((hc f (by simp)).2.comp continuous_fst) hF hY (fun z s hs => hY' z s hs)
      simpa only [G,OrderIso.trans_apply,StrictMono.coe_orderIsoOfSurjective,old,List.map_map,Y,Function.comp_def] using HH
    · intro b k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact move_start _ _ _ (oldSide b)
      · change move _ _ _ (F b (k.1 b)) = k.2 b
        rw [hland b k hk]
        exact move_fixed _ _ _ (List.mem_map.mpr ⟨k.2,List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩)
    · intro b h x
      have hh := hid b (fun g hg => h g (hin _ hg))
      change move (F b (f.1 b)) (f.2 b) _ (F b x) = x
      rw [hh,hh,h f (by simp),move_same]

end ReluStability

open Set

namespace ReluStability

abbrev Input (d : ℕ) := Fin d → ℝ

structure Family (B X : Type*) [TopologicalSpace B] [TopologicalSpace X] where
  map : B → X ≃ₜ X
  forward : Continuous (fun z : B×X => map z.1 z.2)
  backward : Continuous (fun z : B×X => (map z.1).symm z.2)

def Family.identity (B X : Type*) [TopologicalSpace B] [TopologicalSpace X] : Family B X :=
  ⟨fun _ => Homeomorph.refl _,continuous_snd,continuous_snd⟩

theorem inverse_continuous {B : Type*} [TopologicalSpace B] (G : B → ℝ ≃o ℝ)
    (hg : Continuous (fun z : B×ℝ => G z.1 z.2)) :
    Continuous (fun z : B×ℝ => (G z.1).symm z.2) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have hf : Continuous (fun z : B×ℝ => G z.1 a) := hg.comp (continuous_fst.prodMk continuous_const)
  constructor
  · convert isOpen_lt hf continuous_snd using 1
    ext z
    exact (G z.1).lt_symm_apply
  · convert isOpen_lt continuous_snd hf using 1
    ext z
    exact (G z.1).symm_apply_lt

theorem continuous_cons {B : Type*} [TopologicalSpace B] {d : ℕ} {f : B → ℝ} {g : B → Input d}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun z => Fin.cons (α:=fun _ => ℝ) (f z) (g z)) := by
  apply continuous_pi
  intro j
  induction j using Fin.cases with
  | zero => exact hf
  | succ i => exact (continuous_apply i).comp hg

theorem continuous_tail {d : ℕ} : Continuous (Fin.tail (α:=fun _ => ℝ) : Input (d+1) → Input d) :=
  continuous_pi fun i => continuous_apply i.succ

noncomputable def liftForward {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (b : B) (x : Input (d+1)) : Input (d+1) :=
  Fin.cons (G (b,Fin.tail x) (x 0)) (H.map b (Fin.tail x))

noncomputable def liftBackward {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (b : B) (x : Input (d+1)) : Input (d+1) :=
  let y := (H.map b).symm (Fin.tail x)
  Fin.cons ((G (b,y)).symm (x 0)) y

theorem liftForward_continuous {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (hG : Continuous (fun z : (B×Input d)×ℝ => G z.1 z.2)) :
    Continuous (fun z : B×Input (d+1) => liftForward H G z.1 z.2) := by
  have hy : Continuous (fun z : B×Input (d+1) => (z.1,Fin.tail z.2)) :=
    continuous_fst.prodMk (continuous_tail.comp continuous_snd)
  exact continuous_cons (hG.comp (hy.prodMk ((continuous_apply 0).comp continuous_snd))) (H.forward.comp hy)

theorem liftBackward_continuous {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (hG : Continuous (fun z : (B×Input d)×ℝ => G z.1 z.2)) :
    Continuous (fun z : B×Input (d+1) => liftBackward H G z.1 z.2) := by
  have hy : Continuous (fun z : B×Input (d+1) => (H.map z.1).symm (Fin.tail z.2)) :=
    H.backward.comp (continuous_fst.prodMk (continuous_tail.comp continuous_snd))
  exact continuous_cons ((inverse_continuous _ hG).comp ((continuous_fst.prodMk hy).prodMk
    ((continuous_apply 0).comp continuous_snd))) hy

noncomputable def Family.lift {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (hG : Continuous (fun z : (B×Input d)×ℝ => G z.1 z.2)) :
    Family B (Input (d+1)) where
  map b :=
    { toFun := liftForward H G b
      invFun := liftBackward H G b
      left_inv := fun x => by simp [liftForward,liftBackward]
      right_inv := fun x => by simp [liftForward,liftBackward]
      continuous_toFun := (liftForward_continuous H G hG).comp (continuous_const.prodMk continuous_id)
      continuous_invFun := (liftBackward_continuous H G hG).comp (continuous_const.prodMk continuous_id) }
  forward := liftForward_continuous H G hG
  backward := liftBackward_continuous H G hG

end ReluStability

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology

namespace ReluStability

abbrev Params (p : ℕ) := Fin p → ℝ
abbrev Coeff (p : ℕ) := MvPolynomial (Fin p) ℝ

/-- A proper real polynomial hypersurface has Lebesgue measure zero. This also
covers parameter dimension zero. -/
theorem ae_polynomial_ne {p : ℕ} (q : Coeff p) (hq : q ≠ 0) :
    ∀ᵐ x : Params p ∂volume, MvPolynomial.eval x q ≠ 0 := by
  induction p with
  | zero =>
    obtain ⟨r,hr⟩ := (MvPolynomial.isEmptyRingEquiv ℝ (Fin 0)).symm.surjective q
    rw [MvPolynomial.isEmptyRingEquiv_symm_apply] at hr
    subst q
    have hr' : r ≠ 0 := fun e => hq (e ▸ map_zero _)
    exact Eventually.of_forall fun x => by simpa using hr'
  | succ p ih =>
    let f := MvPolynomial.finSuccEquiv ℝ p q
    have hf : f ≠ 0 := by simpa [f] using hq
    obtain ⟨i,hi⟩ : ∃ i, f.coeff i ≠ 0 := by
      by_contra! hz
      apply hf
      apply Polynomial.ext
      intro i
      simpa using hz i
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p+1) => ℝ) 0
    have hm : MeasurableSet {u : ℝ × Params p | MvPolynomial.eval (Fin.cons (α:=fun _ => ℝ) u.1 u.2) q ≠ 0} := by
      have hc : Continuous fun u : ℝ × Params p => Fin.cons (α:=fun _ => ℝ) u.1 u.2 := by
        apply continuous_pi
        intro j
        induction j using Fin.cases with
        | zero => exact continuous_fst
        | succ i => exact (continuous_apply i).comp continuous_snd
      exact (isOpen_ne_fun (q.continuous_eval.comp hc) continuous_const).measurableSet
    have hp : ∀ᵐ u : ℝ × Params p ∂volume, MvPolynomial.eval (Fin.cons (α:=fun _ => ℝ) u.1 u.2) q ≠ 0 := by
      apply (ae_prod_iff_ae_ae hm).mpr
      apply (ae_ae_comm (p:=fun z x => MvPolynomial.eval (Fin.cons z x) q ≠ 0) hm).mpr
      filter_upwards [ih _ hi] with x hx
      have hmap : f.map (MvPolynomial.eval x) ≠ 0 := by
        intro he
        apply hx
        simpa using congrArg (fun t : Polynomial ℝ => t.coeff i) he
      have hfin := (Polynomial.finite_setOfPred_isRoot hmap).measure_zero (volume : Measure ℝ)
      rw [ae_iff]
      simpa only [MvPolynomial.eval_eq_eval_mv_eval',not_not,Polynomial.IsRoot,f] using hfin
    have hall := (volume_preserving_piFinSuccAbove (fun _ : Fin (p+1) => ℝ) 0).quasiMeasurePreserving.ae hp
    filter_upwards [hall] with x hx
    convert hx using 3
    ext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j => simp [MeasurableEquiv.piFinSuccAbove,Fin.insertNthEquiv,Fin.tail]

/-- The complement of the proper zero loci of a finite polynomial family is
open, dense and conull, even when some members vanish identically. -/
def Good {p : ℕ} (polys : List (Coeff p)) : Set (Params p) :=
  {x | ∀ q ∈ polys, q ≠ 0 → MvPolynomial.eval x q ≠ 0}

theorem good_locus {p : ℕ} (polys : List (Coeff p)) :
    IsOpen (Good polys) ∧ Dense (Good polys) ∧ ∀ᵐ x ∂volume, x ∈ Good polys := by
  have hopen : IsOpen (Good polys) := by
    induction polys with
    | nil => simp [Good]
    | cons q qs ih =>
      by_cases hq : q = 0
      · simpa [Good,hq] using ih
      · have he : Good (q::qs) = {x | MvPolynomial.eval x q ≠ 0} ∩ Good qs := by ext; simp [Good,hq]
        rw [he]
        exact (isOpen_ne_fun q.continuous_eval continuous_const).inter ih
  have hae : ∀ᵐ x ∂volume, x ∈ Good polys := by
    clear hopen
    induction polys with
    | nil => simp [Good]
    | cons q qs ih =>
      by_cases hq : q = 0
      · simpa [Good,hq] using ih
      · filter_upwards [ih,ae_polynomial_ne q hq] with x hx he
        simpa [Good,hq,he] using hx
  exact ⟨hopen,volume.dense_of_ae hae,hae⟩

end ReluStability

open SignType Set Filter
open scoped Topology

namespace ReluStability

/-- An affine input form whose coefficients are polynomials in all network parameters. -/
structure Form (p d : ℕ) where
  bias : Coeff p
  weight : Fin d → Coeff p

noncomputable def Form.eval {p d : ℕ} (f : Form p d) (θ : Params p) (x : Input d) : ℝ :=
  MvPolynomial.eval θ f.bias + ∑ i, MvPolynomial.eval θ (f.weight i) * x i

theorem Form.continuous_eval {p d : ℕ} (f : Form p d) :
    Continuous (fun z : Params p × Input d => f.eval z.1 z.2) := by
  unfold eval
  exact (f.bias.continuous_eval.comp continuous_fst).add (continuous_finsetSum _ fun j _ =>
    ((f.weight j).continuous_eval.comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))

noncomputable def Form.scale {p d : ℕ} (a : Coeff p) (f : Form p d) : Form p d :=
  ⟨a*f.bias,fun i => a*f.weight i⟩

noncomputable def Form.sub {p d : ℕ} (f g : Form p d) : Form p d :=
  ⟨f.bias-g.bias,fun i => f.weight i-g.weight i⟩

def Form.tail {p d : ℕ} (f : Form p (d+1)) : Form p d :=
  ⟨f.bias,fun i => f.weight i.succ⟩

def Form.lead {p d : ℕ} (f : Form p (d+1)) := f.weight 0

noncomputable def Form.resultant {p d : ℕ} (f g : Form p (d+1)) : Form p d :=
  (g.tail.scale f.lead).sub (f.tail.scale g.lead)

theorem Form.eval_scale {p d : ℕ} (a : Coeff p) (f : Form p d) (θ : Params p) (x : Input d) :
    (f.scale a).eval θ x = MvPolynomial.eval θ a * f.eval θ x := by
  simp [eval,scale,mul_add,Finset.mul_sum,mul_assoc]

theorem Form.eval_sub {p d : ℕ} (f g : Form p d) (θ : Params p) (x : Input d) :
    (f.sub g).eval θ x = f.eval θ x - g.eval θ x := by
  simp only [sub,eval,map_sub,sub_mul,Finset.sum_sub_distrib]
  ring

theorem Form.eval_split {p d : ℕ} (f : Form p (d+1)) (θ : Params p) (x : Input (d+1)) :
    f.eval θ x = MvPolynomial.eval θ f.lead * x 0 + f.tail.eval θ (Fin.tail x) := by
  rw [eval,Fin.sum_univ_succ]
  dsimp [lead,tail,eval,Fin.tail]
  ring

noncomputable def Form.root {p d : ℕ} (f : Form p (d+1)) (θ : Params p) (x : Input d) : ℝ :=
  -f.tail.eval θ x / MvPolynomial.eval θ f.lead

theorem Form.root_sub {p d : ℕ} (f g : Form p (d+1)) (θ : Params p) (x : Input d)
    (hf : MvPolynomial.eval θ f.lead ≠ 0) (hg : MvPolynomial.eval θ g.lead ≠ 0) :
    f.root θ x - g.root θ x = (f.resultant g).eval θ x /
      (MvPolynomial.eval θ f.lead * MvPolynomial.eval θ g.lead) := by
  rw [root,root,resultant,eval_sub,eval_scale,eval_scale]
  field_simp
  ring

theorem Form.eval_from_root {p d : ℕ} (f : Form p (d+1)) (θ : Params p) (x : Input (d+1))
    (hf : MvPolynomial.eval θ f.lead ≠ 0) :
    f.eval θ x = MvPolynomial.eval θ f.lead * (x 0 - f.root θ (Fin.tail x)) := by
  rw [eval_split,root]
  field_simp
  ring

theorem sign_of_inverse (x : ℝ) : sign x⁻¹ = sign x := by
  rcases lt_trichotomy x 0 with h|rfl|h
  · rw [sign_neg h,sign_neg (inv_lt_zero.mpr h)]
  · simp
  · rw [sign_pos h,sign_pos (inv_pos.mpr h)]

theorem sign_quotient (x y : ℝ) : sign (x/y) = sign x * sign y := by
  rw [div_eq_mul_inv,sign_mul,sign_of_inverse]

theorem sign_sub_iff (a b c d : ℝ) :
    sign (a-b) = sign (c-d) ↔ ((a<b ↔ c<d) ∧ (a=b ↔ c=d)) := by
  constructor
  · intro h
    have hl (x y : ℝ) : x<y ↔ sign (x-y) = -1 := (sign_eq_neg_one_iff.trans sub_neg).symm
    have he (x y : ℝ) : x=y ↔ sign (x-y) = 0 := (sign_eq_zero_iff.trans sub_eq_zero).symm
    exact ⟨by rw [hl a b,hl c d,h],by rw [he a b,he c d,h]⟩
  · rintro ⟨hl,he⟩
    rcases lt_trichotomy a b with h|h|h
    · rw [sign_neg (sub_neg.mpr h),sign_neg (sub_neg.mpr (hl.mp h))]
    · rw [h,he.mp h]; simp
    · have h' := lt_of_le_of_ne (le_of_not_gt (mt hl.mpr h.not_gt)) (Ne.symm (mt he.mpr h.ne'))
      rw [sign_pos (sub_pos.mpr h),sign_pos (sub_pos.mpr h')]

noncomputable def projected {p d : ℕ} (fs : List (Form p (d+1))) : List (Form p d) :=
  fs.map Form.tail ++ fs.flatMap (fun f => fs.map (Form.resultant f))

noncomputable def discriminants {p : ℕ} : (d : ℕ) → List (Form p d) → List (Coeff p)
  | 0, fs => fs.map Form.bias
  | d+1, fs => fs.map Form.lead ++ discriminants d (projected fs)

theorem signs_near {p : ℕ} (fs : List (Coeff p)) {θ : Params p} (hθ : θ ∈ Good fs) :
    ∀ᶠ η in 𝓝 θ, ∀ q ∈ fs, sign (MvPolynomial.eval θ q) = sign (MvPolynomial.eval η q) := by
  induction fs with
  | nil => simp
  | cons q qs ih =>
    have htail := ih (fun f hf => hθ f (List.mem_cons_of_mem _ hf))
    by_cases hz : q = 0
    · simpa [hz] using htail
    have hx := hθ q (by simp) hz
    have hh : ∀ᶠ η in 𝓝 θ, sign (MvPolynomial.eval θ q) = sign (MvPolynomial.eval η q) := by
      rcases lt_or_gt_of_ne hx with hn|hp
      · filter_upwards [q.continuous_eval.continuousAt.eventually_lt continuousAt_const hn] with x hx
        rw [sign_neg hn,sign_neg hx]
      · filter_upwards [continuousAt_const.eventually_lt q.continuous_eval.continuousAt hp] with x hx
        rw [sign_pos hp,sign_pos hx]
    filter_upwards [hh,htail] with η h₁ h₂
    simpa [h₁] using h₂

end ReluStability

open SignType Set Filter
open scoped Topology

namespace ReluStability

def Aligns {B : Type*} [TopologicalSpace B] {p d : ℕ} (fs : List (Form p d))
    (θ : Params p) (w : B → Params p) (H : Family B (Input d)) : Prop :=
  ∀ b f, f ∈ fs → ∀ x, sign (f.eval θ x) = sign (f.eval (w b) (H.map b x))

theorem lift_arrangement {B : Type*} [TopologicalSpace B] {p d : ℕ} (fs : List (Form p (d+1)))
    (θ : Params p) (w : B → Params p) (hw : Continuous w)
    (hl : ∀ b f, f ∈ fs → sign (MvPolynomial.eval θ f.lead) = sign (MvPolynomial.eval (w b) f.lead))
    (H : Family B (Input d)) (hh : Aligns (projected fs) θ w H)
    (hid : ∀ b, w b = θ → ∀ x, H.map b x = x) :
    ∃ G : Family B (Input (d+1)), Aligns fs θ w G ∧ ∀ b, w b = θ → ∀ x, G.map b x = x := by
  classical
  let active := fs.filter fun f => MvPolynomial.eval θ f.lead ≠ 0
  let left (f : Form p (d+1)) (z : B×Input d) := f.root θ z.2
  let right (f : Form p (d+1)) (z : B×Input d) := f.root (w z.1) (H.map z.1 z.2)
  let knots := active.map fun f => (left f,right f)
  have nh (b) (f) (hf : f ∈ fs) : MvPolynomial.eval θ f.lead = 0 ↔ MvPolynomial.eval (w b) f.lead = 0 := by
    rw [←sign_eq_zero_iff,←sign_eq_zero_iff (a:=MvPolynomial.eval (w b) f.lead),hl b f hf]
  have hc (k) (hk : k ∈ knots) : Continuous k.1 ∧ Continuous k.2 := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hk
    obtain ⟨hfs,hlead⟩ := List.mem_filter.mp hf
    have hne : MvPolynomial.eval θ f.lead ≠ 0 := by simpa using hlead
    refine ⟨(f.tail.continuous_eval.comp (continuous_const.prodMk continuous_snd)).neg.div_const _,?_⟩
    exact ((f.tail.continuous_eval.comp ((hw.comp continuous_fst).prodMk H.forward)).neg).div
      (f.lead.continuous_eval.comp (hw.comp continuous_fst)) (fun z => mt (nh z.1 f hfs).mpr hne)
  have ho (z : B×Input d) (i) (hi : i ∈ knots) (j) (hj : j ∈ knots) :
      (i.1 z < j.1 z ↔ i.2 z < j.2 z) ∧ (i.1 z = j.1 z ↔ i.2 z = j.2 z) := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hi
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hj
    obtain ⟨hfs,hnf'⟩ := List.mem_filter.mp hf
    obtain ⟨hgs,hng'⟩ := List.mem_filter.mp hg
    have hnf : MvPolynomial.eval θ f.lead ≠ 0 := by simpa using hnf'
    have hng : MvPolynomial.eval θ g.lead ≠ 0 := by simpa using hng'
    apply (sign_sub_iff ..).mp
    change sign (f.root θ z.2-g.root θ z.2) = sign (f.root _ _ - g.root _ _)
    have hd := hh z.1 (f.resultant g) (by
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨f,hfs,List.mem_map.mpr ⟨g,hgs,rfl⟩⟩) z.2
    rw [f.root_sub g _ _ hnf hng,f.root_sub g _ _ (mt (nh _ f hfs).mpr hnf) (mt (nh _ g hgs).mpr hng),
      sign_quotient,sign_quotient,sign_mul,sign_mul,hd,hl _ f hfs,hl _ g hgs]
  obtain ⟨T,hT,hland,htid⟩ := ordered_transport knots hc ho
  refine ⟨H.lift T hT,?_,?_⟩
  · intro b f hf x
    have ht : f.tail ∈ projected fs := List.mem_append_left _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
    change sign (f.eval θ x) = sign (f.eval (w b) (liftForward H T b x))
    by_cases hz : MvPolynomial.eval θ f.lead = 0
    · simpa only [f.eval_split,hz,(nh b f hf).mp hz,zero_mul,zero_add,liftForward,Fin.tail_cons] using
        hh b f.tail ht (Fin.tail x)
    · have hk : (left f,right f) ∈ knots := List.mem_map.mpr ⟨f,List.mem_filter.mpr ⟨hf,by simpa using hz⟩,rfl⟩
      have hm : T (b,Fin.tail x) (left f (b,Fin.tail x)) = right f (b,Fin.tail x) := hland (b,Fin.tail x) (left f,right f) hk
      rw [f.eval_from_root _ _ hz,f.eval_from_root _ _ (mt (nh _ f hf).mpr hz),sign_mul,sign_mul,hl _ f hf]
      congr 1
      simp only [liftForward,Fin.cons_zero,Fin.tail_cons]
      change sign (x 0 - left f (b,Fin.tail x)) = sign (T _ (x 0) - right f (b,Fin.tail x))
      rw [←hm]
      exact (sign_sub_iff ..).mpr ⟨(T _).lt_iff_lt.symm,(T _).injective.eq_iff.symm⟩
  · intro b hb x
    have hkn : ∀ k ∈ knots, k.1 (b,Fin.tail x) = k.2 (b,Fin.tail x) := by
      intro k hk
      obtain ⟨f,_,rfl⟩ := List.mem_map.mp hk
      simp [left,right,hb,hid b hb]
    change Fin.cons (T (b,Fin.tail x) (x 0)) (H.map b (Fin.tail x)) = x
    rw [htid _ hkn,hid _ hb,Fin.cons_self_tail]

/-- A finite parameter-polynomial discriminant list suffices to keep every
ternary sign throughout the whole input space under ambient homeomorphisms. -/
theorem sweep {B : Type*} [TopologicalSpace B] {p : ℕ} (d : ℕ) (fs : List (Form p d))
    (θ : Params p) (w : B → Params p) (hw : Continuous w)
    (hs : ∀ b q, q ∈ discriminants d fs → sign (MvPolynomial.eval θ q) = sign (MvPolynomial.eval (w b) q)) :
    ∃ H : Family B (Input d), Aligns fs θ w H ∧ ∀ b, w b = θ → ∀ x, H.map b x = x := by
  induction d with
  | zero =>
    refine ⟨Family.identity _ _,?_,fun _ _ _ => rfl⟩
    intro b f hf x
    simpa [Form.eval] using hs b f.bias (List.mem_map.mpr ⟨f,hf,rfl⟩)
  | succ d ih =>
    obtain ⟨H,hh,hid⟩ := ih (projected fs) (fun b q hq => hs b q (List.mem_append_right _ hq))
    exact lift_arrangement fs θ w hw (fun b f hf => hs b f.lead (List.mem_append_left _ (List.mem_map.mpr ⟨f,hf,rfl⟩))) H hh hid

/-- The parameter region is the complement of explicit polynomial zero loci.
Every base parameter in it has a neighborhood of simultaneous triviality. -/
theorem arrangement_stable {p d : ℕ} (fs : List (Form p d)) :
    let U := Good (discriminants d fs)
    IsOpen U ∧ Dense U ∧ (∀ᵐ θ ∂MeasureTheory.volume, θ ∈ U) ∧
      ∀ θ ∈ U, ∃ V : Set (Params p), IsOpen V ∧ θ ∈ V ∧
        ∃ H : Family V (Input d), Aligns fs θ Subtype.val H ∧ ∀ b : V, b.val = θ → ∀ x, H.map b x = x := by
  refine ⟨(good_locus _).1,(good_locus _).2.1,(good_locus _).2.2,?_⟩
  intro θ hθ
  obtain ⟨V,hsub,hopen,hmem⟩ := mem_nhds_iff.mp (signs_near _ hθ)
  refine ⟨V,hopen,hmem,?_⟩
  exact sweep d fs θ Subtype.val continuous_subtype_val (fun b => hsub b.property)

end ReluStability

open SignType Set

namespace ReluStability

noncomputable def Form.zero (p d : ℕ) : Form p d := ⟨0,fun _ => 0⟩

noncomputable def Form.add {p d : ℕ} (f g : Form p d) : Form p d :=
  ⟨f.bias+g.bias,fun i => f.weight i+g.weight i⟩

noncomputable def Form.sum {p d : ℕ} : {n : ℕ} → (Fin n → Form p d) → Form p d
  | 0, _ => .zero p d
  | _+1, f => (Form.sum (Fin.tail f)).add (f 0)

theorem Form.eval_sum {p d n : ℕ} (f : Fin n → Form p d) (θ : Params p) (x : Input d) :
    (Form.sum f).eval θ x = ∑ i, (f i).eval θ x := by
  induction n with
  | zero => simp [sum,zero,eval]
  | succ n ih =>
    rw [sum,Fin.sum_univ_succ]
    have add_eval (a b : Form p d) : (a.add b).eval θ x = a.eval θ x+b.eval θ x := by
      simp only [add,eval,map_add,add_mul,Finset.sum_add_distrib]; ring
    rw [add_eval,ih,add_comm]
    rfl

/-- A gate can depend affinely on the inputs and any previous gates, with
arbitrary polynomial functions of the parameters as all its coefficients.
Independent trainable weights, biases, fixed weights and shared weights are included. -/
structure Gate (p d n : ℕ) where
  direct : Form p d
  weight : Fin n → Coeff p

noncomputable def Gate.eval {p d n : ℕ} (a : Gate p d n) (θ : Params p) (x : Input d) (v : Fin n → ℝ) : ℝ :=
  a.direct.eval θ x + ∑ i, MvPolynomial.eval θ (a.weight i) * v i

noncomputable def Gate.form {p d n : ℕ} (a : Gate p d n) (v : Fin n → Form p d) : Form p d :=
  a.direct.add (Form.sum fun i => (v i).scale (a.weight i))

theorem Gate.eval_form {p d n : ℕ} (a : Gate p d n) (v : Fin n → Form p d) (θ : Params p) (x : Input d) :
    (a.form v).eval θ x = a.eval θ x (fun i => (v i).eval θ x) := by
  have ha (b c : Form p d) : (b.add c).eval θ x = b.eval θ x + c.eval θ x := by
    simp only [Form.add,Form.eval,map_add,add_mul,Finset.sum_add_distrib]; ring
  simp only [form,ha,Form.eval_sum,Form.eval_scale,eval]

inductive Model (p d : ℕ) : ℕ → Type where
  | empty : Model p d 0
  | append {n : ℕ} (b : Model p d n) (a : Gate p d n) : Model p d (n+1)

noncomputable def Model.pre {p d n : ℕ} (N : Model p d n) (θ : Params p) (x : Input d) : Fin n → ℝ :=
  match N with
  | .empty => Fin.elim0
  | .append b a => Fin.snoc (α:=fun _ => ℝ) (b.pre θ x) (a.eval θ x (fun i => max (b.pre θ x i) 0))

noncomputable def Model.masked {p d n : ℕ} (N : Model p d n) (σ : Fin n → Bool) : Fin n → Form p d :=
  match N with
  | .empty => Fin.elim0
  | @append _ _ k b a =>
    let v := b.masked (Fin.init σ)
    Fin.snoc (α:=fun _ => Form p d) v (if σ (Fin.last k) then a.form v else Form.zero p d)

noncomputable def Model.tests {p d n : ℕ} (N : Model p d n) : List (Form p d) :=
  match N with
  | .empty => []
  | @append _ _ k b a => b.tests ++ (Finset.univ : Finset (Fin k → Bool)).toList.map (fun σ => a.form (b.masked σ))

def Model.realizes {p d n : ℕ} (N : Model p d n) (σ : Fin n → Bool) (θ : Params p) (x : Input d) :=
  ∀ i, max (N.pre θ x i) 0 = (N.masked σ i).eval θ x

theorem Model.pre_last {p d n : ℕ} (b : Model p d n) (a : Gate p d n) (σ : Fin n → Bool)
    (θ : Params p) (x : Input d) (h : b.realizes σ θ x) :
    (b.append a).pre θ x (Fin.last n) = (a.form (b.masked σ)).eval θ x := by
  simp only [pre,Fin.snoc_last,Gate.eval_form]
  rw [show (fun i => max (b.pre θ x i) 0) = _ from funext h]

theorem Model.realizes_append {p d n : ℕ} (b : Model p d n) (a : Gate p d n) (σ : Fin n → Bool)
    (θ : Params p) (x : Input d) (h : b.realizes σ θ x) (active : Bool)
    (he : max ((a.form (b.masked σ)).eval θ x) 0 =
      (if active then a.form (b.masked σ) else Form.zero p d).eval θ x) :
    (b.append a).realizes (Fin.snoc (α:=fun _ => Bool) σ active) θ x := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [b.pre_last a σ θ x h,masked,Fin.snoc_last,Fin.init_snoc] using he
  | cast i => simpa only [pre,masked,Fin.snoc_castSucc,Fin.init_snoc] using h i

noncomputable def Model.word {p d n : ℕ} (N : Model p d n) (θ : Params p) (x : Input d) : Fin n → SignType :=
  fun i => sign (N.pre θ x i)

theorem Model.aligned_words {p d n : ℕ} (N : Model p d n) (θ η : Params p) (x y : Input d)
    (h : ∀ f ∈ N.tests, sign (f.eval θ x) = sign (f.eval η y)) :
    N.word θ x = N.word η y ∧ ∃ σ, N.realizes σ θ x ∧ N.realizes σ η y := by
  induction N with
  | empty => exact ⟨funext fun i => i.elim0,Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | @append n b a ih =>
    obtain ⟨hw,σ,hx,hy⟩ := ih (fun f hf => h f (List.mem_append_left _ hf))
    have hf := h (a.form (b.masked σ)) (List.mem_append_right _ (List.mem_map.mpr ⟨σ,by simp,rfl⟩))
    constructor
    · funext i
      induction i using Fin.lastCases with
      | last => simpa only [word,b.pre_last a σ θ x hx,b.pre_last a σ η y hy] using hf
      | cast i => simpa only [word,pre,Fin.snoc_castSucc] using congrFun hw i
    · by_cases hp : 0 < (a.form (b.masked σ)).eval θ x
      · have hy' := sign_eq_one_iff.mp (hf ▸ sign_pos hp)
        exact ⟨Fin.snoc σ true,b.realizes_append a σ θ x hx true (max_eq_left hp.le),
          b.realizes_append a σ η y hy true (max_eq_left hy'.le)⟩
      · have hy' : ¬0 < (a.form (b.masked σ)).eval η y := fun hy' =>
          hp (sign_eq_one_iff.mp (hf.trans (sign_pos hy')))
        refine ⟨Fin.snoc σ false,b.realizes_append a σ θ x hx false ?_,b.realizes_append a σ η y hy false ?_⟩
        · rw [max_eq_right (le_of_not_gt hp)]; simp [Form.zero,Form.eval]
        · rw [max_eq_right (le_of_not_gt hy')]; simp [Form.zero,Form.eval]

/-- The full ternary sign cell, including units exactly at zero. -/
def Model.cell {p d n : ℕ} (N : Model p d n) (θ : Params p) (s : Fin n → SignType) : Set (Input d) :=
  {x | N.word θ x = s}

end ReluStability

open SignType Set MeasureTheory

namespace ReluStability

/-- The finite exceptional polynomial hypersurfaces are read directly from
the architecture. All ternary sign cells, their closures, face incidences and
small inductive dimensions are simultaneously preserved by a continuously
varying ambient homeomorphism equal to the identity at the base parameter. -/
theorem stability {p d n : ℕ} (N : Model p d n) :
    ∃ polys : List (Coeff p), IsOpen (Good polys) ∧ Dense (Good polys) ∧
      (∀ᵐ θ : Params p ∂volume, θ ∈ Good polys) ∧
      ∀ θ ∈ Good polys, ∃ V : Set (Params p), IsOpen V ∧ θ ∈ V ∧
        ∃ H : Family V (Input d), (∀ b : V, b.val = θ → ∀ x, H.map b x = x) ∧
          ∀ b : V, (∀ x, N.word θ x = N.word b.val (H.map b x)) ∧
            (∀ s, H.map b '' N.cell θ s = N.cell b.val s ∧
              H.map b '' closure (N.cell θ s) = closure (N.cell b.val s) ∧
              smallInductiveDimension (N.cell θ s) = smallInductiveDimension (N.cell b.val s)) ∧
            ∀ s t, closure (N.cell θ s) ⊆ closure (N.cell θ t) ↔
              closure (N.cell b.val s) ⊆ closure (N.cell b.val t) := by
  obtain ⟨hop,hd,ha,hl⟩ := arrangement_stable N.tests
  refine ⟨discriminants d N.tests,hop,hd,ha,?_⟩
  intro θ hθ
  obtain ⟨V,hV,hmem,H,hH,hid⟩ := hl θ hθ
  refine ⟨V,hV,hmem,H,hid,?_⟩
  intro b
  have hw (x) : N.word θ x = N.word b.val (H.map b x) :=
    (N.aligned_words _ _ _ _ (fun f hf => hH b f hf x)).1
  have hi (s) : H.map b '' N.cell θ s = N.cell b.val s := by
    ext y
    obtain ⟨x,rfl⟩ := (H.map b).surjective y
    constructor
    · rintro ⟨x',hx',he'⟩
      obtain rfl := (H.map b).injective he'
      exact (hw x').symm.trans hx'
    · exact fun hx => ⟨x,(hw x).trans hx,rfl⟩
  have hcl (s) : H.map b '' closure (N.cell θ s) = closure (N.cell b.val s) := by
    rw [(H.map b).image_closure,hi]
  refine ⟨hw,fun s => ⟨hi s,hcl s,?_⟩,fun s t => ?_⟩
  · exact (((H.map b).isEmbedding.homeomorphImage _).trans (Homeomorph.setCongr (hi s))).smallInductiveDimension_congr
  · rw [←hcl,←hcl]
    exact (image_subset_image_iff (H.map b).injective).symm

end ReluStability
