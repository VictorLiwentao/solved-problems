module

public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

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
