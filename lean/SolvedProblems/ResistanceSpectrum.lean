module

public import SolvedProblems.ResistanceSoundness
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

open scoped Matrix

namespace ResistanceLifts

/-- Apply the ordinary Laplacian using the displayed neighbor lists. -/
def lapStep (t : Bool) (f : Vertex → ℤ) (x : Vertex) : ℤ :=
  (neighbors t x).length * f x - ((neighbors t x).map f).sum

def diagonalCube (t : Bool) (x : Vertex) : ℤ :=
  lapStep t (lapStep t (lapStep t (fun i => if i = x then 1 else 0))) x

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem integer_traces : (∑ x, diagonalCube false x) = 9228 ∧
    (∑ x, diagonalCube true x) = 9240 := by decide +kernel

theorem lap_step_real (t : Bool) (f : Vertex → ℤ) :
    (graph t).lapMatrix ℝ *ᵥ (fun v => (f v : ℝ)) = fun x => (lapStep t f x : ℝ) := by
  ext x
  rw [SimpleGraph.lapMatrix_mulVec_apply, lapStep, ← degree_eq_length,
    ← List.sum_toFinset _ (neighbors_valid t x).1, ← neighborFinset_eq]
  push_cast
  rfl

theorem trace_cube (t : Bool) : ((graph t).lapMatrix ℝ ^ 3).trace =
    ((∑ x, diagonalCube t x : ℤ) : ℝ) := by
  rw [Matrix.trace, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  let L := (graph t).lapMatrix ℝ
  change (L^3).col x x = _
  rw [← Matrix.mulVec_single_one]
  have hs : Pi.single x (1:ℝ) = (fun i => ((if i = x then 1 else 0 : ℤ) : ℝ)) := by
    ext i
    by_cases h : i = x <;> simp [h]
  rw [show L^3 = L * (L * L) by simp [pow_succ, Matrix.mul_assoc], ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hs, lap_step_real, lap_step_real, lap_step_real]
  rfl

/-- For symmetric real matrices the cube trace is fixed by the characteristic
polynomial, since it is the sum of the cubes of the eigenvalues with multiplicity. -/
theorem trace_cube_characteristic {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℝ} (ha : A.IsHermitian) (hb : B.IsHermitian)
    (hp : A.charpoly = B.charpoly) : (A ^ 3).trace = (B ^ 3).trace := by
  have trace_diag {M : Matrix V V ℝ} (h : M.IsHermitian) :
      (M^3).trace = ((Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) : Matrix V V ℝ)^3).trace := by
    conv_lhs => rw [h.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  rw [trace_diag ha, trace_diag hb, (ha.eigenvalues_eq_eigenvalues_iff hb).mpr hp]

theorem spectra_differ : laplacianPolynomial (graph false) ≠ laplacianPolynomial (graph true) := by
  intro h
  unfold laplacianPolynomial at h
  rw [show (fun i j => Classical.propDecidable ((graph false).Adj i j)) =
    (inferInstance : DecidableRel (graph false).Adj) from Subsingleton.elim _ _,
    show (fun i j => Classical.propDecidable ((graph true).Adj i j)) =
    (inferInstance : DecidableRel (graph true).Adj) from Subsingleton.elim _ _] at h
  have ht := trace_cube_characteristic ((graph false).isHermitian_lapMatrix ℝ)
    ((graph true).isHermitian_lapMatrix ℝ) h
  rw [trace_cube, trace_cube, integer_traces.1, integer_traces.2] at ht
  norm_num at ht

end ResistanceLifts
