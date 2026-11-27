module

public import SolvedProblems.ResistanceKernel
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped Matrix

namespace ResistanceLifts

/-- Any solution to the unit current equations gives the same terminal drop. -/
theorem resistance_of_potential {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Reachable a b) {u : V → ℝ}
    (hu : UnitPotential G a b u) : resistance G a b = u a - u b := by
  classical
  have ex : ∃ v, UnitPotential G a b v := ⟨u, hu⟩
  rw [resistance, dite_eq_left ex]
  have he : G.lapMatrix ℝ *ᵥ ex.choose = G.lapMatrix ℝ *ᵥ u := ex.choose_spec.trans hu.symm
  have hz : G.lapMatrix ℝ *ᵥ (ex.choose - u) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
  have hv := (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hz) a b hab
  simp only [Pi.sub_apply] at hv
  linarith

theorem degree_eq_length (t : Bool) (v : Vertex) :
    (graph t).degree v = (neighbors t v).length := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq,
    List.toFinset_card_of_nodup (neighbors_valid t v).1]

theorem column_real {t : Bool} {z : Vertex} (h : ∀ x, columnHolds t z x) (x : Vertex) :
    ((graph t).lapMatrix ℝ *ᵥ (fun v => (green t v z : ℝ))) x =
    (if x = z then (1152 : ℝ) else 0) - (if x.1.val < 3 then 192 else 0) := by
  have hz := h x
  unfold columnHolds at hz
  rw [← degree_eq_length, ← List.sum_toFinset _ (neighbors_valid t x).1, ← neighborFinset_eq] at hz
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  split_ifs at hz ⊢ <;> exact_mod_cast hz

/-- The explicit scaled integer kernel certifies the true real effective resistance. -/
theorem resistance_from_columns {t : Bool} (cols : ∀ z x, columnHolds t z x)
    (hc : (graph t).Connected) (a b : Vertex) :
    resistance (graph t) a b = (numerator t a b : ℝ) / 1152 := by
  let col (z : Vertex) := fun x => (green t x z : ℝ)
  let u : Vertex → ℝ := (1152 : ℝ)⁻¹ • (col a - col b)
  have hu : UnitPotential (graph t) a b u := by
    unfold UnitPotential
    rw [show (fun i j => Classical.propDecidable ((graph t).Adj i j)) =
      (inferInstance : DecidableRel (graph t).Adj) from Subsingleton.elim _ _]
    rw [show u = (1152 : ℝ)⁻¹ • (col a - col b) from rfl, Matrix.mulVec_smul, Matrix.mulVec_sub]
    ext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, col]
    rw [column_real (cols a), column_real (cols b)]
    split_ifs <;> norm_num
  rw [resistance_of_potential (hc a b) hu]
  simp only [u, col, numerator, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Int.cast_sub]
  ring

end ResistanceLifts
