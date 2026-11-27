module

public import SolvedProblems.JointForestNeighbors

@[expose] public section

namespace JointForest

open SimpleGraph

variable {T : Type*} [LinearOrder T] [Fintype T] {m r : ℕ}

instance decideStep : DecidableRel (@step T _ m r) := fun x y => by
  cases x with
  | inl x => cases y <;> unfold step <;> infer_instance
  | inr x => cases y <;> unfold step <;> infer_instance

instance : DecidableRel (expanded T m r).Adj := fun u v => by
  letI : Decidable (step u v) := decideStep u v
  letI : Decidable (step v u) := decideStep v u
  exact inferInstanceAs (Decidable (u ≠ v ∧ (step u v ∨ step v u)))

/-- Summing the incidences of all sides at `u` counts each other terminal once. -/
theorem incident_sum (u : T) (f : T → ℚ) :
    (∑ e : Side T, ((if e.val.1 = u then f e.val.2 else 0) + (if e.val.2 = u then f e.val.1 else 0))) =
    ∑ v, if u ≠ v then f v else 0 := by
  let l (p : T × T) := if p.1 = u then (if u < p.2 then f p.2 else 0) else 0
  let r (p : T × T) := if p.2 = u then (if p.1 < u then f p.1 else 0) else 0
  have h (p : Side T) : (if p.val.1 = u then f p.val.2 else 0) + (if p.val.2 = u then f p.val.1 else 0) = l p + r p := by
    have hp := p.property
    dsimp [l,r]
    split_ifs <;> simp_all
  have hz : (∑ p : {p : T × T // ¬ p.1 < p.2}, (l p + r p)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hp := p.property
    dsimp [l,r]; split_ifs <;> simp_all
  have ht := Fintype.sum_subtype_add_sum_subtype (fun p : T × T => p.1 < p.2) (fun p => l p + r p)
  rw [hz, add_zero] at ht
  simp_rw [h]
  rw [ht, Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm (f := fun x y => l (x,y))]
  simp only [l,r, Fintype.sum_ite_eq']
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rcases lt_trichotomy u v with h | rfl | h <;> simp [*, ne_of_gt, ne_of_lt, not_lt_of_gt]

def firstPos (hr : 0 < r) : Fin r := ⟨0,hr⟩
def lastPos (hr : 0 < r) : Fin r := ⟨r-1,by omega⟩

omit [Fintype T] in
theorem terminal_adj (u v : T) : (expanded T m r).Adj (.inl u) (.inl v) ↔ u ≠ v := by
  change (_ ∧ (u < v ∨ v < u)) ↔ _
  exact ⟨fun h e => h.1 (congrArg Sum.inl e), fun h => ⟨fun h' => h (Sum.inl.inj h'), lt_or_gt_of_ne h⟩⟩

omit [Fintype T] in
theorem terminal_inner_adj (u : T) (e : Side T) (i : Fin m) (j : Fin r) (hr : 0 < r) :
    (expanded T m r).Adj (.inl u) (.inr (e,i,j)) ↔
      (e.val.1 = u ∧ j = firstPos hr) ∨ (e.val.2 = u ∧ j = lastPos hr) := by
  have h : j.val+1 = r ↔ j.val = r-1 := by omega
  simp [expanded, step, firstPos, lastPos, Fin.ext_iff, eq_comm (a := u), h]

omit [Fintype T] in
/-- Sum over one path bundle at its two endpoints. The distinguished positions
are present whenever the number of internal vertices is positive. -/
theorem incident_path_sum (u : T) (e : Side T) (hr : 0 < r) (f : Base T m r → ℚ) :
    (∑ i : Fin m, ∑ j : Fin r, if (expanded T m r).Adj (.inl u) (.inr (e,i,j)) then f (.inr (e,i,j)) else 0) =
    (if e.val.1 = u then ∑ i, f (.inr (e,i,firstPos hr)) else 0) +
    (if e.val.2 = u then ∑ i, f (.inr (e,i,lastPos hr)) else 0) := by
  have hne := ne_of_lt e.property
  by_cases hl : e.val.1 = u <;> by_cases hr' : e.val.2 = u <;>
    first | exact (hne (hl.trans hr'.symm)).elim | simp [terminal_inner_adj _ _ _ _ hr, hl, hr']

/-- Exact neighbor enumeration at a terminal, including the direct edge and
both kinds of incident long-path bundles. -/
theorem terminal_neighbor_sum (u : T) (hr : 0 < r) (f : Base T m r → ℚ) :
    (∑ z, if (expanded T m r).Adj (.inl u) z then f z else 0) =
    ∑ e : Side T,
      ((if e.val.1 = u then f (.inl e.val.2) + ∑ i, f (.inr (e,i,firstPos hr)) else 0) +
      (if e.val.2 = u then f (.inl e.val.1) + ∑ i, f (.inr (e,i,lastPos hr)) else 0)) := by
  rw [Fintype.sum_sum_type]
  simp_rw [terminal_adj, Fintype.sum_prod_type]
  rw [← incident_sum u (fun v => f (.inl v))]
  simp_rw [incident_path_sum u _ hr f]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

end JointForest
