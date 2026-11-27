module

public import SolvedProblems.JointForestBoundary

@[expose] public section

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

theorem left_contact (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inl e.val.1) (.inr (e,i,j))) = 1 := by
  simp [signing, signBit, ne_of_lt e.property]

theorem right_contact (tw : Bool) (d e : Side T) (i : Fin m) (j : Fin r) :
    polarity ((signing tw d).neg (.inl e.val.2) (.inr (e,i,j))) = -sideSign tw d e := by
  rw [(signing tw d).symm]; exact right_sign ..

theorem direct_reverse (tw : Bool) (d e : Side T) :
    polarity ((signing (m := m) (r := r) tw d).neg (.inl e.val.2) (.inl e.val.1)) = sideSign tw d e := by
  rw [(signing tw d).symm]; exact direct_sign ..

/-- The diagonal of the terminal Schur complement is positive and independent
of all signs. Each other terminal contributes the conductance of one side. -/
noncomputable def terminalD [Fintype T] (r : ℕ) (u : T) : ℚ := 1 + ∑ v : T, if u ≠ v then gain r else 0

theorem terminalD_pos [Fintype T] (r : ℕ) (u : T) : 0 < terminalD r u := by
  have h : 0 ≤ ∑ v : T, if u ≠ v then gain r else 0 := by
    apply Finset.sum_nonneg; intro x _; split <;> first | exact (gain_pos r).le | rfl
  unfold terminalD; linarith

/-- Compute the terminal row of the shifted signed Laplacian after extending
arbitrary boundary data and a single interior or terminal source. -/
theorem terminal_current [Fintype T] (hr : 0 < r) (hm : m = continuant (r+1)) (tw : Bool) (d : Side T)
    (z : T → ℚ) (a : Base T m r) (u : T) :
    signedShift (expanded T m r) (signing tw d) (extension tw d z a) (.inl u) =
    terminalD r u * z u - (boundaryWeight tw d a u - pulse (.inl u) a) := by
  classical
  let p := extension tw d z a
  let f (v : Base T m r) := z u - polarity ((signing tw d).neg (.inl u) v) * p v
  have hL (e : Side T) (h : e.val.1 = u) : f (.inl e.val.2) + (∑ i, f (.inr (e,i,firstPos hr))) =
      gain r * z u - leftLeak a e := by
    subst u
    simp only [f, p, extension, direct_sign, left_contact, one_mul, firstPos, Nat.zero_add, leftLeak]
    exact left_bundle hm tw d e z a
  have hR (e : Side T) (h : e.val.2 = u) : f (.inl e.val.1) + (∑ i, f (.inr (e,i,lastPos hr))) =
      gain r * z u + sideSign tw d e * rightLeak a e := by
    subst u
    simp only [f, p, extension, direct_reverse, right_contact, neg_mul, sub_neg_eq_add, lastPos,
      show r-1+1 = r by omega, rightLeak]
    exact right_bundle hm tw d e z a
  have terms (e : Side T) : (if e.val.1 = u then f (.inl e.val.2) + ∑ i, f (.inr (e,i,firstPos hr)) else 0) +
      (if e.val.2 = u then f (.inl e.val.1) + ∑ i, f (.inr (e,i,lastPos hr)) else 0) =
      ((if e.val.1 = u then gain r else 0) + (if e.val.2 = u then gain r else 0)) * z u -
      ((if e.val.1 = u then leftLeak a e else 0) - (if e.val.2 = u then sideSign tw d e * rightLeak a e else 0)) := by
    split_ifs with hl ht ht
    · exact (ne_of_lt e.property (hl.trans ht.symm)).elim
    · rw [hL e hl]; ring
    · rw [hR e ht]; ring
    · ring
  have row : signedShift (expanded T m r) (signing tw d) (extension tw d z a) (.inl u) =
      z u + (∑ v, if (expanded T m r).Adj (.inl u) v then f v else 0) := by
    unfold signedShift
    apply congrArg (z u + ·)
    apply Finset.sum_congr (Finset.ext (fun _ => by simp))
    intro v _
    by_cases hv : (expanded T m r).Adj (.inl u) v <;> simp [hv, f, p, extension]
  rw [row]
  rw [terminal_neighbor_sum u hr f]
  simp_rw [terms]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, incident_sum u (fun _ => gain r), sum_leaks]
  unfold terminalD
  ring

noncomputable def terminalVoltage [Fintype T] (tw : Bool) (d : Side T) (a : Base T m r) (u : T) : ℚ :=
  boundaryWeight tw d a u / terminalD r u

/-- The signed inverse after eliminating long interiors. -/
noncomputable def signedGreen [Fintype T] (tw : Bool) (d : Side T) (a : Base T m r) : Base T m r → ℚ :=
  extension tw d (terminalVoltage tw d a) a

theorem signedGreen_solve [Fintype T] (hr : 0 < r) (hm : m = continuant (r+1)) (tw : Bool) (d : Side T)
    (a x : Base T m r) : signedShift (expanded T m r) (signing tw d) (signedGreen tw d a) x = pulse x a := by
  cases x with
  | inl u =>
    rw [signedGreen, terminal_current hr hm]
    unfold terminalVoltage
    field_simp [(terminalD_pos r u).ne']
    ring
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    exact extension_inner_eq tw d _ a e i j

end JointForest
