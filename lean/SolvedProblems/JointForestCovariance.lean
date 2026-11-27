module

public import SolvedProblems.JointForestFlips

@[expose] public section

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- The part of the covariance conditional on all terminal values. It vanishes
unless both arguments are in the same long path. -/
def localPart (a : Base T m r) : Base T m r → ℚ
  | .inl _ => 0
  | .inr (e,i,j) => localGreen a e i (j.val+1)

theorem green_expansion [Fintype T] (tw : Bool) (d : Side T) (a x : Base T m r) :
    signedGreen tw d a x = localPart a x + ∑ u : T,
      boundaryWeight tw d a u * boundaryWeight tw d x u / terminalD r u := by
  let w := boundaryWeight tw d a
  cases x with
  | inl v =>
    have h (u : T) : w u * boundaryWeight tw d (.inl v : Base T m r) u / terminalD r u =
        if u = v then w u / terminalD r u else 0 := by
      by_cases hu : u = v <;> simp [boundaryWeight,hu]
    change w v / terminalD r v = 0 + ∑ u, w u * boundaryWeight tw d (.inl v : Base T m r) u / terminalD r u
    simp_rw [h]
    simp
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    have h (u : T) : w u * boundaryWeight tw d (.inr (e,i,j)) u / terminalD r u =
        (if u = e.val.1 then w u * leftRatio j / terminalD r u else 0) -
        (if u = e.val.2 then w u * (sideSign tw d e * rightRatio j) / terminalD r u else 0) := by
      unfold boundaryWeight
      simp only [eq_comm (a := u) (b := e.val.1), eq_comm (a := u) (b := e.val.2)]
      by_cases hl : e.val.1 = u <;> by_cases hr : e.val.2 = u <;> simp_all <;> ring
    change lineValue tw d (terminalVoltage tw d a) a e i (j.val+1) =
      localGreen a e i (j.val+1) + ∑ u, w u * boundaryWeight tw d (.inr (e,i,j)) u / terminalD r u
    simp_rw [h]
    simp only [Finset.sum_sub_distrib, Fintype.sum_ite_eq', lineValue, terminalVoltage, leftRatio, rightRatio,
      Nat.add_sub_add_right, w]
    ring

theorem localPart_flip (d : Side T) (a x : Base T m r) :
    localPart a x = polarity (sheetFlip d a x) * localPart a x := by
  cases x with
  | inl x => simp [localPart]
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    cases a with
    | inl y => simp [localPart,localGreen]
    | inr y =>
      obtain ⟨e',i',j'⟩ := y
      by_cases h : e = e' <;> simp [localPart, localGreen, h, sheetFlip, onSide]

theorem weight_product_flip (d : Side T) (a x : Base T m r) (u : T) :
    boundaryWeight true d a u * boundaryWeight true d x u = polarity (sheetFlip d a x) *
      (boundaryWeight false d a u * boundaryWeight false d x u) := by
  by_cases ha : touches a u
  · by_cases hx : touches x u
    · rw [weight_flip, weight_flip, ← common_terminal_flip d a x u ha hx, polarity_xor]; ring
    · simp [weight_off _ _ _ _ hx]
  · simp [weight_off _ _ _ _ ha]

theorem green_flip [Fintype T] (d : Side T) (a x : Base T m r) :
    signedGreen true d a x = polarity (sheetFlip d a x) * signedGreen false d a x := by
  rw [green_expansion, green_expansion, mul_add, Finset.mul_sum, ← localPart_flip]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [weight_product_flip]
  ring

/-- Concrete sign changes align both the full grounded Green entries and
adjacency, vertex fiber by vertex fiber. -/
def expandedAlignment [Fintype T] (d : Side T) : Alignment (expanded T m r)
    (signing false d) (signing true d) (signedGreen false d) (signedGreen true d) where
  flip := sheetFlip d
  diag := sheetFlip_diag d
  symm := sheetFlip_comm d
  edge := edge_flip d
  green := green_flip d

theorem expanded_equivalent [Fintype T] (hr : 0 < r) (hm : m = continuant (r+1)) (d : Side T) :
    Equivalent (jointLabels (cone (signedLift (expanded T m r) (signing false d))))
      (jointLabels (cone (signedLift (expanded T m r) (signing true d)))) :=
  cones_equivalent _ _ _ _ _ (signedGreen_solve hr hm false d) (signedGreen_solve hr hm true d) (expandedAlignment d)

end JointForest
