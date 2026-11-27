module

public import SolvedProblems.JointForestSchur
public import SolvedProblems.JointForestAlignment

@[expose] public section

namespace JointForest

variable {T : Type*} [LinearOrder T] {m r : ℕ}

/-- Terminal support of a row of the interpolation matrix. -/
def touches (x : Base T m r) (u : T) : Prop :=
  match x with
  | .inl v => u = v
  | .inr (e,_,_) => u = e.val.1 ∨ u = e.val.2

instance (x : Base T m r) (u : T) : Decidable (touches x u) := by
  cases x <;> unfold touches <;> infer_instance

def onSide (d : Side T) : Base T m r → Bool
  | .inl _ => false
  | .inr (e,_,_) => decide (e = d)

def sheetFlip (d : Side T) (x y : Base T m r) : Bool :=
  match x,y with
  | .inl u, .inl v => decide (s(u,v) = s(d.val.1,d.val.2))
  | _,_ => (onSide d x ^^ onSide d y) && decide (touches x d.val.2 ∧ touches y d.val.2)

def terminalFlip (d : Side T) (x : Base T m r) (u : T) : Bool := onSide d x && decide (u = d.val.2)

theorem sheetFlip_diag (d : Side T) (x : Base T m r) : sheetFlip d x x = false := by
  cases x with
  | inl u => simp [sheetFlip]; grind [ne_of_lt d.property]
  | inr x => simp [sheetFlip]

theorem sheetFlip_comm (d : Side T) (x y : Base T m r) : sheetFlip d x y = sheetFlip d y x := by
  cases x <;> cases y <;> simp only [sheetFlip, Bool.xor_comm, and_comm, Sym2.eq_swap]

/-- An object touching both endpoints of the distinguished side must be an
interior on that side: distinct sides share at most one terminal. -/
theorem onSide_of_both (d : Side T) (x : Base T m r) (hl : touches x d.val.1) (hr : touches x d.val.2) :
    onSide d x = true := by
  cases x with
  | inl v => exact (ne_of_lt d.property (hl.trans hr.symm)).elim
  | inr p =>
    obtain ⟨e,i,j⟩ := p
    have h : e = d := by
      apply (side_endpoints e d).mp
      apply Sym2.eq_iff.mpr
      rcases hl with hl | hl <;> rcases hr with hr | hr <;> grind [ne_of_lt d.property]
    simp [onSide, h]

theorem touch_of_onSide (d : Side T) (x : Base T m r) (hx : onSide d x = true) (u : T) :
    touches x u ↔ u = d.val.1 ∨ u = d.val.2 := by
  cases x with
  | inl v => cases hx
  | inr p =>
    obtain ⟨e,i,j⟩ := p
    have he : e = d := by simpa [onSide] using hx
    cases he; rfl

theorem common_terminal_flip (d : Side T) (x y : Base T m r) (u : T)
    (hx : touches x u) (hy : touches y u) :
    (terminalFlip d x u ^^ terminalFlip d y u) = sheetFlip d x y := by
  have local_rule (x y : Base T m r) (hx : touches x u) (hy : touches y u) :
      (terminalFlip d x u ^^ terminalFlip d y u) =
      ((onSide d x ^^ onSide d y) && decide (touches x d.val.2 ∧ touches y d.val.2)) := by
    by_cases hu : u = d.val.2
    · subst u; simp [terminalFlip, hx,hy]
    · have imp (x y : Base T m r) (hx : touches x u) (hy : touches y u) (hs : onSide d x = true)
          (hr : touches y d.val.2) : onSide d y = true := by
        have hl := ((touch_of_onSide d x hs u).mp hx).resolve_right hu
        exact onSide_of_both d y (hl ▸ hy) hr
      by_cases hc : touches x d.val.2 ∧ touches y d.val.2
      · have hxy : onSide d x = onSide d y := by
          cases h1 : onSide d x <;> cases h2 : onSide d y <;>
            first | rfl | exact (by have := imp x y hx hy h1 hc.2; simp_all) |
              exact (by have := imp y x hy hx h2 hc.1; simp_all)
        simp [terminalFlip, hu, hxy]
      · simp [terminalFlip, hu, hc]
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      have h : v = w := (show u = v from hx).symm.trans hy
      rw [← h, sheetFlip_diag]; simp
    | inr y => exact local_rule _ _ hx hy
  | inr x => cases y <;> exact local_rule _ _ hx hy

theorem weight_off (tw : Bool) (d : Side T) (x : Base T m r) (u : T) (h : ¬touches x u) :
    boundaryWeight tw d x u = 0 := by
  cases x with
  | inl v => simpa [boundaryWeight, touches] using h
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    have hl : e.val.1 ≠ u := fun h' => h (Or.inl h'.symm)
    have hr : e.val.2 ≠ u := fun h' => h (Or.inr h'.symm)
    simp [boundaryWeight, hl,hr]

theorem weight_flip (d : Side T) (x : Base T m r) (u : T) :
    boundaryWeight true d x u = polarity (terminalFlip d x u) * boundaryWeight false d x u := by
  cases x with
  | inl v => simp [boundaryWeight, terminalFlip, onSide]
  | inr x =>
    obtain ⟨e,i,j⟩ := x
    by_cases he : e = d
    · subst e
      by_cases hu : u = d.val.2
      · subst u; simp [boundaryWeight, terminalFlip, onSide, sideSign, ne_of_lt d.property]
      · simp [boundaryWeight, terminalFlip, onSide, hu, Ne.symm hu]
    · simp [boundaryWeight, terminalFlip, onSide, sideSign, he]

/-- The same exchange aligns the signed covariance and the lift adjacency at
an incident pair, including the direct distinguished terminal edge. -/
theorem edge_flip (d : Side T) (x y : Base T m r) (h : (expanded T m r).Adj x y) :
    (signing true d).neg x y = ((signing false d).neg x y ^^ sheetFlip d x y) := by
  have ti (u : T) (e : Side T) (i : Fin m) (j : Fin r) :
      (signing true d).neg (.inl u) (.inr (e,i,j)) =
      ((signing false d).neg (.inl u) (.inr (e,i,j)) ^^ sheetFlip d (.inl u) (.inr (e,i,j))) := by
    by_cases he : e = d
    · subst e; by_cases hu : u = d.val.2 <;> simp [signing, signBit, sheetFlip, onSide, touches, hu, eq_comm]
    · simp [signing, signBit, sheetFlip, onSide, touches, he]
  cases x with
  | inl u =>
    cases y with
    | inl v => simp [signing, signBit, sheetFlip]
    | inr p => obtain ⟨e,i,j⟩ := p; exact ti ..
  | inr p =>
    obtain ⟨e,i,j⟩ := p
    cases y with
    | inl v =>
      rw [(signing true d).symm, (signing false d).symm, sheetFlip_comm]; exact ti ..
    | inr p =>
      obtain ⟨e',i',j'⟩ := p
      have he : e = e' := h.2.elim (fun ht => ht.1) (fun ht => ht.1.symm)
      subst e'
      simp [signing, signBit, sheetFlip, onSide]

end JointForest
