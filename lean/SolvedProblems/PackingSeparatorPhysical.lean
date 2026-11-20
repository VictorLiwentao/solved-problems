module

public import SolvedProblems.PackingSeparatorModel

@[expose] public section

namespace PackingSeparator

/-- The physical position of local slot i in zero-based window w. -/
def coord (k m w i : Nat) := w*(k-m)+i

/-- Reflexive transitive closure of the comparisons within the given windows,
directly on physical positions. -/
inductive Physical {k m} (p : Pattern k m) (j x : Nat) : Nat → Prop
  | refl : Physical p j x x
  | step {w i h} : Physical p j x (coord k m w i) → w < j → i < k → h < k →
      p.rank i ≤ p.rank h → Physical p j x (coord k m w h)

private theorem transBelow {k m j w r v s u t} {p : Pattern k m}
    (h : Below p j w r v s) (h' : Below p j v s u t) : Below p j w r u t := by
  induction h' with
  | refl => exact h
  | rise _ le ok ih => exact .rise ih le ok
  | right _ overlap next ih => exact .right ih overlap next
  | left _ overlap ih => exact .left ih overlap

private theorem validWindow {k m j w r v s} {p : Pattern k m}
    (start : w < j) (path : Below p j w r v s) : v < j := by
  induction path <;> omega

private theorem aliasRight {k m j} (p : Pattern k m) (d w i h : Nat) (valid : w+d < j)
    (hi : i < k) (hh : h < k) (eq : coord k m w i = coord k m (w+d) h) :
    Below p j w (p.rank i) (w+d) (p.rank h) ∧ Below p j (w+d) (p.rank h) w (p.rank i) := by
  induction d generalizing h with
  | zero =>
    have ih : i=h := by simpa [coord] using eq
    subst h
    exact ⟨.refl,.refl⟩
  | succ d ih =>
    have ordered : w*(k-m) ≤ (w+d)*(k-m) := Nat.mul_le_mul_right _ (by omega)
    have same : coord k m w i = coord k m (w+d) (k-m+h) := by
      simpa only [coord,Nat.add_succ,Nat.succ_mul,Nat.add_assoc] using eq
    have ih' := same
    unfold coord at ih'
    have shared : h < m := by have := p.short; omega
    have inside : k-m+h < k := by omega
    obtain ⟨forward,back⟩ := ih (k-m+h) (by omega) inside same
    exact ⟨.right forward shared valid, transBelow (.left .refl shared) back⟩

private theorem alias {k m j w v i h} (p : Pattern k m) (hw : w<j) (hv : v<j)
    (hi : i<k) (hh : h<k) (eq : coord k m w i = coord k m v h) :
    Below p j w (p.rank i) v (p.rank h) := by
  rcases Nat.le_total w v with order|order
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le order
    exact (aliasRight p d w i h hv hi hh eq).1
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le order
    exact (aliasRight p d v h i hw hh hi eq.symm).2

private theorem toPhysical {k m j w r v s} {p : Pattern k m} (path : Below p j w r v s) (hw : w<j)
    (i : Nat) (hi : i<k) (ir : p.rank i = r) :
    ∀ h < k, p.rank h = s → Physical p j (coord k m w i) (coord k m v h) := by
  induction path with
  | refl =>
    intro h hh eq
    have := p.distinct i hi h hh (ir.trans eq.symm)
    subst h; exact .refl
  | @rise v s t path le ht ih =>
    intro h hh eq
    obtain ⟨u,hu,eu⟩ := p.onto s (by omega)
    exact .step (ih u hu eu) (validWindow hw path) hu hh (by omega)
  | @right v t _ ht _ ih =>
    intro h hh eq
    have same := p.distinct h hh t (by have := p.short; omega) eq
    subst h
    have physical := ih (k-m+t) (by have := p.short; omega) rfl
    simpa only [coord,Nat.succ_mul,Nat.add_assoc] using physical
  | @left v t _ ht ih =>
    intro h hh eq
    have same := p.distinct h hh (k-m+t) (by have := p.short; omega) eq
    subst h
    have physical := ih t (by have := p.short; omega) rfl
    simpa only [coord,Nat.succ_mul,Nat.add_assoc] using physical

private theorem fromPhysical {k m j w i pos} {p : Pattern k m} (hw : w<j) (hi : i<k)
    (path : Physical p j (coord k m w i) pos) :
    ∀ v < j, ∀ h < k, pos = coord k m v h → Below p j w (p.rank i) v (p.rank h) := by
  induction path with
  | refl =>
    intro v hv h hh eq
    exact alias p hw hv hi hh eq
  | @step z a b _ hz ha hb le ih =>
    intro v hv h hh eq
    exact transBelow (.rise (ih z hz a ha rfl) le (p.bounded b hb)) (alias p hz hv hb hh eq)

/-- Comparisons of window ranks agree with the actual transitive closure on
physical positions, including positions having more than one home. -/
theorem physical_iff {k m j} (p : Pattern k m) (w v : Fin j) (i h : Fin k) :
    Physical p j (coord k m w.val i.val) (coord k m v.val h.val) ↔
      LEPos p (w,⟨p.rank i.val,p.bounded _ i.isLt⟩) (v,⟨p.rank h.val,p.bounded _ h.isLt⟩) := by
  exact ⟨fun path => fromPhysical w.isLt i.isLt path v.val v.isLt h.val h.isLt rfl,
    fun path => toPhysical path w.isLt i.val i.isLt rfl h.val h.isLt rfl⟩

end PackingSeparator
