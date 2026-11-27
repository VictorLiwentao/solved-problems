module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.List.Pairwise
public import Mathlib.Tactic.Push

@[expose] public section

namespace ChainWords

/-- An ascent is weak and a descent is strict. Injective vertex labels make the
two labels distinct on every cover and inside every linear extension. -/
def color {α : Type*} (label : α → ℕ) (x y : α) : Bool := decide (label x ≤ label y)

/-- The adjacent comparison word encodes exactly the descent set of a word. -/
def descWord {α : Type*} (label : α → ℕ) : List α → List Bool
  | x :: y :: l => color label x y :: descWord label (y :: l)
  | _ => []

theorem color_trans {α : Type*} (label : α → ℕ) {x y z : α} {b : Bool}
    (h : color label x y = b) (h' : color label y z = b) : color label x z = b := by
  cases b <;> simp [color] at * <;> omega

theorem color_split {α : Type*} (label : α → ℕ) (x y z : α) :
    color label x y = color label x z ∨ color label y z = color label x z := by
  by_cases h : color label x y = color label y z
  · exact Or.inl (color_trans label rfl h.symm).symm
  · cases h₁ : color label x y <;> cases h₂ : color label y z <;> cases h₃ : color label x z <;> simp_all

theorem desc_take {α : Type*} (label : α → ℕ) (n : ℕ) (l : List α) :
    descWord label (l.take n) = (descWord label l).take (n-1) := by
  induction n generalizing l with
  | zero => simp [descWord]
  | succ n ih =>
    cases n with
    | zero => cases l <;> simp [descWord]
    | succ n =>
      rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
      · simp [descWord]
      · simp [descWord]
      · simpa [descWord] using congrArg (List.cons (color label x y)) (ih (y :: l))

theorem desc_drop {α : Type*} (label : α → ℕ) (n : ℕ) (l : List α) :
    descWord label (l.drop n) = (descWord label l).drop n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp [descWord]
    · simp [descWord]
    · simpa [descWord] using ih (y :: l)

def Run {α : Type*} (label : α → ℕ) (b : Bool) (l : List α) : Prop :=
  l.Pairwise fun x y => color label x y = b

theorem run_iff {α : Type*} (label : α → ℕ) (b : Bool) (l : List α) :
    Run label b l ↔ ∀ s ∈ descWord label l, s = b := by
  induction l with
  | nil => simp [Run, descWord]
  | cons x l ih =>
    rcases l with _ | ⟨y, l⟩
    · simp [Run, descWord]
    · let _ : IsTrans α (fun x y => color label x y = b) := ⟨fun _ _ _ => color_trans label⟩
      change (x :: y :: l).Pairwise (fun x y => color label x y = b) ↔
        ∀ s ∈ color label x y :: descWord label (y :: l), s = b
      rw [List.pairwise_cons_cons_iff_of_trans, List.forall_mem_cons]
      exact and_congr Iff.rfl ih

inductive Cuts {α : Type*} (label : α → ℕ) : List Bool → List α → Prop where
  | nil : Cuts label [] []
  | cons {s l r b} : Run label b l → Cuts label s r → Cuts label (b :: s) (l ++ r)

/-- Block cuts depend only on the length and the descent set. Empty blocks are allowed. -/
theorem cuts_transfer {α β : Type*} {f : α → ℕ} {g : β → ℕ} {s l}
    (hc : Cuts f s l) (r : List β) (hn : l.length = r.length) (hd : descWord f l = descWord g r) :
    Cuts g s r := by
  induction hc generalizing r with
  | nil =>
    have hr : r = [] := List.length_eq_zero_iff.mp hn.symm
    subst r
    exact .nil
  | @cons s l t b hl ht ih =>
    have h₁ : descWord f l = descWord g (r.take l.length) := by
      rw [desc_take, ← hd, ← desc_take]
      simp
    have h₂ : descWord f t = descWord g (r.drop l.length) := by
      rw [desc_drop, ← hd, ← desc_drop]
      simp
    have hl' : Run g b (r.take l.length) := (run_iff ..).2 (h₁ ▸ (run_iff ..).1 hl)
    have ht' : Cuts g s (r.drop l.length) := ih _ (by simp at hn ⊢; omega) h₂
    simpa using Cuts.cons hl' ht'

/-- The descent set is indexed by the size of the poset, as in the homogeneous
fundamental basis. The list visits every vertex exactly once in a linear extension. -/
def IsExtension {α : Type*} [PartialOrder α] (D : Set α) (l : List α) : Prop :=
  l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ D) ∧ l.Pairwise (fun x y => ¬ y < x)

def fundamentalSupport {α : Type*} [PartialOrder α] (label : α → ℕ) : Set (ℕ × List Bool) :=
  {c | ∃ l : List α, IsExtension Set.univ l ∧ c = (l.length, descWord label l)}

/-- Ordered selected covers give exactly a subsequence of cover colors on a
saturated chain. The unselected segments are the intervals between successive covers. -/
def Above {α : Type*} [PartialOrder α] (label : α → ℕ) : List Bool → α → Prop
  | [], _ => True
  | c :: w, x => ∃ a b, x ≤ a ∧ a ⋖ b ∧ color label a b = c ∧ Above label w b

def language {α : Type*} [PartialOrder α] (label : α → ℕ) : Set (List Bool) :=
  {w | ∃ x, Above label w x}

theorem above_mono {α : Type*} [PartialOrder α] (label : α → ℕ) {x y : α} (h : x ≤ y)
    (w : List Bool) : Above label w y → Above label w x := by
  cases w with
  | nil => exact fun _ => trivial
  | cons c w =>
    rintro ⟨a,b,hy,he,hc,hw⟩
    exact ⟨a,b,h.trans hy,he,hc,hw⟩

/-- At least one cover in a comparable interval has the same comparison of labels
as its endpoints. -/
theorem cover_color {α : Type*} [Fintype α] [PartialOrder α] (label : α → ℕ)
    {x y : α} (hlt : x < y) :
    ∃ a b, x ≤ a ∧ a ⋖ b ∧ b ≤ y ∧ color label a b = color label x y := by
  classical
  let _ := Fintype.toLocallyFiniteOrder (α := α)
  induction lt_iff_transGen_covBy.mp hlt with
  | single h => exact ⟨_,_,le_rfl,h,le_rfl,rfl⟩
  | @tail y z path step ih =>
    rcases color_split label x y z with h | h
    · obtain ⟨a,b,ha,he,hb,hc⟩ := ih (lt_iff_transGen_covBy.mpr path)
      exact ⟨a,b,ha,he,hb.trans step.le,hc.trans h⟩
    · exact ⟨y,z,(lt_iff_transGen_covBy.mpr path).le,step,le_rfl,h⟩

end ChainWords
