module

public import SolvedProblems.OrdinalCubeLogic
public import Mathlib.Order.WellFounded

@[expose] public section

namespace OrdinalCube

variable {I : Type v} {X : Type u} [LinearOrder I]
variable (bit : X → I → Bool) (C : X → Prop)

/-- This coordinate separates two points of the cell. -/
def Splits (i : I) : Prop := ∃ x y, C x ∧ C y ∧ bit x i ≠ bit y i

def First (i : I) : Prop := Splits bit C i ∧ ∀ j < i, ¬ Splits bit C j

theorem first_unique {i j : I} (hi : First bit C i) (hj : First bit C j) : i = j := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact False.elim (hj.2 i h hi.1)
  · rfl
  · exact False.elim (hi.2 j h hj.1)

variable [TruthValues]

/-- Choose the bit by testing the uniquely specified first splitting coordinate.
This definition does not select a coordinate or a representative from each cell. -/
def firstBit (x : X) : Bool := decide (∃ i, First bit C i ∧ bit x i = true)

theorem firstBit_eq {i : I} (hi : First bit C i) (x : X) :
    firstBit bit C x = bit x i := by
  cases hb : bit x i with
  | false =>
    apply decide_eq_false
    rintro ⟨j,hj,h⟩
    exact Bool.noConfusion (hb.symm.trans (first_unique bit C hi hj ▸ h))
  | true => exact decide_eq_true ⟨i,hi,hb⟩

theorem has_first (wf : WellFounded ((· < ·) : I → I → Prop))
    (h : ∃ i, Splits bit C i) : ∃ i, First bit C i := by
  obtain ⟨i,hi⟩ := h
  induction i using wf.induction with
  | h i ih =>
    rcases truthCases (∃ j, j < i ∧ Splits bit C j) with earlier | earlier
    · obtain ⟨j,hj,hs⟩ := earlier
      exact ih j hj hs
    · exact ⟨i,hi,fun j hj hs => earlier ⟨j,hj,hs⟩⟩

omit [LinearOrder I] [TruthValues] in
private theorem two_values {i : I} (h : Splits bit C i) (b : Bool) :
    ∃ x, C x ∧ bit x i = b := by
  obtain ⟨x,y,hx,hy,hd⟩ := h
  cases hxb : bit x i <;> cases hyb : bit y i <;> cases b <;>
    first | exact ⟨x,hx,hxb⟩ | exact ⟨y,hy,hyb⟩ | exact False.elim (hd (hxb.trans hyb.symm))

/-- A cell contributes one child if its coordinates are constant, two otherwise. -/
def width : ℕ := if ∃ i, Splits bit C i then 2 else 1

omit [LinearOrder I] in
private theorem width_options : width bit C = 1 ∨ width bit C = 2 := by
  unfold width; split <;> simp

omit [LinearOrder I] in
private theorem no_split {i : I} (w : width bit C = 1) : ¬ Splits bit C i := by
  intro h
  have hs : ∃ j, Splits bit C j := ⟨i,h⟩
  simp [width,hs] at w

private theorem no_digit (w : width bit C = 1) (x : X) : firstBit bit C x = false := by
  apply decide_eq_false
  exact fun ⟨_,h,_⟩ => no_split bit C w h.1

private theorem digit_lt (x : X) : (firstBit bit C x).toNat < width bit C := by
  rcases width_options bit C with h|h
  · rw [no_digit bit C h, h]; decide
  · rw [h]; cases firstBit bit C x <;> decide

private theorem digits_onto (wf : WellFounded ((· < ·) : I → I → Prop))
    (inh : ∃ x, C x) (k : ℕ) (hk : k < width bit C) : ∃ x, C x ∧ (firstBit bit C x).toNat = k := by
  rcases truthCases (∃ i, Splits bit C i) with hs | hs
  · obtain ⟨i,hi⟩ := has_first bit C wf hs
    simp [width,hs] at hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · obtain ⟨x,hx,hb⟩ := two_values bit C hi.1 false
      exact ⟨x,hx,by rw [firstBit_eq bit C hi,hb]; rfl⟩
    · obtain ⟨x,hx,hb⟩ := two_values bit C hi.1 true
      exact ⟨x,hx,by rw [firstBit_eq bit C hi,hb]; rfl⟩
  · obtain ⟨x,hx⟩ := inh
    have h : width bit C = 1 := by simp [width,hs]
    have : k = 0 := by omega
    exact ⟨x,hx,by rw [no_digit bit C h,this]; rfl⟩

/-- Once a cell splits at i, each nonsingleton half splits at its own first difference. -/
def half (i : I) (b : Bool) (x : X) : Prop := C x ∧ bit x i = b

def arity (i : I) : ℕ := width bit (half bit C i false) + width bit (half bit C i true)

/-- The children are numbered consecutively, from the false half to the true half. -/
def rank (i : I) (x : X) : ℕ :=
  let b := bit x i
  (if b then width bit (half bit C i false) else 0) + (firstBit bit (half bit C i b) x).toNat

theorem rank_lt (i : I) (x : X) : rank bit C i x < arity bit C i := by
  have h₀ := digit_lt bit (half bit C i false) x
  have h₁ := digit_lt bit (half bit C i true) x
  unfold arity rank
  cases h : bit x i <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega

theorem rank_bit {i : I} {x y : X} (h : rank bit C i x = rank bit C i y) : bit x i = bit y i := by
  have hx := digit_lt bit (half bit C i false) x
  have hy := digit_lt bit (half bit C i false) y
  unfold rank at h
  cases ha : bit x i <;> cases hb : bit y i <;> simp_all <;> omega

omit [LinearOrder I] in
theorem arity_options (i : I) : arity bit C i = 2 ∨ arity bit C i = 3 ∨ arity bit C i = 4 := by
  have h₀ := width_options bit (half bit C i false)
  have h₁ := width_options bit (half bit C i true)
  unfold arity; omega

theorem rank_onto (wf : WellFounded ((· < ·) : I → I → Prop)) {i : I}
    (hs : Splits bit C i) (k : ℕ) (hk : k < arity bit C i) : ∃ x, C x ∧ rank bit C i x = k := by
  by_cases h : k < width bit (half bit C i false)
  · obtain ⟨x,⟨hx,hb⟩,hd⟩ := digits_onto bit (half bit C i false) wf
      (two_values bit C hs false) k h
    exact ⟨x,hx,by simpa [rank,hb] using hd⟩
  · have h' : k - width bit (half bit C i false) < width bit (half bit C i true) := by
      unfold arity at hk; omega
    obtain ⟨x,⟨hx,hb⟩,hd⟩ := digits_onto bit (half bit C i true) wf
      (two_values bit C hs true) _ h'
    exact ⟨x,hx,by simp [rank,hb,hd]; omega⟩

/-- If a splitting cell has two children, both are singletons. -/
theorem rank_injective_two (embed : Function.Injective bit) {i : I} (two : arity bit C i = 2)
    {x y : X} (hx : C x) (hy : C y) (eq : rank bit C i x = rank bit C i y) : x = y := by
  have same := rank_bit bit C eq
  have h₀ := width_options bit (half bit C i false)
  have h₁ := width_options bit (half bit C i true)
  unfold arity at two
  have hw : width bit (half bit C i (bit x i)) = 1 := by cases bit x i <;> omega
  apply embed
  funext j
  apply Decidable.by_contra
  intro hn
  exact no_split bit _ hw ⟨x,y,⟨hx,rfl⟩,⟨hy,same.symm⟩,hn⟩

end OrdinalCube
