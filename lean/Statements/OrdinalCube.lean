module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.WellFounded

@[expose] public section

namespace OrdinalCube

/-- Classical truth values are available in ZF. Keeping this parameter explicit
allows Lean to audit the combinatorial construction independently of choice. -/
class TruthValues where
  truth (p : Prop) : Decidable p

scoped instance (priority := 10) (p : Prop) [TruthValues] : Decidable p := TruthValues.truth p

theorem truthCases [TruthValues] (p : Prop) : p ∨ ¬ p := @Decidable.em p (TruthValues.truth p)

end OrdinalCube

namespace OrdinalCube

/-- A permutation of the points preserving and reflecting the directed edges. -/
def Preserves {X : Type u} (R : X → X → Prop) (f : Equiv.Perm X) : Prop :=
  ∀ x y, R (f x) (f y) ↔ R x y

/-- Each external point has constant incoming and outgoing adjacency on a module. -/
def IsModule {X : Type u} (R : X → X → Prop) (M : X → Prop) : Prop :=
  ∀ z, ¬ M z → ∀ x, M x → ∀ y, M y →
    (R z x ↔ R z y) ∧ (R x z ↔ R y z)

/-- Substituting arbitrary nonempty graphs into the vertices of a directed path. -/
def PathPartition {X : Type u} (R : X → X → Prop) {n : ℕ} (child : X → Fin n) : Prop :=
  ∀ x y, child x ≠ child y → (R x y ↔ (child x).val + 1 = (child y).val)

private def view {n : ℕ} (c a : Fin n) : Bool × Bool :=
  (decide (c.val + 1 = a.val), decide (a.val + 1 = c.val))

private def PrimeHit {n : ℕ} (hit : Fin n → Bool) : Prop :=
  (∃ a b, hit a = true ∧ hit b = true ∧ a ≠ b) → (∃ c, hit c = false) →
    ∃ c a b, hit c = false ∧ hit a = true ∧ hit b = true ∧ view c a ≠ view c b

private theorem path_prime {n} (hn : n = 3 ∨ n = 4) (hit : Fin n → Bool) : PrimeHit hit := by
  rcases hn with rfl | rfl
  · let pattern (a b c : Bool) (i : Fin 3) := if i = 0 then a else if i = 1 then b else c
    have check : ∀ a b c : Bool, PrimeHit (pattern a b c) := by unfold PrimeHit; decide
    have restore : pattern (hit 0) (hit 1) (hit 2) = hit := by
      funext ⟨i,hi⟩
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> rfl
    exact restore ▸ check (hit 0) (hit 1) (hit 2)
  · let pattern (a b c d : Bool) (i : Fin 4) :=
      if i = 0 then a else if i = 1 then b else if i = 2 then c else d
    have check : ∀ a b c d : Bool, PrimeHit (pattern a b c d) := by unfold PrimeHit; decide
    have restore : pattern (hit 0) (hit 1) (hit 2) (hit 3) = hit := by
      funext ⟨i,hi⟩
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    exact restore ▸ check (hit 0) (hit 1) (hit 2) (hit 3)

private theorem other_views {n} (hn : n = 3 ∨ n = 4) (c : Fin n) :
    ∃ a b, c ≠ a ∧ c ≠ b ∧ view c a ≠ view c b := by
  revert c
  rcases hn with rfl | rfl <;> decide

private theorem module_views {X : Type u} {n} {R : X → X → Prop} {child : X → Fin n}
    (cross : PathPartition R child) {M : X → Prop} (modl : IsModule R M)
    {z x y : X} (hz : ¬ M z) (hx : M x) (hy : M y)
    (hcx : child z ≠ child x) (hcy : child z ≠ child y) :
    view (child z) (child x) = view (child z) (child y) := by
  obtain ⟨hin, hout⟩ := modl z hz x hx y hy
  have hin' := (cross z x hcx).symm.trans <| hin.trans (cross z y hcy)
  have hout' := (cross x z hcx.symm).symm.trans <| hout.trans (cross y z hcy.symm)
  simp only [view, propext hin', propext hout']

/-- Every proper module lies in one child. No order or representatives of the
points inside a child enter the argument. -/
theorem properModule_oneChild {X : Type u} {n} {R : X → X → Prop} {child : X → Fin n}
    [TruthValues] (hn : n = 3 ∨ n = 4) (onto : Function.Surjective child)
    (cross : PathPartition R child) {M : X → Prop} (modl : IsModule R M)
    (proper : ∃ z, ¬ M z) (x y : X) (hx : M x) (hy : M y) : child x = child y := by
  apply Decidable.by_contra
  intro hne
  let hit (i : Fin n) := decide (∃ t, M t ∧ child t = i)
  have mem (i : Fin n) : hit i = true ↔ ∃ t, M t ∧ child t = i := decide_eq_true_iff
  rcases truthCases (∀ i, hit i = true) with hall | hall
  · obtain ⟨z, hz⟩ := proper
    obtain ⟨a,b,ha,hb,hv⟩ := other_views hn (child z)
    obtain ⟨u, hu, rfl⟩ := (mem a).mp (hall a)
    obtain ⟨v, hw, rfl⟩ := (mem b).mp (hall b)
    exact hv (module_views cross modl hz hu hw ha hb)
  · have missing : ∃ i, hit i = false := by
      apply Decidable.by_contra
      intro no
      apply hall
      intro i
      cases hi : hit i with
      | false => exact False.elim (no ⟨i,hi⟩)
      | true => rfl
    obtain ⟨c,a,b,hc,ha,hb,hv⟩ := path_prime hn hit
      ⟨_,_,(mem _).mpr ⟨x,hx,rfl⟩,(mem _).mpr ⟨y,hy,rfl⟩,hne⟩ missing
    obtain ⟨z,rfl⟩ := onto c
    obtain ⟨u,hu,rfl⟩ := (mem a).mp ha
    obtain ⟨v,hw,rfl⟩ := (mem b).mp hb
    have hz : ¬ M z := fun hz => by have := (mem _).mpr ⟨z,hz,rfl⟩; simp_all
    apply hv
    exact module_views cross modl hz hu hw (fun e => by simp_all) (fun e => by simp_all)

private theorem child_module {X : Type u} {n} {R : X → X → Prop} {child : X → Fin n}
    (cross : PathPartition R child) (i : Fin n) : IsModule R (fun x => child x = i) := by
  intro z hz x hx y hy
  have hzx : child z ≠ child x := fun e => hz (e.trans hx)
  have hzy : child z ≠ child y := fun e => hz (e.trans hy)
  rw [cross z x hzx, cross z y hzy, cross x z hzx.symm, cross y z hzy.symm, hx, hy]
  exact ⟨Iff.rfl, Iff.rfl⟩

private theorem preimage_module {X : Type u} {R : X → X → Prop} {M : X → Prop}
    (f : Equiv.Perm X) (hf : Preserves R f) (hM : IsModule R M) :
    IsModule R (fun x => M (f x)) := by
  intro z hz x hx y hy
  obtain ⟨a,b⟩ := hM _ hz _ hx _ hy
  exact ⟨(hf _ _).symm.trans (a.trans (hf _ _)), (hf _ _).symm.trans (b.trans (hf _ _))⟩

private theorem child_reflects {X : Type u} {n} {R : X → X → Prop} {child : X → Fin n}
    [TruthValues] (hn : n = 3 ∨ n = 4) (onto : Function.Surjective child)
    (cross : PathPartition R child) (f : Equiv.Perm X) (hf : Preserves R f) (x y : X)
    (h : child (f x) = child (f y)) : child x = child y := by
  let i := child (f y)
  obtain ⟨a,b,ha,_,_⟩ := other_views hn i
  obtain ⟨w,hw⟩ := onto a
  exact properModule_oneChild hn onto cross (preimage_module f hf (child_module cross i))
    ⟨f.symm w, fun e => ha (by simpa [hw, i] using e.symm)⟩ x y h rfl

/-- A directed path has a unique source and each successive index is forced.
It suffices that same-child membership be preserved and reflected. -/
theorem child_fixed_of_partition {X : Type u} {n} {R : X → X → Prop} {child : X → Fin n}
    (onto : Function.Surjective child) (cross : PathPartition R child)
    (f : Equiv.Perm X) (hf : Preserves R f)
    (same : ∀ x y, child (f x) = child (f y) ↔ child x = child y) (x : X) :
    child (f x) = child x := by
  have ind (k : ℕ) : ∀ x, (child x).val = k → child (f x) = child x := by
    induction k with
    | zero =>
      intro x hx
      apply Fin.ext
      by_contra h
      have hy : 0 < (child (f x)).val := by omega
      obtain ⟨y,hy'⟩ := onto ⟨(child (f x)).val - 1, by have := (child (f x)).isLt; omega⟩
      have e : (child (f (f.symm y))).val + 1 = (child (f x)).val := by simp [hy']; omega
      have hd : child (f (f.symm y)) ≠ child (f x) := fun h => by rw [h] at e; omega
      have hd' := fun h => hd ((same _ _).mpr h)
      have hr := (cross _ _ hd').mp ((hf _ _).mp ((cross _ _ hd).mpr e))
      omega
    | succ k ih =>
      intro x hx
      obtain ⟨y, hy⟩ := onto ⟨k, by have := (child x).isLt; omega⟩
      have hy' := congrArg Fin.val hy
      have hd : child y ≠ child x := fun h => by rw [h] at hy'; simp at hy'; omega
      have hd' := fun h => hd ((same _ _).mp h)
      have e := (cross _ _ hd').mp ((hf y x).mpr ((cross _ _ hd).mpr (by simp_all)))
      rw [ih _ hy'] at e
      exact Fin.ext (e.symm.trans (by rw [show (child y).val = k from hy', hx]))
  exact ind _ x rfl

/-- In a substitution on three or four path vertices, an automorphism fixes every
child setwise, irrespective of the internal directed graphs. -/
theorem path_children_fixed {X : Type u} {n} {R : X → X → Prop} {child : X → Fin n}
    [TruthValues] (hn : n = 3 ∨ n = 4) (onto : Function.Surjective child)
    (cross : PathPartition R child) (f : Equiv.Perm X) (hf : Preserves R f) (x : X) :
    child (f x) = child x := by
  have hi : Preserves R f.symm := fun x y => by simpa using (hf (f.symm x) (f.symm y)).symm
  apply child_fixed_of_partition onto cross f hf _ x
  intro a b
  exact ⟨child_reflects hn onto cross f hf a b, fun h => by
    simpa using child_reflects hn onto cross f.symm hi (f a) (f b) (by simpa using h)⟩

end OrdinalCube

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

namespace OrdinalCube

variable {I : Type v} {X : Type u} [LinearOrder I] [TruthValues]

/-- The cell of x at coordinate i is determined by all its earlier child numbers.
This also defines limit cells, by intersection. -/
def Before (row : I → X → ℕ) (i : I) (x y : X) : Prop := ∀ j < i, row j y = row j x

omit [TruthValues] in
private theorem before_refl (row : I → X → ℕ) (i : I) (x : X) : Before row i x x :=
  fun _ _ => rfl

omit [TruthValues] in
private theorem before_eq {row : I → X → ℕ} {i : I} {x y : X} (h : Before row i x y) :
    Before row i x = Before row i y := by
  funext z
  apply propext
  exact ⟨fun hz j hj => (hz j hj).trans (h j hj).symm, fun hz j hj => (hz j hj).trans (h j hj)⟩

variable (bit : X → I → Bool) (wf : WellFounded ((· < ·) : I → I → Prop))

/-- A cell refines exactly when its two bits differ at the current coordinate.
Every nonsingleton half then splits immediately at its own first difference. -/
noncomputable def rows : I → X → ℕ := wf.fix fun i earlier x =>
  let C := fun y => ∀ j (h : j < i), earlier j h y = earlier j h x
  if Splits bit C i then rank bit C i x else 0

private theorem rows_eq (i : I) (x : X) :
    rows bit wf i x = if Splits bit (Before (rows bit wf) i x) i then
      rank bit (Before (rows bit wf) i x) i x else 0 := by
  conv_lhs => unfold rows; rw [WellFounded.fix_eq]
  rfl

private theorem rows_on_cell {i : I} {u : X} (x : {x // Before (rows bit wf) i u x}) :
    rows bit wf i x = if Splits bit (Before (rows bit wf) i u) i then
      rank bit (Before (rows bit wf) i u) i x else 0 := by
  rw [rows_eq bit wf i x, ← before_eq x.property]

/-- Connect consecutive children at the first stage at which two points separate. -/
def Edge (x y : X) : Prop := ∃ i, Before (rows bit wf) i x y ∧
  rows bit wf i x + 1 = rows bit wf i y

private theorem edge_on_cell {i : I} {u : X} (x y : {x // Before (rows bit wf) i u x})
    (diff : rows bit wf i x ≠ rows bit wf i y) :
    Edge bit wf x y ↔ rows bit wf i x + 1 = rows bit wf i y := by
  have h : Before (rows bit wf) i x.val y.val := fun j hj => (y.property j hj).trans (x.property j hj).symm
  constructor
  · rintro ⟨j,hj,adj⟩
    rcases lt_trichotomy j i with lt | rfl | gt
    · rw [h j lt] at adj; omega
    · exact adj
    · exact False.elim (diff (hj i gt).symm)
  · exact fun adj => ⟨i,h,adj⟩

private theorem fixes_rows (embed : Function.Injective bit) (f : Equiv.Perm X)
    (hf : Preserves (Edge bit wf) f) (i : I) : ∀ u, rows bit wf i (f u) = rows bit wf i u := by
  induction i using wf.induction with
  | h i ih =>
    intro u
    let C := Before (rows bit wf) i u
    have stable (x : X) : C x ↔ C (f x) := by
      constructor
      · exact fun hx j hj => (ih j hj x).trans (hx j hj)
      · exact fun hx j hj => (ih j hj x).symm.trans (hx j hj)
    let g : Equiv.Perm (Subtype C) := f.subtypeEquiv stable
    let R (x y : Subtype C) := Edge bit wf x.val y.val
    have hg : Preserves R g := fun x y => hf x y
    let u₀ : Subtype C := ⟨u,before_refl _ _ u⟩
    rcases truthCases (Splits bit C i) with splits | skip
    · let child (x : Subtype C) : Fin (arity bit C i) := ⟨rank bit C i x, rank_lt bit C i x⟩
      have eqChild (x : Subtype C) : rows bit wf i x = (child x).val := by
        exact (rows_on_cell bit wf x).trans (ite_eq_left splits)
      have onto : Function.Surjective child := by
        intro j
        obtain ⟨x,hx,hr⟩ := rank_onto bit C wf splits j.val j.isLt
        exact ⟨⟨x,hx⟩,Fin.ext hr⟩
      have path : PathPartition R child := by
        intro x y hxy
        have diff : rows bit wf i x ≠ rows bit wf i y := fun h => hxy (Fin.ext (by simpa only [eqChild] using h))
        simpa only [eqChild] using edge_on_cell bit wf x y diff
      have fixed : child (g u₀) = child u₀ := by
        rcases arity_options bit C i with two | three | four
        · have inj : Function.Injective child := fun x y h =>
            Subtype.ext (rank_injective_two bit C embed two x.property y.property (congrArg Fin.val h))
          apply child_fixed_of_partition onto path g hg _ u₀
          intro x y
          exact ⟨fun h => congrArg child (g.injective (inj h)), fun h => congrArg (fun a => child (g a)) (inj h)⟩
        · exact path_children_fixed (Or.inl three) onto path g hg u₀
        · exact path_children_fixed (Or.inr four) onto path g hg u₀
      exact (eqChild (g u₀)).trans ((congrArg Fin.val fixed).trans (eqChild u₀).symm)
    · have zero (x : Subtype C) : rows bit wf i x = 0 := by
        exact (rows_on_cell bit wf x).trans (ite_eq_right skip)
      exact (zero (g u₀)).trans (zero u₀).symm

/-- For every injection into a well-ordered binary cube, the canonical edge
relation on the original carrier has no nonidentity automorphisms. The only
logical parameter in its construction is decidability of propositions. -/
theorem ordinal_cube_rigid (embed : Function.Injective bit) (f : Equiv.Perm X)
    (hf : Preserves (Edge bit wf) f) (x : X) : f x = x := by
  have fixed := fixes_rows bit wf embed f hf
  apply embed
  funext i
  let C := Before (rows bit wf) i x
  have hx : C x := before_refl _ _ x
  have hfx : C (f x) := fun j _ => fixed j x
  apply Decidable.by_contra
  intro diff
  have split : Splits bit C i := ⟨f x,x,hfx,hx,diff⟩
  have eqR (z : Subtype C) : rows bit wf i z = rank bit C i z := by
    exact (rows_on_cell bit wf z).trans (ite_eq_left split)
  exact diff (rank_bit bit C ((eqR ⟨f x,hfx⟩).symm.trans ((fixed i x).trans (eqR ⟨x,hx⟩))))

/-- A loop-free directed graph on the specified carrier whose only automorphism
is the identity. Vertices, including those of a singleton or empty set, are not enlarged. -/
def HasRigidGraph (Y : Type w) : Prop :=
  ∃ R : Y → Y → Prop, (∀ x, ¬ R x x) ∧ ∀ f : Equiv.Perm Y, Preserves R f → ∀ x, f x = x

include wf in
theorem graph_of_embedding (embed : Function.Injective bit) : HasRigidGraph X := by
  refine ⟨Edge bit wf, ?_, ordinal_cube_rigid bit wf embed⟩
  rintro x ⟨i,_,h⟩
  omega

end OrdinalCube

namespace OrdinalCube

/-- Howard–Tachtsis Problem 5. The subset may be arbitrary and the coordinate
well-order may have any order type. -/
theorem ordinal_subsets {I : Type v} [LinearOrder I]
    (wf : WellFounded ((· < ·) : I → I → Prop)) (S : Set (I → Bool)) : HasRigidGraph S := by
  let _ : TruthValues := ⟨Classical.propDecidable⟩
  exact graph_of_embedding (fun x : S => x.val) wf Subtype.val_injective

/-- The first Kinna–Wagner hypothesis at the given universe levels, phrased as
an injection into the powerset of some well-ordered set for each carrier. -/
def HasOrdinalCoding.{u',v'} (Y : Type u') : Prop :=
  ∃ (J : Type v') (ord : LinearOrder J), WellFounded ord.lt ∧
    ∃ e : Y → Set J, Function.Injective e

/-- From a powerset injection on each carrier obtain a rigid relation on each.
The embeddings in the hypothesis are existential for each individual carrier. -/
theorem kwp_with_truth_values [TruthValues] (kwp : ∀ Y : Type u, HasOrdinalCoding.{u,v} Y)
    (Y : Type u) : HasRigidGraph Y := by
  obtain ⟨J,ord,hJ,e,he⟩ := kwp Y
  let _ : LinearOrder J := ord
  let bits (y : Y) (j : J) := decide (j ∈ e y)
  apply graph_of_embedding bits hJ
  intro x y h
  apply he
  ext j
  have hb := (congrArg (fun b => b = true) (congrFun h j)).to_iff
  simpa only [bits, decide_eq_true_eq] using hb

/-- The first Kinna–Wagner principle implies the rigid relation principle. -/
theorem kwp_implies_rigid (kwp : ∀ Y : Type u, HasOrdinalCoding.{u,v} Y) (Y : Type u) :
    HasRigidGraph Y := by
  let _ : TruthValues := ⟨Classical.propDecidable⟩
  exact kwp_with_truth_values kwp Y

end OrdinalCube
