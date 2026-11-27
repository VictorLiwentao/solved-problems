module

public import SolvedProblems.OrdinalCubeLogic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fin.Basic

@[expose] public section

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
