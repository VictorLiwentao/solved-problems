module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Nat

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne.Cantor

open Set

abbrev Branch := ℕ → Bool
abbrev Word := Σ n : ℕ, Fin n → Bool

def node (s : Branch) (n : ℕ) : Word := ⟨n,fun i => s i⟩
def On (s : Branch) (t : Word) : Prop := ∀ k : Fin t.1, s k = t.2 k

theorem same_node {s : Branch} {t : Word} (h : On s t) : node s t.1 = t := by
  obtain ⟨n,w⟩ := t
  exact congrArg (Sigma.mk n) (funext h)

private theorem uncountable : ¬ Countable Branch := by
  intro c
  obtain ⟨f,surj⟩ := @exists_surjective_nat Branch ⟨fun _ => false⟩ c
  obtain ⟨n,h⟩ := surj (fun n => !(f n n))
  have e := congrFun h n
  cases he : f n n <;> simp [he] at e

private theorem large_color {Y : Type u} [Countable Y] (f : Branch → Y) : ∃ c, ¬ (f ⁻¹' {c}).Countable := by
  classical
  by_contra! h
  apply uncountable
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion h).mono
  exact fun x _ => Set.mem_iUnion.2 ⟨f x,rfl⟩

/-- Some member of an uncountable set has uncountably many members of the
same set sharing each of its finite prefixes. -/
private theorem condensation {B : Set Branch} (h : ¬ B.Countable) :
    ∃ s ∈ B, ∀ n, ¬ {r ∈ B | On r (node s n)}.Countable := by
  classical
  by_contra! all
  let slice (w : Word) := {r ∈ B | On r w}
  let small := {w : Word // (slice w).Countable}
  apply h
  apply (Set.countable_iUnion (fun w : small => w.property)).mono
  intro s hs
  obtain ⟨n,hn⟩ := all s hs
  exact Set.mem_iUnion.2 ⟨⟨node s n,hn⟩,hs,fun _ => rfl⟩

structure Split (s t : Branch) (n : ℕ) : Prop where
  earlier : ∀ k < n, s k = t k
  differ : s n ≠ t n

private theorem different (s : Branch) {B : Set Branch} (many : ∀ n, ¬ {r ∈ B | On r (node s n)}.Countable)
    (n : ℕ) : ∃ r ∈ B, ∃ m ≥ n, Split r s m := by
  classical
  have extra : ∃ r ∈ B, On r (node s n) ∧ r ≠ s := by
    by_contra! h
    apply many n
    apply (Set.countable_singleton s).mono
    intro x hx; exact h x hx.1 hx.2
  obtain ⟨r,hr,pre,ne⟩ := extra
  have dif : ∃ k, r k ≠ s k := by
    by_contra! eq
    exact ne (funext eq)
  let m := Nat.find dif
  have before (k : ℕ) (hk : k < m) : r k = s k := not_not.mp (Nat.find_min dif hk)
  refine ⟨r,hr,m,?_,before,Nat.find_spec dif⟩
  by_contra! short
  exact (Nat.find_spec dif) (pre ⟨m,short⟩)

/-- Four branches of the same color with successively later first differences
from a single center branch. No measurability condition on the coloring is needed. -/
theorem four_same {Y : Type u} [Countable Y] (f : Branch → Y) :
    ∃ (r v s w : Branch) (a b c : ℕ), f r=f s ∧ f v=f w ∧ a<b ∧ b<c ∧
      Split r s a ∧ Split v s b ∧ Split w s c := by
  obtain ⟨y,large⟩ := large_color f
  obtain ⟨s,hs,big⟩ := condensation large
  obtain ⟨r,hr,a,_,ar⟩ := different s big 0
  obtain ⟨v,hv,b,ab,bv⟩ := different s big (a+1)
  obtain ⟨w,hw,c,bc,cw⟩ := different s big (b+1)
  exact ⟨r,v,s,w,a,b,c,(show f r=y from hr).trans (show f s=y from hs).symm,
    (show f v=y from hv).trans (show f w=y from hw).symm,ab,bc,ar,bv,cw⟩

private theorem on_short {r s : Branch} {a : ℕ} (h : Split r s a) {t : Word} (ht : t.1 ≤ a) :
    On r t ↔ On s t := by
  constructor <;> intro f k
  · exact (h.earlier k (k.isLt.trans_le ht)).symm.trans (f k)
  · exact (h.earlier k (k.isLt.trans_le ht)).trans (f k)

private theorem not_both {r s : Branch} {a : ℕ} (h : Split r s a) {t : Word} (ht : a < t.1) :
    ¬ (On r t ∧ On s t) := fun e => h.differ ((e.1 ⟨a,ht⟩).trans (e.2 ⟨a,ht⟩).symm)

def path (s : Branch) (b c : ℕ) : Finset Word := (Finset.Ioc b c).image (node s)

theorem path_nonempty (s : Branch) {b c : ℕ} (lt : b < c) : (path s b c).Nonempty := by
  exact ⟨node s c,Finset.mem_image.2 ⟨c,Finset.mem_Ioc.2 ⟨lt,le_rfl⟩,rfl⟩⟩

/-- The signed factors can overlap only on one finite nonempty path, where
both have positive sign. At every other word at least one pair cancels. -/
theorem path_signs {r v s w : Branch} {a b c : ℕ} (ab : a<b) (bc : b<c)
    (ar : Split r s a) (bv : Split v s b) (cw : Split w s c) (t : Word) :
    (t ∈ path s b c → ¬ On r t ∧ On s t ∧ ¬ On v t ∧ On w t) ∧
    (t ∉ path s b c → (On r t ↔ On s t) ∨ (On v t ↔ On w t)) := by
  classical
  constructor
  · intro ht
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨bd,dc⟩ := Finset.mem_Ioc.mp hd
    have os : On s (node s d) := fun _ => rfl
    exact ⟨fun h => not_both ar (ab.trans bd) ⟨h,os⟩,os,fun h => not_both bv bd ⟨h,os⟩,
      (on_short cw dc).mpr os⟩
  · intro ht
    by_cases small : t.1 ≤ a
    · exact Or.inl (on_short ar small)
    have aa : a < t.1 := lt_of_not_ge small
    by_cases or' : On r t
    · right
      have exclude {z : Branch} (eq : z a = s a) : ¬On z t := fun on =>
        ar.differ (((or' ⟨a,aa⟩).trans (on ⟨a,aa⟩).symm).trans eq)
      exact iff_of_false (exclude (bv.earlier a ab)) (exclude (cw.earlier a (ab.trans bc)))
    by_cases os : On s t
    · right
      by_cases bb : t.1 ≤ b
      · exact (on_short bv bb).trans (on_short cw (bb.trans bc.le)).symm
      have high : b < t.1 := lt_of_not_ge bb
      have far : c < t.1 := by
        by_contra! short
        exact ht (Finset.mem_image.2 ⟨t.1,Finset.mem_Ioc.2 ⟨high,short⟩,same_node os⟩)
      exact iff_of_false (fun h => not_both bv high ⟨h,os⟩) (fun h => not_both cw far ⟨h,os⟩)
    · exact Or.inl (iff_of_false or' os)

end ChoiceOmegaOne.Cantor
