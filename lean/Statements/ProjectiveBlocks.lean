module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Ring

@[expose] public section

namespace ProjectiveBlocks

/-- A finite core and countably many blocks, each with `d` labelled positions. -/
abbrev Point (c d : ℕ) := Fin c ⊕ (ℕ × Fin d)

/-- Each of the `k` coordinates stores its finite/cofinite flag and its finite part. -/
abbrev Code (c d k : ℕ) := Fin k → Bool × Finset (Point c d)

/-- A block permutation fixes the core and preserves the position inside each block. -/
def relabel {c d : ℕ} (σ : Equiv.Perm ℕ) : Equiv.Perm (Point c d) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr σ (Equiv.refl _))

/-- Transport the actual finite subsets by the positionwise action. -/
def rename {c d k : ℕ} (σ : Equiv.Perm ℕ) (x : Code c d k) : Code c d k :=
  fun j => ((x j).1, (x j).2.map (relabel σ).toEmbedding)

/-- The self-map commutes with every block permutation. -/
def Equivariant {c d k : ℕ} (g : Code c d k → Code c d k) : Prop :=
  ∀ σ x, g (rename σ x) = rename σ (g x)

/-- The core and flags have `2^(k(1+c))` states, and there are `q` possible
patterns of a block, giving `q^q` output tables on input patterns. -/
def orbitBound (c d k : ℕ) : ℕ :=
  let q := 2 ^ (d * k)
  2 ^ (k * (1 + c)) * q ^ q

end ProjectiveBlocks

public section

namespace ProjectiveBlocks

open Function Set

private abbrev Pattern (d k : ℕ) := Fin d × Fin k → Bool
private abbrev Table (c d k : ℕ) :=
  (Fin k → Bool) × (Fin c × Fin k → Bool) × (Pattern d k → Pattern d k)

private def pattern {c d k} (x : Code c d k) (i : ℕ) : Pattern d k :=
  fun p => decide (Sum.inr (i, p.1) ∈ (x p.2).2)

private def core {c d k} (x : Code c d k) : Fin c × Fin k → Bool :=
  fun p => decide (Sum.inl p.1 ∈ (x p.2).2)

private theorem ext_code {c d k} {x y : Code c d k}
    (hflag : ∀ j, (x j).1 = (y j).1) (hcore : core x = core y)
    (hblocks : ∀ i, pattern x i = pattern y i) : x = y := by
  funext j
  apply Prod.ext (hflag j)
  apply Finset.ext
  intro a
  obtain a | ⟨i,t⟩ := a
  · simpa [core] using congrFun hcore (a,j)
  · simpa [pattern] using congrFun (hblocks i) (t,j)

private theorem pattern_rename {c d k} (σ : Equiv.Perm ℕ) (x : Code c d k) (i : ℕ) :
    pattern (rename σ x) i = pattern x (σ.symm i) := by
  funext j
  simp only [pattern, rename, Finset.mem_map_equiv]
  rfl

private theorem core_rename {c d k} (σ : Equiv.Perm ℕ) (x : Code c d k) :
    core (rename σ x) = core x := by
  funext j
  simp only [core, rename, Finset.mem_map_equiv]
  rfl

private theorem iter_const {c d k} {g : Code c d k → Code c d k} (hg : Equivariant g)
    (s : Code c d k) {a b : ℕ} (hab : pattern s a = pattern s b) (n : ℕ) :
    pattern (g^[n] s) a = pattern (g^[n] s) b := by
  let σ := Equiv.swap a b
  have fixed : rename σ s = s := by
    apply ext_code (x := rename σ s) (y := s) (fun _ => rfl) (core_rename σ s)
    intro i
    rw [pattern_rename]
    change pattern s (Equiv.swap a b i) = pattern s i
    by_cases ha : i = a
    · simpa [ha] using hab.symm
    by_cases hb : i = b
    · simpa [hb] using hab
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  have stabilizes : rename σ (g^[n] s) = g^[n] s := by
    induction n with
    | zero => exact fixed
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← hg σ, ih]
  have hb := congrArg (fun x => pattern x b) stabilizes
  simpa only [pattern_rename, σ, Equiv.symm_swap, Equiv.swap_apply_right] using hb

private noncomputable def representative {c d k} (s : Code c d k) (p : Pattern d k) : ℕ :=
  open Classical in if h : ∃ i, pattern s i = p then Nat.find h else 0

private theorem rep_pattern {c d k} (s : Code c d k) (i : ℕ) :
    pattern s (representative s (pattern s i)) = pattern s i := by
  classical
  have h : ∃ j, pattern s j = pattern s i := ⟨i,rfl⟩
  simpa only [representative, dite_eq_left h] using Nat.find_spec h

private noncomputable def encode {c d k} (s x : Code c d k) : Table c d k :=
  (fun j => (x j).1, core x, fun p => pattern x (representative s p))

private theorem encode_inj {c d k} {g : Code c d k → Code c d k} (hg : Equivariant g)
    (s : Code c d k) : Set.InjOn (encode s) (Set.range (fun n => g^[n] s)) := by
  rintro _ ⟨n,rfl⟩ _ ⟨m,rfl⟩ h
  apply ext_code (congrFun (congrArg Prod.fst h)) (congrArg (fun t => t.2.1) h)
  intro i
  have hi := rep_pattern s i
  exact (iter_const hg s hi n).symm.trans <|
    (congrFun (congrArg (fun t => t.2.2) h) (pattern s i)).trans (iter_const hg s hi m)

private theorem table_card (c d k : ℕ) : Fintype.card (Table c d k) = orbitBound c d k := by
  simp only [Table, Pattern, orbitBound, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  rw [← Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  ring

/-- The explicit uniform bound in the manuscript counts all forward iterates of
any finite/cofinite code, including the finite parts on the fixed core. -/
theorem blockOrbitBound {c d k : ℕ} (g : Code c d k → Code c d k) (hg : Equivariant g)
    (s : Code c d k) :
    (Set.range fun n : ℕ => g^[n] s).Finite ∧
    (Set.range fun n : ℕ => g^[n] s).ncard ≤ orbitBound c d k := by
  classical
  let O := Set.range fun n : ℕ => g^[n] s
  have inj := encode_inj hg s
  have finite : O.Finite := Set.Finite.of_injOn (f := encode s) (t := Set.univ)
    (fun _ _ => trivial) inj (Set.finite_univ)
  refine ⟨finite, ?_⟩
  have le := O.ncard_le_ncard_of_injOn (encode s) (t := Set.univ) (fun _ _ => trivial) inj
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, table_card] using le

private theorem eventual_period {X : Type*} (f : X → X) (x : X) (B : ℕ)
    {a b : Fin (B+1)} (hab : a < b) (heq : f^[a.val] x = f^[b.val] x) :
    Function.IsPeriodicPt f B.factorial (f^[B] x) := by
  have hper : Function.IsPeriodicPt f (b.val - a.val) (f^[a.val] x) := by
    change f^[b.val-a.val] (f^[a.val] x) = f^[a.val] x
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le, heq]
  have ale : a.val ≤ B := by omega
  have pos : 0 < b.val-a.val := by omega
  have le : b.val-a.val ≤ B := by omega
  have period := (hper.trans_dvd (Nat.dvd_factorial pos le)).apply_iterate (B-a.val)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel ale] at period

/-- A surjective equivariant map has a single finite exponent working on all
codes. In particular it cannot be the noninjective surjection transferred to
this countable block model in the degenerate case of the paper. -/
theorem equivariantSurjection {c d k : ℕ} (g : Code c d k → Code c d k)
    (hg : Equivariant g) (hs : Function.Surjective g) :
    g^[(orbitBound c d k).factorial] = id ∧ Function.Injective g := by
  let B := orbitBound c d k
  have all (s : Code c d k) : Function.IsPeriodicPt g B.factorial s := by
    obtain ⟨x,rfl⟩ := hs.iterate B s
    let tags (n : Fin (B+1)) := encode x (g^[n.val] x)
    have count : Fintype.card (Table c d k) < Fintype.card (Fin (B+1)) := by
      rw [table_card, Fintype.card_fin]
      exact Nat.lt_succ_self B
    obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt tags count
    have same := encode_inj hg x ⟨i.val,rfl⟩ ⟨j.val,rfl⟩ he
    rcases lt_or_gt_of_ne hne with h | h
    · exact eventual_period g x B h same
    · exact eventual_period g x B h same.symm
  exact ⟨funext (fun s => (all s).eq),
    fun {_ _} h => (all _).eq_of_apply_eq_same (all _) (Nat.factorial_pos B) h⟩

end ProjectiveBlocks
