module

public import SolvedProblems.SettlingEnumeration

@[expose] public section

namespace StrongSettling

open Enumeration
open scoped Computability

/-- Identity-bounded oracle use: an ordinary partial recursive routine
receives x and the code of the oracle's answers at precisely 0,...,x. -/
def IdentityUse (a b : ℕ → ℕ) : Prop :=
  ∃ p : ℕ →. ℕ, Partrec p ∧ ∀ x, a x ∈ p (Nat.pair x (prefixCode b x))

private theorem rel_pair {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (h : Nat.RecursiveIn O (fun n => Part.some (f n))) (k : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun x => Part.some (Nat.pair (f x) (g x))) :=
  (h.pair k).of_eq fun n => by
    change (Nat.pair <$> (pure (f n) : Part ℕ) <*> pure (g n)) = pure _
    simp only [map_pure, pure_seq]

private theorem rel_comp {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (h : Nat.RecursiveIn O (fun n => Part.some (f n))) (k : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun x => Part.some (f (g x))) :=
  (h.comp k).of_eq fun _ => Part.bind_some ..

/-- The finite prefix itself is recursive in the characteristic oracle. -/
theorem prefix_relative (f : ℕ → ℕ) :
    (fun n => Part.some (prefixCode f n)) ≤ᵀ (f : ℕ →. ℕ) := by
  let O : Set (ℕ →. ℕ) := {(f : ℕ →. ℕ)}
  have obs : Nat.RecursiveIn O f := .oracle _ (by simp [O])
  have z : Nat.RecursiveIn O (fun _ => Part.some (f 0)) := (Nat.Primrec.const (f 0)).recursiveIn
  have firstProjection : Nat.RecursiveIn O (fun n => Part.some n.unpair.1) := .left
  have secondProjection : Nat.RecursiveIn O (fun n => Part.some n.unpair.2) := .right
  have step := rel_pair (rel_comp secondProjection secondProjection) (rel_comp obs (rel_comp Nat.RecursiveIn.succ (rel_comp firstProjection secondProjection)))
  have recursion := z.prec step
  have main : Nat.RecursiveIn O (fun n => Part.some (prefixCode f n.unpair.2)) := by
    refine recursion.of_eq fun n => ?_
    obtain ⟨⟨a,k⟩,rfl⟩ := Nat.pairEquiv.surjective n
    change _ = Part.some (prefixCode f (Nat.pair a k).unpair.2)
    rw [show Nat.pairEquiv (a,k) = Nat.pair a k from rfl]
    simp only [Nat.unpair_pair]
    induction k with
    | zero => rfl
    | succ k ih =>
      exact (congrArg (fun v : Part ℕ => v.bind fun i => Part.some (Nat.pair i (f (k+1)))) ih).trans
        (Part.bind_some ..)
  apply RecursiveIn.iff_nat.mpr
  have key := rel_pair (O := O) Nat.RecursiveIn.zero (Nat.Primrec.id.recursiveIn)
  simpa only [Nat.unpair_pair,id_eq,O] using rel_comp main key

theorem IdentityUse.turing {a b : ℕ → ℕ} (useBound : IdentityUse a b) :
    (a : ℕ →. ℕ) ≤ᵀ (b : ℕ →. ℕ) := by
  obtain ⟨p, code, hp⟩ := useBound
  apply RecursiveIn.iff_nat.mpr
  have pair := rel_pair (Nat.Primrec.id.recursiveIn) (RecursiveIn.iff_nat.mp (prefix_relative b))
  refine ((Partrec.nat_iff.mp code).recursiveIn.comp pair).of_eq_tot fun x => ?_
  change a x ∈ (Part.some (Nat.pair x (prefixCode b x))).bind p
  exact Part.mem_bind_iff.mpr ⟨_,Part.mem_some _,hp x⟩

end StrongSettling
