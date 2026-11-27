module

public import Mathlib.Computability.TuringDegree
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

section

open Filter
namespace StrongSettling

/-- A computably enumerable set is presented by its increasing computable
array of 0/1 stage approximations. Stage zero may already contain entries. -/
structure Enumeration where
  read : ℕ → ℕ → ℕ
  effective : Computable₂ read
  bit : ∀ s x, read s x ≤ 1
  increases : ∀ {s t}, s ≤ t → ∀ x, read s x ≤ read t x

namespace Enumeration

noncomputable def answer (E : Enumeration) (x : ℕ) : ℕ := by
  classical
  exact if ∃ s, E.read s x = 1 then 1 else 0

theorem read_le (E : Enumeration) (s x : ℕ) : E.read s x ≤ E.answer x := by
  classical
  unfold answer
  split
  · exact E.bit _ _
  · rename_i h
    have v := E.bit s x
    have n : E.read s x ≠ 1 := fun e => h ⟨_,e⟩
    exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne v n)

theorem attains (E : Enumeration) (x : ℕ) : ∃ s, E.read s x = E.answer x := by
  classical
  by_cases h : ∃ s, E.read s x = 1
  · simp [answer,h]
  · have bound := E.read_le 0 x
    simp only [answer,h,ite_false] at bound ⊢
    exact ⟨0,Nat.eq_zero_of_le_zero bound⟩

/-- A pairing code for exactly the answers at inputs 0 through x. -/
def prefixCode (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | x+1 => Nat.pair (prefixCode f x) (f (x+1))

theorem prefix_eq {f g : ℕ → ℕ} (x : ℕ) :
    prefixCode f x = prefixCode g x ↔ ∀ i ≤ x, f i = g i := by
  induction x with
  | zero => simp [prefixCode]
  | succ x ih =>
    rw [prefixCode,prefixCode,Nat.pair_eq_pair,ih]
    constructor
    · rintro ⟨h,last⟩ i hi
      by_cases eq : i=x+1
      · simpa [eq] using last
      · exact h _ (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hi eq))
    · intro h
      exact ⟨fun i hi => h _ (Nat.le_succ_of_le hi), h _ le_rfl⟩

theorem stable_prefix (E : Enumeration) (x : ℕ) :
    ∃ s, prefixCode (E.read s) x = prefixCode E.answer x := by
  induction x with
  | zero => simpa [prefixCode] using E.attains 0
  | succ x ih =>
    obtain ⟨s,h⟩ := ih
    obtain ⟨t,ht⟩ := E.attains (x+1)
    use max s t
    apply (prefix_eq _).mpr
    intro i hi
    apply le_antisymm (E.read_le _ _)
    by_cases eq : i=x+1
    · subst i
      rw [← ht]
      exact E.increases (le_max_right _ _) _
    · rw [← (prefix_eq _).mp h i (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hi eq))]
      exact E.increases (le_max_left _ _) _

/-- The first stage by which every answer up to x is final, equivalently
the last entry stage below or at x (zero when nothing enters). -/
noncomputable def modulus (E : Enumeration) (x : ℕ) : ℕ := by
  classical
  exact Nat.find (E.stable_prefix x)

theorem final_at (E : Enumeration) {x s : ℕ} (hs : E.modulus x ≤ s) (i : ℕ) (hi : i ≤ x) :
    E.read s i = E.answer i := by
  classical
  have h : prefixCode (E.read (E.modulus x)) x = prefixCode E.answer x := Nat.find_spec (E.stable_prefix x)
  apply le_antisymm (E.read_le _ _)
  rw [← (prefix_eq _).mp h i hi]
  exact E.increases hs _

theorem modulus_le_iff (E : Enumeration) (x s : ℕ) :
    E.modulus x ≤ s ↔ ∀ i ≤ x, E.read s i = E.answer i := by
  classical
  exact ⟨fun h => E.final_at h,fun h => Nat.find_min' (E.stable_prefix x) ((prefix_eq _).mpr h)⟩

theorem modulus_mono (E : Enumeration) : Monotone E.modulus := by
  intro x y h
  apply (E.modulus_le_iff _ _).mpr
  exact fun i hi => E.final_at (x:=y) le_rfl i (hi.trans h)

end Enumeration

/-- Strong settling-time domination in the sense of Csima and Shore. -/
def Strong (A B : Enumeration) : Prop :=
  ∀ f g : ℕ → ℕ, Computable f → Computable g →
    ∀ᶠ x in atTop, f (A.modulus (g x)) < B.modulus x

end StrongSettling

end

section

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

end

section

open Filter
open scoped Computability
namespace StrongSettling

open Enumeration

private theorem computablePrefix (E : Enumeration) : Computable₂ (fun s x => prefixCode (E.read s) x) := by
  let update (p : ℕ × ℕ) (step : ℕ × ℕ) := Nat.pair step.2 (E.read p.1 (step.1+1))
  have h : Computable₂ update := ((Primrec.to_comp Primrec₂.natPair).to₂.comp
    (Computable.snd.comp Computable.snd)
    (E.effective.comp (Computable.fst.comp Computable.fst)
      (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂
  have c := Computable.nat_rec (α := ℕ × ℕ) Computable.snd (E.effective.comp Computable.fst (Computable.const 0)) h
  refine c.of_eq ?_
  rintro ⟨s,x⟩
  induction x with
  | zero => rfl
  | succ x ih => exact congrArg (fun p => Nat.pair p (E.read s (x+1))) ih

/-- Look for the first stage having exactly the prescribed finite prefix.
For a spurious prefix this search may run forever. -/
noncomputable def firstMatch (B : Enumeration) (p : ℕ) : Part ℕ :=
  Nat.rfind fun s => Part.some (decide (prefixCode (B.read s) p.unpair.1 = p.unpair.2))

theorem firstMatch_partrec (B : Enumeration) : Partrec (firstMatch B) := by
  apply Partrec.rfind
  have stageCode := (computablePrefix B).comp (Computable.snd (α := ℕ) (β := ℕ))
    (Computable.fst.comp (Computable.unpair.comp Computable.fst))
  have expectedCode : Computable fun a : ℕ × ℕ => a.1.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp Computable.fst)
  exact ((Primrec.to_comp Primrec.eq.decide).to₂.comp stageCode expectedCode).partrec.to₂

theorem firstMatch_correct (B : Enumeration) (x : ℕ) :
    B.modulus x ∈ firstMatch B (Nat.pair x (prefixCode B.answer x)) := by
  apply Nat.mem_rfind.mpr
  simp only [Nat.unpair_pair,Part.mem_some_iff]
  constructor
  · exact (decide_eq_true ((prefix_eq x).mpr (B.final_at le_rfl))).symm
  · intro s hs
    exact (decide_eq_false (fun e => hs.not_ge ((B.modulus_le_iff x s).mpr ((prefix_eq x).mp e)))).symm

private theorem boundedTable (f : ℕ → ℕ) (N : ℕ) : Primrec (fun n => if n < N then f n else 0) := by
  induction N with
  | zero => simpa using (Primrec.const (α := ℕ) 0)
  | succ n ih =>
    refine (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const n)) (Primrec.const (f n)) ih).of_eq fun x => ?_
    by_cases eq : x=n
    · simp [eq]
    · by_cases small : x<n <;> simp [eq,small,show x<n+1 ↔ x<n by omega]

/-- Eventual domination of the settling moduli already suffices for the
identity-use reduction. The machine queries the finite oracle prefix and
waits for the observed enumeration to agree with all its answers. -/
theorem reduction_of_eventual (A B : Enumeration) (dom : ∀ᶠ x in atTop, A.modulus x ≤ B.modulus x) :
    IdentityUse A.answer B.answer := by
  obtain ⟨N,bound⟩ := eventually_atTop.mp dom
  let finish (p s : ℕ) := if p.unpair.1 < N then (if p.unpair.1 < N then A.answer p.unpair.1 else 0)
    else A.read s p.unpair.1
  let xOf : ℕ×ℕ → ℕ := fun q => q.1.unpair.1
  have xc : Computable xOf := Computable.fst.comp (Computable.unpair.comp Computable.fst)
  have small := (Primrec.to_comp Primrec.nat_lt.decide).to₂.comp xc (Computable.const N)
  have data := (boundedTable A.answer N).to_comp.comp xc
  have routine : Computable₂ finish := by
    apply (Computable.cond small data (A.effective.comp Computable.snd xc)).of_eq
    rintro ⟨u,s⟩
    by_cases h : u.unpair.1 < N <;> simp [xOf,finish,h]
  let p (u : ℕ) : Part ℕ := (firstMatch B u).map (finish u)
  have code : Partrec p := (firstMatch_partrec B).map routine
  refine ⟨p,code,fun x => ?_⟩
  have hs := firstMatch_correct B x
  apply (Part.mem_map_iff _).mpr
  refine ⟨_,hs,?_⟩
  by_cases h : x<N
  · simp [finish,h]
  · simp [finish,h,A.final_at (bound x (by omega)) x le_rfl]

/-- Strong settling domination gives the stated bound x on the largest input
queried and hence genuine Mathlib Turing reducibility on characteristic functions. -/
theorem strong_imp_reducible (A B : Enumeration) (h : Strong A B) :
    IdentityUse A.answer B.answer ∧ (A.answer : ℕ →. ℕ) ≤ᵀ (B.answer : ℕ →. ℕ) := by
  have dom := (h id id Computable.id Computable.id).mono (fun x hx => Nat.le_of_lt hx)
  have r := reduction_of_eventual A B dom
  exact ⟨r,r.turing⟩

end StrongSettling

end
