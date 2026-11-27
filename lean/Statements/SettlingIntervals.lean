module

public import Mathlib.Computability.TuringDegree
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE

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

section

open Filter
open Nat.Partrec.Code
open scoped Computability
namespace StrongSettling

abbrev Program := Nat.Partrec.Code

/-- The interpreter is allowed exactly the final settling modulus as its fuel. -/
def Eligible (D : Enumeration) (c : Program) (x : ℕ) : Prop := (evaln (D.modulus x) c x).isSome

noncomputable def runningTime (c : Program) : ℕ →. ℕ :=
  fun x => Nat.rfind fun k => Part.some ((evaln k c x).isSome)

theorem runningTime_partrec (c : Program) : Partrec (runningTime c) := by
  apply Partrec.rfind
  exact (Primrec.option_isSome.to_comp.comp (primrec_evaln.to_comp.comp
    ((Computable.snd.pair (Computable.const c)).pair Computable.fst))).partrec.to₂

theorem total_time {c : Program} (total : ∀ x, (eval c x).Dom) :
    ∃ t : ℕ → ℕ, Computable t ∧ ∀ x, (evaln (t x) c x).isSome := by
  classical
  have existsTime (x : ℕ) : ∃ k, (evaln k c x).isSome := by
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp (total x)
    obtain ⟨k,hk⟩ := evaln_complete.mp hy
    exact ⟨k,Option.isSome_iff_exists.mpr ⟨y,hk⟩⟩
  let t (x : ℕ) := Nat.find (existsTime x)
  have halt (x : ℕ) : (evaln (t x) c x).isSome := Nat.find_spec (existsTime x)
  refine ⟨t,(runningTime_partrec c).of_eq_tot (fun x => ?_),halt⟩
  apply Nat.mem_rfind.mpr
  constructor
  · exact Part.mem_some_iff.mpr (halt x).symm
  · intro k hk
    apply Part.mem_some_iff.mpr
    have n : ¬(evaln k c x).isSome := Nat.find_min (existsTime x) hk
    cases e : (evaln k c x).isSome <;> simp_all

/-- Dominating the running-time function recognizes all sufficiently late
computations of every total partial-recursive program. -/
theorem eventually_eligible (D : Enumeration)
    (dominant : ∀ f : ℕ → ℕ, Computable f → ∀ᶠ x in atTop, f x ≤ D.modulus x)
    (c : Program) (total : ∀ x, (eval c x).Dom) : ∀ᶠ x in atTop, Eligible D c x := by
  obtain ⟨t,ht,h⟩ := total_time total
  apply (dominant t ht).mono
  intro x bound
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (h x)
  exact Option.isSome_iff_exists.mpr ⟨v,evaln_mono bound hv⟩

/-- A computation with enough fuel returns exactly its genuine, unbounded
interpreter value. This includes programs which are partial on other inputs. -/
theorem eligibility_sound (D : Enumeration) (c : Program) (x v : ℕ)
    (h : v ∈ evaln (D.modulus x) c x) : v ∈ eval c x := evaln_sound h

end StrongSettling

end

section

open Nat.Partrec.Code
namespace StrongSettling
open Enumeration

private theorem later_entry (D : Enumeration) (x t : ℕ) :
    t < D.modulus x ↔ ∃ i ≤ x, ∃ s, D.read t i < D.read s i := by
  constructor
  · intro ht
    by_contra! h
    apply ht.not_ge
    apply (D.modulus_le_iff x t).mpr
    intro i hi
    obtain ⟨s,hs⟩ := D.attains i
    exact le_antisymm (D.read_le _ _) (hs ▸ h i hi s)
  · rintro ⟨i,hi,s,h⟩
    by_contra! low
    rw [D.final_at low i hi] at h
    exact h.not_ge (D.read_le s i)

private def witness (D : Enumeration) (c : Program) (x w : ℕ) : Bool :=
  let t := w.unpair.1
  let i := w.unpair.2.unpair.1
  let s := w.unpair.2.unpair.2
  (evaln (t+1) c x).isSome && decide (i ≤ x) && decide (D.read t i < D.read s i)

private theorem exists_witness (D : Enumeration) (c : Program) (x : ℕ) :
    (∃ w, witness D c x w = true) ↔ Eligible D c x := by
  constructor
  · rintro ⟨w,hw⟩
    rw [witness] at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hw.1.1
    have lt := (later_entry D x w.unpair.1).mpr ⟨_,hw.1.2,_,hw.2⟩
    exact Option.isSome_iff_exists.mpr ⟨v,evaln_mono lt hv⟩
  · intro h
    change (evaln (D.modulus x) c x).isSome at h
    cases eq : D.modulus x with
    | zero => simp [eq,evaln] at h
    | succ t =>
      have lt : t < D.modulus x := by omega
      obtain ⟨i,hi,s,later⟩ := (later_entry D x t).mp lt
      use Nat.pair t (Nat.pair i s)
      simpa [witness,hi,later,eq] using h

/-- Eligibility can be recognized by an ordinary computably enumerable search
on the program and input jointly; the final modulus is not an input to it. -/
theorem eligibility_re (D : Enumeration) : REPred fun p : Program × ℕ => Eligible D p.1 p.2 := by
  let U := (Program × ℕ) × ℕ
  have p : Computable (fun a : U => a.1.1) := Computable.fst.comp Computable.fst
  have x : Computable (fun a : U => a.1.2) := Computable.snd.comp Computable.fst
  have u : Computable (fun a : U => a.2.unpair) := Computable.unpair.comp Computable.snd
  have t := Computable.fst.comp u
  have v := Computable.unpair.comp (Computable.snd.comp u)
  have i := Computable.fst.comp v
  have s := Computable.snd.comp v
  have sim := Primrec.option_isSome.to_comp.comp (primrec_evaln.to_comp.comp (((Computable.succ.comp t).pair p).pair x))
  have le := (Primrec.to_comp Primrec.nat_le.decide).to₂.comp i x
  have lt := (Primrec.to_comp Primrec.nat_lt.decide).to₂.comp (D.effective.comp t i) (D.effective.comp s i)
  have both : Computable₂ (· && ·) := (Primrec.to_comp (Primrec.dom_bool₂ (· && ·))).to₂
  have check : Computable (fun a : U => witness D a.1.1 a.1.2 a.2) := both.comp (both.comp sim le) lt
  have search := Partrec.rfind check.partrec.to₂
  apply search.dom_re.of_eq
  intro a
  rw [← exists_witness D a.1 a.2]
  constructor
  · intro h
    obtain ⟨k,hk,_⟩ := Nat.rfind_dom.mp h
    exact ⟨k,(Part.mem_some_iff.mp hk).symm⟩
  · rintro ⟨k,hk⟩
    exact Nat.rfind_dom.mpr ⟨k, Part.mem_some_iff.mpr hk.symm, fun {_} _ => trivial⟩

/-- Access to the characteristic oracle through x decides success as well as
failure of the bounded computation, even when the original program diverges. -/
theorem eligibility_decided (D : Enumeration) (c : Program) :
    IdentityUse (fun x => (evaln (D.modulus x) c x).isSome.toNat) D.answer := by
  let inspect (p s : ℕ) := (evaln s c p.unpair.1).isSome.toNat
  have routine : Computable₂ inspect :=
    (Primrec.to_comp (Primrec.dom_bool Bool.toNat)).comp₂
      ((Primrec.option_isSome.to_comp.comp (primrec_evaln.to_comp.comp
       ((Computable.snd.pair (Computable.const c)).pair (Computable.fst.comp (Computable.unpair.comp Computable.fst))))).to₂)
  let p (u : ℕ) := (firstMatch D u).map (inspect u)
  refine ⟨p,(firstMatch_partrec D).map routine,fun x => ?_⟩
  exact (Part.mem_map_iff _).mpr ⟨_,firstMatch_correct D x, by simp [inspect]⟩

end StrongSettling

end

section

open Nat.Partrec.Code
open Filter
namespace StrongSettling

/-- The input program must halt on every earlier input before this sum returns. -/
def prefixSum (c : Program) : ℕ →. ℕ
  | 0 => eval c 0
  | n+1 => (prefixSum c n).bind fun a => (eval c (n+1)).map fun b => a+b

def envelope (c : Program) (n : ℕ) : Part ℕ := (prefixSum c n).map fun s => n+1+s

private theorem sum_partrec : Partrec₂ prefixSum := by
  let U := (Program × ℕ) × (ℕ × ℕ)
  have step : Partrec fun q : U => (eval q.1.1 (q.2.1+1)).map (fun z => q.2.2+z) := by
    apply (eval_part.comp (Computable.fst.comp Computable.fst)
      (Computable.succ.comp (Computable.fst.comp Computable.snd))).map
    exact ((Primrec.to_comp Primrec.nat_add).to₂.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd).to₂
  have s := Partrec.nat_rec (α := Program × ℕ) Computable.snd
    (eval_part.comp Computable.fst (Computable.const 0)) step.to₂
  refine s.of_eq ?_
  rintro ⟨c,n⟩
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun v : Part ℕ => v.bind fun a => (eval c (n+1)).map fun b => a+b) ih

theorem envelope_partrec : Partrec₂ envelope := by
  apply sum_partrec.map
  exact ((Primrec.to_comp Primrec.nat_add).to₂.comp
    (Computable.succ.comp (Computable.snd.comp Computable.fst)) Computable.snd).to₂

/-- There is one computable list of programs for the envelopes. -/
theorem envelope_compiler : ∃ e : Program → Program, Computable e ∧
    ∀ c x, eval (e c) x = envelope c x := by
  let fn (i x : ℕ) := envelope (Denumerable.ofNat Program i) x
  have dec : Partrec₂ fn := (envelope_partrec.comp ((Computable.ofNat Program).comp Computable.fst) Computable.snd).to₂
  obtain ⟨m,hm⟩ := exists_code.mp (Partrec₂.unpaired'.mpr dec)
  refine ⟨fun c => curry m (Encodable.encode c),
    (primrec₂_curry.comp (Primrec.const m) Primrec.encode).to_comp,fun c x => ?_⟩
  rw [eval_curry,hm]
  simp [Nat.unpaired,fn]

private theorem larger_sum {c : Program} {n j v : ℕ} (h : v ∈ prefixSum c n) (below : j ≤ n) :
    ∃ u ∈ prefixSum c j, u ≤ v := by
  induction n generalizing v with
  | zero =>
    obtain rfl : j=0 := by omega
    exact ⟨_,h,le_rfl⟩
  | succ n ih =>
    by_cases eq : j=n+1
    · subst j; exact ⟨_,h,le_rfl⟩
    obtain ⟨a,ha,hv⟩ := Part.mem_bind_iff.mp h
    obtain ⟨b,_,rfl⟩ := (Part.mem_map_iff _).mp hv
    obtain ⟨u,hu,le⟩ := ih ha (by omega)
    exact ⟨u,hu,by omega⟩

/-- Every value at a larger input forces convergence at every smaller one,
and the output strictly increases between any two different inputs. -/
theorem envelope_initial {c : Program} {n m v : ℕ} (h : v ∈ envelope c n) (lt : m<n) :
    ∃ u ∈ envelope c m, u < v := by
  obtain ⟨a,ha,rfl⟩ := (Part.mem_map_iff _).mp h
  obtain ⟨b,hb,le⟩ := larger_sum ha lt.le
  exact ⟨_,(Part.mem_map_iff _).mpr ⟨b,hb,rfl⟩,by omega⟩

private theorem total_sum {c : Program} (h : ∀ x, (eval c x).Dom) (n : ℕ) :
    ∃ s ∈ prefixSum c n, ∃ v ∈ eval c n, v ≤ s := by
  induction n with
  | zero =>
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp (h 0)
    exact ⟨_,hv,_,hv,le_rfl⟩
  | succ n ih =>
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp (h (n+1))
    obtain ⟨a,ha,-⟩ := ih
    exact ⟨_,Part.mem_bind_iff.mpr ⟨a,ha,(Part.mem_map_iff _).mpr ⟨v,hv,rfl⟩⟩,v,hv,by omega⟩

/-- Total computable functions are pointwise majorized by total members of
the envelope list. Each such member is eventually eligible under a dominant modulus. -/
theorem effective_majorants (D : Enumeration)
    (dom : ∀ f : ℕ → ℕ, Computable f → ∀ᶠ x in atTop, f x ≤ D.modulus x) :
    ∃ e : Program → Program, Computable e ∧
      (∀ c n m v, v ∈ eval (e c) n → m<n → ∃ u ∈ eval (e c) m, u<v) ∧
      ∀ f : ℕ → ℕ, Computable f → ∃ c,
        (∀ x, ∃ v ∈ eval (e c) x, max x (f x)<v) ∧ ∀ᶠ x in atTop, Eligible D (e c) x := by
  obtain ⟨e,eff,ok⟩ := envelope_compiler
  refine ⟨e,eff,fun c n m v h lt => by simpa only [ok] using envelope_initial (ok c n ▸ h) lt,?_⟩
  intro f hf
  obtain ⟨c,hc⟩ := exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  have total (n : ℕ) : (eval c n).Dom := by rw [hc]; trivial
  have positive (n : ℕ) : ∃ v ∈ eval (e c) n, max n (f n)<v := by
    obtain ⟨s,hs,v,hv,le⟩ := total_sum total n
    have eq : v = f n := by rw [hc] at hv; exact Part.mem_some_iff.mp hv
    rw [ok]
    exact ⟨_,(Part.mem_map_iff _).mpr ⟨s,hs,rfl⟩,by omega⟩
  exact ⟨c,positive,eventually_eligible D dom _ (fun n => (positive n).choose_spec.1.1)⟩

end StrongSettling

end

section

open Filter

namespace StrongSettling

namespace Enumeration

/-- A genuine positive entry at a successor stage (stage zero carries no delay). -/
def Entry (E : Enumeration) (t i : ℕ) : Prop := 0 < t ∧ E.read (t-1) i < E.read t i

theorem entry_le_modulus (E : Enumeration) {t i x : ℕ} (h : E.Entry t i) (hi : i≤x) :
    t ≤ E.modulus x := by
  by_contra! lt
  have late : E.modulus x ≤ t-1 := by omega
  exact h.2.not_ge ((E.read_le _ _).trans_eq (E.final_at late i hi).symm)

theorem last_entry (E : Enumeration) {x : ℕ} (pos : 0 < E.modulus x) :
    ∃ i ≤ x, E.Entry (E.modulus x) i := by
  have lower : ¬E.modulus x ≤ E.modulus x-1 := by omega
  rw [E.modulus_le_iff] at lower
  push Not at lower
  obtain ⟨i,hi,unequal⟩ := lower
  refine ⟨i,hi,pos,?_⟩
  rw [E.final_at (x := x) le_rfl i hi]
  exact lt_of_le_of_ne (E.read_le _ _) unequal

end Enumeration

/-- A signal at stage s activates a response in the earlier block of A.
Each later entry in B below its cutoff generates a second kind of request.
Only actual entry stages and positions of the two enumerations occur here. -/
def Responses (A B : Enumeration) (F : ℕ → ℕ) (lo s cutoff : ℕ) : Prop :=
  (∃ t i, i≤lo ∧ F s<t ∧ A.Entry t i) ∧
  ∀ t i, s<t → i≤cutoff → B.Entry t i → ∃ u j, j≤lo ∧ F t<u ∧ A.Entry u j

/-- The domination inequality on the whole interval between successive
final markers, including the case of a last entry after activation. -/
theorem interval_domination (A B : Enumeration) (F G : ℕ → ℕ) (f : Monotone F) (g : Monotone G)
    {lo hi x s cutoff : ℕ} (low : lo≤x) (high : x<hi) (size : G hi ≤ cutoff)
    (responses : Responses A B F lo s cutoff) : F (B.modulus (G x)) < A.modulus x := by
  by_cases early : B.modulus (G x) ≤ s
  · obtain ⟨t,i,whereAt,delay,enters⟩ := responses.1
    exact (lt_of_le_of_lt (f early) delay).trans_le (A.entry_le_modulus enters (whereAt.trans low))
  · have late := Nat.lt_of_not_ge early
    obtain ⟨i,whereAt,enters⟩ := B.last_entry (Nat.zero_lt_of_lt late)
    obtain ⟨u,j,whereNext,delay,respond⟩ := responses.2 _ i late (whereAt.trans ((g high.le).trans size)) enters
    exact delay.trans_le (A.entry_le_modulus respond (whereNext.trans low))

private theorem computable_majorant {f : ℕ → ℕ} (hf : Computable f) :
    ∃ F : ℕ → ℕ, Computable F ∧ Monotone F ∧ ∀ i, f i ≤ F i := by
  let F (n : ℕ) := Nat.rec (motive := fun _ => ℕ) (f 0) (fun k z => max z (f (k+1))) n
  have effective : Computable F := Computable.nat_rec Computable.id (Computable.const (f 0))
    (((Primrec.to_comp Primrec.nat_max).to₂.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂)
  exact ⟨F,effective,monotone_nat_of_le_succ (fun _ => le_max_left _ _),fun i => by
    cases i with | zero => exact le_rfl | succ i => exact le_max_right ..⟩

/-- In a given ordered pair of rows, successful response processing at all
sufficiently late levels yields Csima and Shore's full strong comparison. -/
theorem row_comparison (A B : Enumeration) (M : ℕ → ℕ) (grow : StrictMono M)
    (signals : ∀ F G : ℕ → ℕ, Computable F → Computable G → Monotone F → Monotone G →
      ∀ᶠ k in atTop, ∃ s u, G (M (k+1)) ≤ u ∧ Responses A B F (M k) s u) : Strong B A := by
  intro f g hf hg
  obtain ⟨F,cf,mf,bf⟩ := computable_majorant hf
  obtain ⟨G,cg,mg,bg⟩ := computable_majorant hg
  obtain ⟨N,later⟩ := eventually_atTop.mp (signals F G cf cg mf mg)
  apply eventually_atTop.mpr
  refine ⟨M N,fun x hx => ?_⟩
  have stop : ∃ k, x < M k := ⟨x+1,Nat.lt_succ_self x |>.trans_le (grow.id_le _)⟩
  let j := Nat.find stop
  have upper : x<M j := Nat.find_spec stop
  have index : N<j := by
    by_contra! low
    exact upper.not_ge ((grow.monotone low).trans hx)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (n:=j) (by omega)
  rw [hk] at upper
  have lower : M k ≤ x := Nat.le_of_not_gt (Nat.find_min stop (show k<j by omega))
  obtain ⟨s,u,size,valid⟩ := later k (by omega)
  have whole := interval_domination A B F G mf mg lower upper size valid
  exact (bf _).trans_lt ((mf (B.modulus_mono (bg x))).trans_lt whole)

end StrongSettling

end
