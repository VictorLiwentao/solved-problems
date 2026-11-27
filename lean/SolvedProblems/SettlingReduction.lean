module

public import SolvedProblems.SettlingOracle

@[expose] public section
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
