module

public import SolvedProblems.SettlingReduction
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE

@[expose] public section
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
