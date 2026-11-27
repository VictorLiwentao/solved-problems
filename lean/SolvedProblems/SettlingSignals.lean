module

public import SolvedProblems.SettlingEligibility

@[expose] public section

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
