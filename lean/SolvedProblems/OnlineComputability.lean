module

public import SolvedProblems.OnlineCertificatesModel
public import Mathlib.Computability.PartrecCode

public section

namespace OnlineCertificates
open Encodable

/-- A transducer that answers all required next queries reaches every legal finite
history. In total mode this includes histories inconsistent with the class. -/
theorem runOnHistory {H : (Nat → Bool) → Prop} {total : Bool} {A : Machine}
    (halts : ∀ h s m, Run A h s m → (total = true ∨ Realizes H h) →
      ∀ x, ∃ r, Answers A s x r) (h : Hist) (legal : total = true ∨ Realizes H h) :
    ∃ s m, Run A h s m := by
  induction h with
  | nil => exact ⟨_,_,.nil⟩
  | cons z h ih =>
    have tail : total = true ∨ Realizes H h := legal.imp_right (by
      rintro ⟨f,hf,ok⟩
      exact ⟨f,hf,fun y hy => ok y (List.mem_cons_of_mem _ hy)⟩)
    obtain ⟨s,m,run⟩ := ih tail
    obtain ⟨r,ans⟩ := halts h s m run tail z.1
    exact ⟨_,_, Run.step (b := z.2) run ans⟩

private theorem staged {α β : Type} [Primcodable α] [Primcodable β] {f : α → Part β}
    (hf : Partrec f) :
    ∃ step : α × Nat → Option β, Primrec step ∧
      (∀ a t u b, t ≤ u → step (a,t) = some b → step (a,u) = some b) ∧
      ∀ a b, b ∈ f a ↔ ∃ t, step (a,t) = some b := by
  obtain ⟨c, code⟩ := Nat.Partrec.Code.exists_code.mp hf
  let natStep (v : α × Nat) := Nat.Partrec.Code.evaln v.2 c (encode v.1)
  let step (v : α × Nat) := (natStep v).bind (decode₂ β)
  have eff : Primrec natStep :=
    Nat.Partrec.Code.primrec_evaln.comp (((Primrec.snd.pair (Primrec.const c))).pair
      (Primrec.encode.comp Primrec.fst))
  refine ⟨step, (Primrec.option_bind₁ Primrec.decode₂).comp eff, ?_, ?_⟩
  · intro a t u b le found
    obtain ⟨z,hz,hb⟩ := Option.bind_eq_some_iff.mp found
    exact Option.bind_eq_some_iff.mpr ⟨z, Nat.Partrec.Code.evaln_mono le hz,hb⟩
  · intro a b
    have base : Nat.Partrec.Code.eval c (encode a) = (f a).map encode := by
      simpa [encodek] using congrFun code (encode a)
    constructor
    · intro hb
      obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp (base.symm ▸ Part.mem_map encode hb)
      exact ⟨t, Option.bind_eq_some_iff.mpr ⟨_, ht, decode₂_encode b⟩⟩
    · rintro ⟨t,ht⟩
      obtain ⟨z,hz,hd⟩ := Option.bind_eq_some_iff.mp ht
      have h := Nat.Partrec.Code.evaln_sound hz
      rw [base] at h
      obtain ⟨y,hy,ey⟩ := (Part.mem_map_iff _).mp h
      exact (encode_injective (ey.trans (decode₂_eq_some.mp hd).symm)) ▸ hy

/-- Stable primitive-recursive stages represent exactly the partial computable
online transition functions, with unrestricted finite memory and running time. -/
theorem partrec_transitions (f : Hist × Nat → Part Reply) :
    Partrec f ↔ ∃ A : Machine, Primrec A ∧ Stable A ∧
      ∀ s x r, r ∈ f (s,x) ↔ Answers A s x r := by
  constructor
  · intro hf
    obtain ⟨step,eff,mono,graph⟩ := staged hf
    let A : Machine := fun v => step ((v.1,v.2.1),v.2.2)
    exact ⟨A, eff.comp ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)), fun s x => mono (s,x), fun s x => graph (s,x)⟩
  · rintro ⟨A,eff,mono,graph⟩
    let stage (p : Hist × Nat) (t : Nat) := A (p.1,p.2,t)
    have comp : Computable₂ stage := (eff.comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to_comp
    apply (Partrec.rfindOpt comp).of_eq
    intro p
    apply Part.ext
    intro r
    exact (Nat.rfindOpt_mono (fun le v => mono p.1 p.2 _ _ _ le v)).trans (graph p.1 p.2 r).symm

/-- Any ordinary partial computable predictor on the entire labelled history is a
transducer of the model. Its two successor memories record the observed label. -/
theorem historyPredictor (f : Hist × Nat → Part Bool) (hf : Partrec f) :
    ∃ A : Machine, Primrec A ∧ Stable A ∧ ∀ s x r,
      Answers A s x r ↔ ∃ b ∈ f (s,x), r = (b,(x,false)::s,(x,true)::s) := by
  let reply (p : Hist × Nat) (b : Bool) : Reply := (b,(p.2,false)::p.1,(p.2,true)::p.1)
  have branch (b : Bool) : Computable fun v : (Hist × Nat) × Bool => (v.1.2,b)::v.1.1 :=
    Computable.list_cons.comp ((Computable.snd.comp Computable.fst).pair (Computable.const b))
      (Computable.fst.comp Computable.fst)
  have make : Computable₂ reply := Computable.snd.pair ((branch false).pair (branch true))
  obtain ⟨A,eff,mono,graph⟩ := (partrec_transitions _).mp (hf.map make)
  refine ⟨A,eff,mono,fun s x r => ?_⟩
  rw [← graph s x r, Part.mem_map_iff]
  exact exists_congr fun b => and_congr_right fun _ => eq_comm

/-- A total computable enumeration of finite traces can be replaced by a
primitive-recursive enumeration of exactly the same traces. The zeroth item
fills stages at which the simulation has yet to produce an answer. -/
theorem reindexEnumeration (f : Nat → Hist) (hf : Computable f) :
    ∃ E : Nat → Hist, Primrec E ∧ ∀ s, (∃ n, E n = s) ↔ ∃ n, f n = s := by
  obtain ⟨step,eff,_,graph⟩ := staged hf.partrec
  let E (n : Nat) := (step n.unpair).getD (f 0)
  refine ⟨E, Primrec.option_getD.comp (eff.comp Primrec.unpair) (Primrec.const (f 0)), ?_⟩
  intro s
  constructor
  · rintro ⟨n,rfl⟩
    cases h : step n.unpair with
    | none => exact ⟨0,by simp [E,h]⟩
    | some y =>
      have mem := (graph n.unpair.1 y).mpr ⟨n.unpair.2,h⟩
      exact ⟨n.unpair.1, by simpa [E,h] using (Part.mem_some_iff.mp mem).symm⟩
  · rintro ⟨n,rfl⟩
    obtain ⟨t,ht⟩ := (graph n (f n)).mp (Part.mem_some _)
    exact ⟨Nat.pair n t,by simp [E,ht]⟩

/-- Any computably enumerable collection of traces containing the empty trace is the
range of a total primitive-recursive enumerator. Membership is semidecided by the
domain of an arbitrary partial recursive program. -/
theorem enumerateTraceDomain (test : Hist → Part Unit) (eff : Partrec test)
    (empty : (test []).Dom) :
    ∃ E : Nat → Hist, Primrec E ∧ ∀ s, (∃ n, E n = s) ↔ (test s).Dom := by
  obtain ⟨step,effStep,_,graph⟩ := staged eff
  let candidate (n : Nat) := (decode (α := Hist) n.unpair.1).getD []
  let E (n : Nat) := bif (step (candidate n,n.unpair.2)).isSome then candidate n else []
  have pr : Primrec candidate := Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have prStep := effStep.comp (pr.pair (Primrec.snd.comp Primrec.unpair))
  refine ⟨E, Primrec.cond (Primrec.option_isSome.comp prStep) pr (Primrec.const []), ?_⟩
  intro s
  constructor
  · rintro ⟨n,rfl⟩
    cases found : step (candidate n,n.unpair.2) with
    | none => simpa [E,found] using empty
    | some v =>
      have yes := (graph (candidate n) v).2 ⟨_,found⟩
      simpa [E,found] using yes.1
  · intro yes
    obtain ⟨t,ht⟩ := (graph s ()).1 (show () ∈ test s from ⟨yes,Subsingleton.elim ..⟩)
    exact ⟨Nat.pair (encode s) t,by simp [E,candidate,ht,encodek]⟩

end OnlineCertificates
