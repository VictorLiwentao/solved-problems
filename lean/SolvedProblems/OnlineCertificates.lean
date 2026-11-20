module

public import SolvedProblems.OnlineCertificatesReverse
public import SolvedProblems.OnlineComputability

public section

namespace OnlineCertificates

private def contains (z : Sample) (s : Hist) := decide (s.idxOf z < s.length)
private theorem contains_iff {z s} : contains z s = true ↔ z ∈ s := by
  simp [contains, List.idxOf_lt_length_iff]

private def fresh (x : Nat) (s : Hist) := !(contains (x,false) s || contains (x,true) s)
private theorem fresh_iff {x s} : fresh x s = true ↔ x ∉ s.map Prod.fst := by
  have neg (b) : contains (x,b) s = false ↔ (x,b) ∉ s := Bool.eq_false_iff.trans (not_congr contains_iff)
  simp only [fresh, Bool.not_eq_true', Bool.or_eq_false_iff, neg, List.mem_map]
  constructor
  · rintro ⟨hf,ht⟩ ⟨⟨a,b⟩,hm,rfl⟩
    cases b <;> contradiction
  · intro h
    exact ⟨fun hm => h ⟨_,hm,rfl⟩,fun hm => h ⟨_,hm,rfl⟩⟩

private def simpleBit : Hist → Bool
  | [] => true
  | z::s => fresh z.1 s && simpleBit s

private theorem simpleBit_iff (s : Hist) : simpleBit s = true ↔ Simple s := by
  induction s with
  | nil => simp [simpleBit, Simple]
  | cons z s ih => simp [simpleBit, Simple, fresh_iff, ih, Simple] at *

private def inspect (A : Machine) (t : Nat) (z : Sample) (s : Hist) : Option Hist :=
  (A (s,z.1,t)).bind fun r =>
    bif r.1 == z.2 then none else some (bif z.2 then r.2.2 else r.2.1)

/-- Replay one ordering with a common time bound, retaining its final state only when every prediction errs. -/
private def wrongAt (A : Machine) (t : Nat) (h : Hist) : Option Hist :=
  h.foldr (fun z st => st.bind (inspect A t z)) (some [])

private inductive Wrong (A : Machine) : Hist → Hist → Prop
  | nil : Wrong A [] []
  | step {h s x b r} : Wrong A h s → Answers A s x r → r.1 ≠ b →
      Wrong A ((x,b)::h) (if b then r.2.2 else r.2.1)

private theorem Wrong.run {A h s} (w : Wrong A h s) : Run A h s h.length := by
  induction w with
  | nil => exact .nil
  | @step h s x b r w ans hb ih => simpa [hb] using Run.step (b := b) ih ans

private theorem wrongAt_sound {A t h s} (hw : wrongAt A t h = some s) : Wrong A h s := by
  induction h generalizing s with
  | nil => simp [wrongAt] at hw; subst s; exact .nil
  | cons z h ih =>
    change (wrongAt A t h).bind (inspect A t z) = some s at hw
    obtain ⟨v, hv, hp⟩ := Option.bind_eq_some_iff.mp hw
    unfold inspect at hp
    obtain ⟨r, hr, he⟩ := Option.bind_eq_some_iff.mp hp
    simp only [Bool.cond_eq_ite] at he
    split at he
    · contradiction
    · rename_i hn
      cases Option.some.inj he
      exact .step (ih hv) ⟨t,hr⟩ (by simpa using hn)

private theorem Wrong.eventually {A h s} (stable : Stable A) (w : Wrong A h s) :
    ∃ t, ∀ u ≥ t, wrongAt A u h = some s := by
  induction w with
  | nil => exact ⟨0,fun _ _ => rfl⟩
  | @step h s x b r w ans hb ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨t,ht⟩ := ans
    refine ⟨max n t,fun u hu => ?_⟩
    change (wrongAt A u h).bind (inspect A u (x,b)) = _
    rw [hn _ (Nat.le_trans (Nat.le_max_left ..) hu)]
    simp [inspect, stable _ _ _ _ _ (Nat.le_trans (Nat.le_max_right ..) hu) ht, hb]

private def candidate (A : Machine) (d : Nat) (h : Hist) (t : Nat) :=
  bif simpleBit h && decide (h.length ≤ d+1) && (wrongAt A t h).isSome then h else []

/-- One coordinate codes an ordered candidate, the other a simulation bound. Failed tests list the empty trace. -/
private noncomputable def enumerate (A : Machine) (d : Nat) (n : Nat) :=
  candidate A d ((Encodable.decode (α := Hist) n.unpair.1).getD []) n.unpair.2

private theorem enum_properties {A d n} :
    Simple (enumerate A d n) ∧ (enumerate A d n).length ≤ d+1 ∧
    ∃ s, Wrong A (enumerate A d n) s := by
  unfold enumerate candidate
  simp only [Bool.cond_eq_ite]
  split
  · rename_i good
    simp only [Bool.and_eq_true, decide_eq_true_eq, simpleBit_iff, Option.isSome_iff_exists] at good
    obtain ⟨⟨hh,hlen⟩,s,hs⟩ := good
    exact ⟨hh,hlen,s,wrongAt_sound hs⟩
  · exact ⟨by simp [Simple], Nat.zero_le _, [], .nil⟩

private theorem enum_hits {A d h s} (stable : Stable A) (simple : Simple h)
    (len : h.length ≤ d+1) (w : Wrong A h s) : ∃ i, enumerate A d i = h := by
  obtain ⟨t,ht⟩ := w.eventually stable
  exact ⟨Nat.pair (Encodable.encode h) t, by
    simp [enumerate,candidate, (simpleBit_iff _).2 simple,len,ht t (Nat.le_refl _)]⟩

private theorem same_len {s t} (ss : Simple s) (st : Simple t) (eqv : Same s t) :
    s.length = t.length := by
  have hs : s.Nodup := List.Pairwise.of_map Prod.fst (fun _ _ hn eq => hn (congrArg Prod.fst eq)) ss
  have ht : t.Nodup := List.Pairwise.of_map Prod.fst (fun _ _ hn eq => hn (congrArg Prod.fst eq)) st
  exact ((List.perm_ext_iff_of_nodup hs ht).2 eqv).length_eq

private theorem same_real {H s t} (eqv : Same s t) (real : Realizes H t) : Realizes H s := by
  obtain ⟨f,hf,ok⟩ := real
  exact ⟨f,hf,fun z hz => ok z ((eqv z).1 hz)⟩

private theorem forward {H d total} (L : Learnable H d total)
    (enumerable : ∀ A, Primrec A → Primrec (enumerate A d)) : Certificates H d total := by
  obtain ⟨A,pa,stable,halt,bound⟩ := L
  refine ⟨enumerate A d,enumerable _ pa,fun i => ⟨enum_properties.1,enum_properties.2.1⟩,?_,?_,?_⟩
  · obtain ⟨i,hi⟩ := enum_hits (d := d) stable (by simp [Simple]) (by simp) Wrong.nil
    exact ⟨i,hi ▸ fun _ => Iff.rfl⟩
  · rintro h simple ⟨i,eqv⟩ real
    obtain ⟨hs,_,s,hw⟩ := enum_properties (A := A) (d := d) (n := i)
    simpa [same_len hs simple eqv] using bound _ _ _ hw.run (same_real eqv real)
  · rintro h simple ⟨i,eqv⟩ len ok x hx
    obtain ⟨hs,_,s,hw⟩ := enum_properties (A := A) (d := d) (n := i)
    obtain ⟨r,hr⟩ := halt _ _ _ hw.run (ok.imp_right (same_real eqv)) x
    have nd : Simple ((x,!r.1)::enumerate A d i) := by
      refine List.nodup_cons.mpr ⟨?_,hs⟩
      intro mem
      obtain ⟨⟨y,b⟩,he,rfl⟩ := List.mem_map.mp mem
      exact hx b ((eqv _).1 he)
    have sz : ((x,!r.1)::enumerate A d i).length ≤ d+1 := by simp [same_len hs simple eqv,len]
    obtain ⟨j,hj⟩ := enum_hits stable nd sz (Wrong.step hw hr (by cases r.1 <;> decide))
    refine ⟨!r.1,j,?_⟩
    rw [hj]
    intro p
    simp only [List.mem_cons, eqv p]


private def subsetBit (s t : Hist) := s.foldr (fun z ok => contains z t && ok) true
private def sameBit (s t : Hist) := subsetBit s t && subsetBit t s

private theorem subsetBit_iff {s t} : subsetBit s t = true ↔ s ⊆ t := by
  induction s with
  | nil => simp [subsetBit]
  | cons z s ih =>
    change (contains z t && subsetBit s t) = true ↔ _
    simp [contains_iff, ih, List.cons_subset]

private theorem sameBit_iff {s t} : sameBit s t = true ↔ Same s t := by
  simp only [sameBit, Bool.and_eq_true, subsetBit_iff]
  exact ⟨fun ⟨st,ts⟩ p => ⟨fun h => st h,fun h => ts h⟩,
    fun h => ⟨fun _ hp => (h _).mp hp,fun _ hp => (h _).mpr hp⟩⟩

/-- Examine one enumeration output for a valid signed extension. -/
private def scanOne (E : Nat → Hist) (s : Hist) (x n : Nat) : Option Bool :=
  bif sameBit (E n) ((x,false)::s) then some false
  else bif sameBit (E n) ((x,true)::s) then some true else none

/-- Keep the first sign witnessed by the enumeration so that later stages preserve its answer. -/
private def search (E : Nat → Hist) (s : Hist) (x : Nat) (n : Nat) : Option Bool :=
  Nat.rec none (fun i prev => prev <|> scanOne E s x i) n

private theorem search_mono {E s x i j b} (ij : i ≤ j) (h : search E s x i = some b) :
    search E s x j = some b := by
  induction ij with
  | refl => exact h
  | step _ ih => change (search E s x _ <|> _) = _; rw [ih]; rfl

private theorem search_sound {E s x n b} (h : search E s x n = some b) :
    Listed E ((x,b)::s) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    change (search E s x n <|> scanOne E s x n) = some b at h
    cases he : search E s x n with
    | some c =>
      simp [he] at h
      subst c
      exact ih he
    | none =>
      rw [he] at h
      change scanOne E s x n = some b at h
      unfold scanOne at h
      cases hf : sameBit (E n) ((x,false)::s) <;> simp [hf] at h
      · cases ht : sameBit (E n) ((x,true)::s) <;> simp [ht] at h
        subst b
        exact ⟨n,sameBit_iff.mp ht⟩
      · subst b
        exact ⟨n,sameBit_iff.mp hf⟩

private theorem search_complete {E s x} (hit : ∃ b, Listed E ((x,b)::s)) :
    ∃ n b, search E s x n = some b := by
  obtain ⟨b,i,hi⟩ := hit
  refine ⟨i+1,?_⟩
  change ∃ b, (search E s x i <|> scanOne E s x i) = some b
  cases h : search E s x i with
  | some c => exact ⟨c,rfl⟩
  | none =>
    change ∃ c, scanOne E s x i = some c
    have he := sameBit_iff.mpr hi
    cases b
    · exact ⟨false,by simp [scanOne,he]⟩
    · cases hf : sameBit (E i) ((x,false)::s) <;> simp [scanOne,hf,he]

private def extensionReply (s : Hist) (x : Nat) (b : Bool) : Reply :=
  (!b, (bif b then s else (x,false)::s), (bif b then (x,true)::s else s))

private def makeMachine (E : Nat → Hist) (d : Nat) : Machine := fun (s,x,t) =>
  bif contains (x,false) s then some (false,s,s)
  else bif contains (x,true) s then some (true,s,s)
  else bif decide (d < s.length) then some (false,s,s)
  else (search E s x t).map (extensionReply s x)

private theorem make_stable (E d) : Stable (makeMachine E d) := by
  intro s x t u r le h
  unfold makeMachine at h ⊢
  cases a : contains (x,false) s <;> cases b : contains (x,true) s <;>
    cases k : decide (d < s.length) <;> simp only [a,b,k, Bool.cond_true, Bool.cond_false] at h ⊢ <;>
      try exact h
  cases hq : search E s x t with
  | none => simp [hq] at h
  | some c => rw [search_mono le hq]; simpa only [hq] using h

private theorem contains_prim : Primrec₂ contains :=
  ((Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
    (Primrec.list_length.comp Primrec.snd)).decide).to₂

private theorem fresh_prim : Primrec₂ fresh :=
  (Primrec.not.comp (Primrec.or.comp
    (contains_prim.comp (Primrec.fst.pair (Primrec.const false)) Primrec.snd)
    (contains_prim.comp (Primrec.fst.pair (Primrec.const true)) Primrec.snd))).to₂

private theorem simple_prim : Primrec simpleBit := by
  apply (Primrec.list_rec (f := id) (g := fun _ => true)
    (h := fun _ (p : Sample × Hist × Bool) => fresh p.1.1 p.2.1 && p.2.2)
    Primrec.id (Primrec.const true) ?_).of_eq
  · intro h
    induction h with
    | nil => rfl
    | cons z s ih => exact congrArg (fun b => fresh z.1 s && b) ih
  · exact (Primrec.and.comp (fresh_prim.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂

private theorem inspect_prim {A} (pa : Primrec A) :
    Primrec (fun p : (Nat × Sample) × Hist => inspect A p.1.1 p.1.2 p.2) := by
  unfold inspect
  apply Primrec.option_bind (pa.comp (Primrec.snd.pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.fst))))
  unfold Primrec₂
  apply Primrec.cond
  · exact Primrec.beq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  · exact Primrec.const none
  · apply Primrec.option_some.comp
    exact Primrec.cond (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

private theorem wrong_prim {A} (pa : Primrec A) : Primrec₂ (wrongAt A) := by
  unfold Primrec₂
  apply Primrec.list_foldr (h := fun (a : Nat × Hist) (u : Sample × Option Hist) =>
    u.2.bind (inspect A a.1 u.1)) Primrec.snd (Primrec.const (some []))
  unfold Primrec₂
  apply Primrec.option_bind (Primrec.snd.comp Primrec.snd)
  exact ((inspect_prim pa).comp
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)).to₂

private theorem enumerate_prim (d : Nat) (A : Machine) (pa : Primrec A) :
    Primrec (enumerate A d) := by
  have prH : Primrec (fun n : Nat => (Encodable.decode (α := Hist) n.unpair.1).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  apply Primrec.cond _ prH (Primrec.const [])
  exact Primrec.and.comp
    (Primrec.and.comp (simple_prim.comp prH)
      (Primrec.nat_le.comp (Primrec.list_length.comp prH) (Primrec.const (d+1))).decide)
    (Primrec.option_isSome.comp ((wrong_prim pa).comp (Primrec.snd.comp Primrec.unpair) prH))

private theorem subset_prim : Primrec₂ subsetBit := by
  unfold Primrec₂
  apply Primrec.list_foldr (h := fun (a : Hist × Hist) (u : Sample × Bool) =>
    contains u.1 a.2 && u.2) Primrec.fst (Primrec.const true)
  exact (Primrec.and.comp (contains_prim.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)).to₂

private theorem same_prim : Primrec₂ sameBit :=
  (Primrec.and.comp (subset_prim.comp Primrec.fst Primrec.snd)
    (subset_prim.comp Primrec.snd Primrec.fst)).to₂

private theorem one_prim {E} (pe : Primrec E) :
    Primrec (fun p : (Hist × Nat) × Nat => scanOne E p.1.1 p.1.2 p.2) := by
  unfold scanOne
  have ext (b : Bool) : Primrec (fun p : (Hist × Nat) × Nat => sameBit (E p.2) ((p.1.2,b)::p.1.1)) :=
    same_prim.comp (pe.comp Primrec.snd)
      (Primrec.list_cons.comp ((Primrec.snd.comp Primrec.fst).pair (Primrec.const b)) (Primrec.fst.comp Primrec.fst))
  exact Primrec.cond (ext false) (Primrec.const (some false))
    (Primrec.cond (ext true) (Primrec.const (some true)) (Primrec.const none))

private theorem search_prim {E} (pe : Primrec E) :
    Primrec (fun p : (Hist × Nat) × Nat => search E p.1.1 p.1.2 p.2) := by
  apply Primrec.nat_rec (g := fun (a : Hist × Nat) (p : Nat × Option Bool) =>
    p.2 <|> scanOne E a.1 a.2 p.1) (Primrec.const none)
  exact (Primrec.option_orElse.comp (Primrec.snd.comp Primrec.snd)
    ((one_prim pe).comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))).to₂

private theorem reply_prim : Primrec (fun p : (Hist × Nat) × Bool => extensionReply p.1.1 p.1.2 p.2) := by
  have ext (b : Bool) : Primrec (fun p : (Hist × Nat) × Bool => (p.1.2,b)::p.1.1) :=
    Primrec.list_cons.comp ((Primrec.snd.comp Primrec.fst).pair (Primrec.const b)) (Primrec.fst.comp Primrec.fst)
  exact (Primrec.not.comp Primrec.snd).pair
    ((Primrec.cond Primrec.snd (Primrec.fst.comp Primrec.fst) (ext false)).pair
     (Primrec.cond Primrec.snd (ext true) (Primrec.fst.comp Primrec.fst)))

private theorem make_prim (d : Nat) {E} (pe : Primrec E) : Primrec (makeMachine E d) := by
  have seen (b : Bool) : Primrec (fun p : Hist × Nat × Nat => contains (p.2.1,b) p.1) :=
    contains_prim.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.const b)) Primrec.fst
  have known (b : Bool) : Primrec (fun p : Hist × Nat × Nat => some (b,p.1,p.1)) :=
    Primrec.option_some.comp ((Primrec.const b).pair (Primrec.fst.pair Primrec.fst))
  apply Primrec.cond (seen false) (known false)
  apply Primrec.cond (seen true) (known true)
  apply Primrec.cond (Primrec.nat_lt.comp (Primrec.const d) (Primrec.list_length.comp Primrec.fst)).decide (known false)
  apply Primrec.option_map ((search_prim pe).comp ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd)))
  exact (reply_prim.comp (((Primrec.fst.comp Primrec.fst).pair
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)).to₂


private theorem unique_bit {s : Hist} (hs : Simple s) {x b c} (hb : (x,b) ∈ s) (hc : (x,c) ∈ s) :
    b = c := by
  induction s with
  | nil => contradiction
  | cons z s ih =>
    obtain ⟨freshZ,tail⟩ := List.nodup_cons.mp hs
    rcases List.mem_cons.mp hb with eq | hm
    · subst z
      rcases List.mem_cons.mp hc with eq | hc
      · exact congrArg Prod.snd eq.symm
      · exact False.elim (freshZ (List.mem_map.mpr ⟨_,hc,rfl⟩))
    · rcases List.mem_cons.mp hc with eq | hc
      · subst z
        exact False.elim (freshZ (List.mem_map.mpr ⟨_,hm,rfl⟩))
      · exact ih tail hm hc

private theorem make_rule (E d) : Rule E d (makeMachine E d) := by
  refine ⟨?_,?_,?_⟩
  · intro s x hs b hb
    refine ⟨0,?_⟩
    have known := contains_iff.mpr hb
    cases b
    · simp [makeMachine,known]
    · have absent : contains (x,false) s = false := by
        apply Bool.eq_false_iff.mpr
        intro bad
        exact Bool.noConfusion (unique_bit hs (contains_iff.mp bad) hb)
      simp [makeMachine,known,absent]
  · intro s x _ hf large
    have absent (b) : contains (x,b) s = false := Bool.eq_false_iff.mpr (fun he => hf b (contains_iff.mp he))
    exact ⟨0,by simp [makeMachine,absent,large]⟩
  · intro s x _ hf small hit
    obtain ⟨n,b,hb⟩ := search_complete hit
    have absent (c) : contains (x,c) s = false := Bool.eq_false_iff.mpr (fun he => hf c (contains_iff.mp he))
    refine ⟨b,search_sound hb,n,?_⟩
    cases b <;> simp [makeMachine,absent,Nat.not_lt.mpr small,hb,extensionReply]

/-- For every class and budget, computable bounded-mistake learning is equivalent
to the stated finite-evidence criterion in both the partial and total models. -/
theorem uniformCriterion (H : (Nat → Bool) → Prop) (d : Nat) (total : Bool) :
    Learnable H d total ↔ Certificates H d total := by
  refine ⟨fun L => forward L (enumerate_prim d),?_⟩
  rintro ⟨E,pe,small,empty,stop,extend⟩
  exact fromRule small empty stop extend (make_prim d pe) (make_stable E d) (make_rule E d)

end OnlineCertificates
