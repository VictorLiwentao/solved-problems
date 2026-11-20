module

public import SolvedProblems.PromptBoundEffective
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Card

@[expose] public section
namespace PromptBound
variable {q : ℕ}

def present {α : Type} [DecidableEq α] (xs : List α) (x : α) : Bool :=
  xs.any (fun y => decide (x = y))

@[simp] theorem present_iff {α : Type} [DecidableEq α] (xs : List α) (x : α) :
    present xs x = true ↔ x ∈ xs := by simp [present]

def starts {α : Type} [DecidableEq α] (p y : List α) : Bool :=
  decide (p = y.take p.length)

@[simp] theorem starts_iff {α : Type} [DecidableEq α] (p y : List α) :
    starts p y = true ↔ p.IsPrefix y := by simp [starts,List.prefix_iff_eq_take]

def scan (S : List (Word q)) (h : History q) : List (Word q) × Bool :=
  h.foldr (fun r z =>
    let seen := r.1 :: z.1
    (seen, z.2 && present S r.1 && S.any (fun y => !present seen y && starts r.2 y))) ([],true)

/-- The finite sample certifies membership of every observation and provides
a fresh completion for each earlier prompt. -/
theorem scan_spec (S : List (Word q)) (h : History q) :
    (scan S h).1 = sample h ∧ ((scan S h).2 = true ↔ Legal (present S) h) := by
  induction h with
  | nil => simp [scan,sample,Legal]
  | cons r h ih =>
    obtain ⟨a,p⟩ := r
    change a :: (scan S h).1 = a :: sample h ∧
      (((scan S h).2 && present S a && S.any (fun y => !present (a :: (scan S h).1) y && starts p y)) = true ↔
       Legal (present S) ((a,p)::h))
    simp only [ih.1, sample, Bool.and_eq_true, ih.2, present_iff,
      List.any_eq_true, Bool.not_eq_true', Bool.eq_false_iff, starts_iff, Legal, Fresh]
    grind [present_iff]

def memories (S : List (Word q)) : List (History q) :=
  ((List.range (S.length+1)).map (fun i => (Encodable.decode₂ (History q) i).getD [])).filter
    (fun h => (scan S h).2)

theorem mem_memories {S : List (Word q)} {h : History q} (hh : Legal (present S) h)
    (hle : Encodable.encode h ≤ S.length) : h ∈ memories S := by
  simp only [memories,List.mem_filter,List.mem_map,List.mem_range]
  exact ⟨⟨Encodable.encode h,by omega,by simp⟩,(scan_spec S h).2.mpr hh⟩

theorem memory_legal {S : List (Word q)} {h} (hm : h ∈ memories S) : Legal (present S) h :=
  (scan_spec S h).2.mp (List.mem_filter.mp hm).2

theorem legal_mono {A B : Word q → Bool} (hAB : ∀ y, A y = true → B y = true)
    {h} (leg : Legal A h) : Legal B h := by
  induction h with
  | nil => trivial
  | cons r h ih =>
    obtain ⟨a,p⟩ := r
    obtain ⟨obs,⟨y,hy,new,pre⟩,tail⟩ := leg
    exact ⟨hAB _ obs,⟨y,hAB _ hy,new,pre⟩,ih tail⟩

theorem sample_inside {K : Word q → Bool} {h} (leg : Legal K h) : ∀ y ∈ sample h, K y = true := by
  induction h with
  | nil => simp [sample]
  | cons r h ih =>
    obtain ⟨a,p⟩ := r
    obtain ⟨obs,_,tail⟩ := leg
    intro y hy
    change y ∈ a :: sample h at hy
    rcases List.mem_cons.mp hy with rfl|hy
    · exact obs
    · exact ih tail y hy

theorem witness_sample {K : Word q → Bool} {h} (leg : Legal K h) :
    ∃ T : List (Word q), (∀ w ∈ T, K w = true) ∧ Legal (present T) h := by
  induction h with
  | nil => exact ⟨[],by simp, trivial⟩
  | cons r h ih =>
    obtain ⟨a,p⟩ := r
    obtain ⟨obs,⟨y,hy,new,pre⟩,tail⟩ := leg
    obtain ⟨T,hT,ok⟩ := ih tail
    refine ⟨a :: y :: T, ?_,by simp,⟨y, by simp,new,pre⟩,legal_mono ?_ ok⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl|rfl|hw
      · exact obs
      · exact hy
      · exact hT _ hw
    · intro w hw; simpa using Or.inr (a := w=a) (Or.inr (a := w=y) ((present_iff ..).mp hw))

def replayPart (S : List (Word q)) (p : Word q) : History q :=
  ((S.head?).getD [],p) :: S.map (fun a => (a,[]))

def replay (S : List (Word q)) (p : Word q) (h : History q) : History q := replayPart S p ++ h

private theorem mem_head {α : Type} {S : List α} (d) (hne : S ≠ []) : S.head?.getD d ∈ S := by
  cases S <;> simp_all

theorem replay_samples {S : List (Word q)} (p) {h} (hne : S ≠ []) (ok : Legal (present S) h)
    (w) : w ∈ sample (replay S p h) ↔ w ∈ S := by
  simp only [replay,replayPart,sample,List.cons_append,List.map_cons,List.map_append,List.map_map]
  change w ∈ S.head?.getD [] :: S.map id ++ sample h ↔ _
  simp only [List.map_id,List.mem_cons,List.mem_append]
  constructor
  · rintro ((rfl|hw)|hw)
    · exact mem_head _ hne
    · exact hw
    · exact (present_iff ..).mp (sample_inside ok _ hw)
  · exact fun hw => Or.inl (.inr hw)

theorem replay_legal {K : Word q → Bool} (inf : {w | K w = true}.Infinite)
    {S : List (Word q)} {p h} (hne : S ≠ []) (inside : ∀ w ∈ S, K w = true)
    (fresh : ∃ y, Fresh K S p y) (ok : Legal (present S) h) : Legal K (replay S p h) := by
  have past := legal_mono (fun w hw => inside w ((present_iff ..).mp hw)) ok
  have fill (L : List (Word q)) (hL : ∀ w ∈ L, K w = true) :
      Legal K (L.map (fun a => (a,[])) ++ h) := by
    induction L with
    | nil => exact past
    | cons a rest ih =>
      let H := rest.map (fun a => (a,[])) ++ h
      obtain ⟨y,hy,fresh⟩ := inf.exists_notMem_finset (a :: sample H).toFinset
      exact ⟨hL a (by simp),⟨y,hy,by simpa using fresh,by simp⟩,
        ih (fun w hw => hL w (by simp [hw]))⟩
  obtain ⟨y,hy,new,pre⟩ := fresh
  refine ⟨inside _ (mem_head _ hne),⟨y,hy,?_,pre⟩,fill S inside⟩
  exact fun haveSeen => new ((replay_samples p hne ok y).mp haveSeen)

theorem replay_correct {K : Word q → Bool} {S : List (Word q)} {p h y} (hne : S ≠ [])
    (ok : Legal (present S) h) (good : Correct K (replay S p h) y) : Fresh K S p y := by
  obtain ⟨a,p',tail,eq,hy,new,pre⟩ := good
  simp only [replay,replayPart,List.cons_append,List.cons.injEq,Prod.mk.injEq] at eq
  exact ⟨hy,fun mem => new ((replay_samples p hne ok _).mpr mem),eq.1.2 ▸ pre⟩

end PromptBound
