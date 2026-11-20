module

public import SolvedProblems.PromptBoundProbability

public section
open Set MeasureTheory
namespace PromptBound

private theorem lock_realize {α : Type} (s : ℕ → List α)
    (step : ∀ n, (s n).IsPrefix (s (n+1))) (long : ∀ n, n ≤ (s n).length) :
    ∃ e : ℕ → α, ∀ n, initial e (s n).length = s n := by
  have mono {i j : ℕ} (h : i ≤ j) : (s i).IsPrefix (s j) := by
    induction h with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (step _)
  let e := fun k => (s (k+1))[k]'(by have := long (k+1); omega)
  refine ⟨e, fun n => ?_⟩
  apply List.ext_getElem
  · simp [initial]
  · intro k hk hs
    simp [initial]
    exact ((mono (Nat.le_max_left (k+1) n)).getElem (by have := long (k+1); omega)).trans
      ((mono (Nat.le_max_right (k+1) n)).getElem hs).symm

private theorem lock_suffix {q} (K : Word q → Bool) (a h : History q)
    (ha : Legal K (a++h)) : Legal K h := by
  induction a with
  | nil => exact ha
  | cons r a ih => exact ih ha.2.2

private theorem lock_inside {q} (K : Word q → Bool) (h : History q)
    (ha : Legal K h) {r : Round q} (hr : r ∈ h) : K r.1 = true := by
  induction h with
  | nil => simp at hr
  | cons v vs ih =>
    rcases List.mem_cons.mp hr with rfl|hm
    · exact ha.1
    · exact ih ha.2.2 hm

private theorem lock_append_empty {q} (K : Word q → Bool) (inf : {w | K w = true}.Infinite)
    (h : History q) (hh : Legal K h) (a : Word q) (ha : K a = true) :
    Legal K ((a,[])::h) := by
  obtain ⟨y,hy,hn⟩ := inf.exists_notMem_finset (a :: sample h).toFinset
  exact ⟨ha,⟨y,hy,by simpa using hn, List.nil_prefix⟩,hh⟩

/-- If eventual correctness holds almost surely for every fixed exhaustive text,
one finite legal history makes every subsequent legal round marginally reliable. -/
theorem locking_history {q} (μ : FairLaw) (A : RandomStep q) (K : Word q → Bool)
    (inf : {w | K w = true}.Infinite) (good : ∀ e, Full K e → (∀ n, Legal K (rounds e n)) →
      ∀ᵐ w ∂μ.law, ∃ N, ∀ n ≥ N, w ∈ hit A K (rounds e (n+1))) :
    ∃ h, Legal K h ∧ ∀ g : History q, g ≠ [] → Legal K (g++h) →
      (1/2 : ℝ) ≤ μ.law.real (hit A K (g++h)) := by
  classical
  by_contra no
  have bad (h : History q) (hh : Legal K h) :
      ∃ g : History q, g ≠ [] ∧ Legal K (g++h) ∧ μ.law.real (hit A K (g++h)) < 1/2 := by
    by_contra! all
    exact no ⟨h,hh,all⟩
  let W := {x : Word q // K x = true}
  have : Nonempty W := inf.nonempty.to_subtype
  obtain ⟨enum,onto⟩ := exists_surjective_nat W
  let Node := {h : History q // Legal K h}
  let round (j : ℕ) : Round q := ((enum j).val,[])
  let move (j : ℕ) (v : Node) := bad (round j :: v.val)
    (lock_append_empty K inf _ v.property _ (enum j).property)
  let stages : ℕ → Node := Nat.rec ⟨[],trivial⟩ (fun j v ↦
    ⟨(move j v).choose ++ round j :: v.val,(move j v).choose_spec.2.1⟩)
  let path (n : ℕ) := (stages n).val.reverse
  have grow (n : ℕ) : (path n ++ [round n]).IsPrefix (path (n+1)) := by
    refine ⟨(move n (stages n)).choose.reverse,?_⟩
    simp [stages,path,List.reverse_append,List.append_assoc]
  have long (n : ℕ) : n ≤ (path n).length := by
    induction n with
    | zero => omega
    | succ n ih => have h := (grow n).length_le; simp at h; omega
  obtain ⟨e,agree⟩ := lock_realize path
    (fun n ↦ (List.prefix_append ..).trans (grow n)) long
  have rev (n : ℕ) : rounds e (path n).length = (stages n).val := by
    unfold rounds
    rw [agree n]
    exact List.reverse_reverse _
  have legal (n : ℕ) : Legal K (rounds e n) := by
    have hp := (initial_prefix e (long n)).reverse
    obtain ⟨tail,he⟩ : (rounds e n).IsSuffix (rounds e (path n).length) := hp
    apply lock_suffix K tail
    rw [he,rev n]
    exact (stages n).property
  have full : Full K e := by
    intro w
    constructor
    · intro hw
      obtain ⟨j,hj⟩ := onto (⟨w,hw⟩ : W)
      have contains := (grow j).sublist.subset (a := round j) (by simp)
      rw [← agree (j+1)] at contains
      obtain ⟨t,_,he⟩ : ∃ t < (path (j+1)).length, e t = round j := by simpa [initial] using contains
      exact ⟨t,by simpa [he,round] using congrArg Subtype.val hj⟩
    · rintro ⟨t,rfl⟩
      apply lock_inside K _ (legal (t+1)) (r := e t)
      simp [rounds_succ]
  obtain ⟨N,eventuallyGood⟩ := marginal_lock_on_text μ A K e (good e full legal)
  have len := long (N+1)
  let n := (path (N+1)).length - 1
  have hn : N ≤ n := by dsimp [n]; omega
  have endAt : n+1 = (path (N+1)).length := by dsimp [n]; omega
  have reliable := eventuallyGood n hn
  rw [endAt,rev (N+1)] at reliable
  exact ((move N (stages N)).choose_spec.2.2).not_ge reliable

/-- Every legal finite history is realized by a full legal stream. Hence the
round-by-round termination requirement on full streams tests exactly the nonempty
finite legal histories appearing in the machine definitions. -/
theorem legal_extends {q} (K : Word q → Bool) (inf : {w | K w = true}.Infinite)
    (h : History q) (leg : Legal K h) :
    ∃ e, Full K e ∧ (∀ n, Legal K (rounds e n)) ∧ rounds e h.length = h := by
  classical
  let W := {x : Word q // K x = true}
  have : Nonempty W := inf.nonempty.to_subtype
  obtain ⟨enum,onto⟩ := exists_surjective_nat W
  let e := fun n => if hn : n < h.reverse.length then h.reverse[n] else ((enum (n-h.length)).val,[])
  have hh : rounds e h.length = h := by
    have hi : initial e h.length = h.reverse := by
      apply List.ext_getElem
      · simp [initial]
      · intro i hi hit
        have hi' : i < h.length := by simpa using hit
        simp [initial,e,hi']
    simp [rounds,hi]
  have full : Full K e := by
    intro w
    constructor
    · intro hw
      obtain ⟨j,hj⟩ := onto (⟨w,hw⟩ : W)
      exact ⟨h.length+j,by simp [e,hj]⟩
    · rintro ⟨n,rfl⟩
      dsimp [e]; split
      next hn => exact lock_inside K h leg (List.mem_reverse.mp (List.getElem_mem hn))
      next => exact (enum _).property
  refine ⟨e,full,fun n => ?_,hh⟩
  by_cases hn : n ≤ h.length
  · obtain ⟨l,hl⟩ := initial_prefix e hn
    have eq : rounds e h.length = l.reverse ++ rounds e n := by
      unfold rounds
      rw [← hl,List.reverse_append]
    exact lock_suffix K _ _ (eq ▸ hh.symm ▸ leg)
  · have lower : h.length ≤ n := by omega
    induction lower with
    | refl => rwa [hh]
    | @step m hm ih =>
      have re : e m = ((enum (m-h.length)).val,[]) := by simp [e,Nat.not_lt.mpr hm]
      rw [rounds_succ,re]
      exact lock_append_empty K inf _ (by
        by_cases ht : m = h.length
        · simpa [ht,hh] using leg
        · exact ih (by omega)) _ (enum _).property

end PromptBound
