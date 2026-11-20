module

public import SolvedProblems.PromptBoundAlgorithms
public import SolvedProblems.PromptBoundLock
public import SolvedProblems.PromptBoundQuantile
public import SolvedProblems.PromptBoundSearch

public section
open MeasureTheory
namespace PromptBound
variable {q : ℕ}

/-- On each possible sample and prompt, replay every eligible short history.
Once each last response is known on strictly more than half of the coin prefixes,
the maximum recorded length is a finite effective bound. -/
theorem random_to_bound (C : Family q) (X : Oracle) (μ : FairLaw)
    (inf : ∀ i, {w | C i w = true}.Infinite) (hgen : RandomGenerates C X μ) : LengthBound C X := by
  obtain ⟨A,hA,stable,halts,success⟩ := hgen
  let jobs (s : List (Word q) × Word q) := (memories s.1).map (replay s.1 s.2)
  let B : BoundStep q := fun z => batch (jobs z.1) (ready A) (cap A) z.2
  have hjobs : Effective X jobs := eff_map (f := fun s : List (Word q) × Word q => memories s.1)
    (g := fun u : (List (Word q) × Word q) × History q => replay u.1.1 u.1.2 u.2)
    (.comp (eff_memories X) (.basic Primrec.fst.to_comp)) (eff_replay X)
  refine ⟨B,eff_batch jobs _ _ hjobs (ready_eff A hA) (cap_eff A hA),
    fun _ _ _ _ _ le => batch_stable le, ?_, ?_⟩
  · intro S p _ poss
    obtain ⟨hne,i,within,fresh⟩ := poss
    apply batch_terminates (jobs (S,p)) (ready A) (cap A)
    intro u hu
    obtain ⟨h,hm,rfl⟩ := List.mem_map.mp hu
    have leg := replay_legal (inf i) hne within fresh (memory_legal hm)
    exact eventually_ready μ A _ stable (halts i _ (by simp [replay,replayPart]) leg)
  · intro i
    obtain ⟨h,leg,strong⟩ := locking_history μ A (C i) (inf i) (success i)
    obtain ⟨T,inside,witness⟩ := witness_sample leg
    obtain ⟨F,hF,card⟩ := (inf i).exists_subset_card_eq (Encodable.encode h)
    refine ⟨T ++ F.toList,?_,?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact inside _ hw
      · exact hF (Finset.mem_toList.mp hw)
    · intro S p _ hne incl within fresh n b assigned
      have ft : F ⊆ S.toFinset := by
        intro w hw
        exact List.mem_toFinset.mpr (incl (List.mem_append.mpr (.inr (Finset.mem_toList.mpr hw))))
      have size : Encodable.encode h ≤ S.length := by
        rw [← card]; exact (Finset.card_le_card ft).trans S.toFinset_card_le
      have ok : Legal (present S) h := legal_mono (fun w hw => (present_iff ..).mpr <|
        incl (List.mem_append.mpr (.inl ((present_iff ..).mp hw)))) witness
      have inJobs : replay S p h ∈ jobs (S,p) :=
        List.mem_map.mpr ⟨h,mem_memories ok size,rfl⟩
      have proper := replay_legal (inf i) hne within fresh ok
      have heavy := strong (replayPart S p) (by simp [replayPart]) proper
      obtain ⟨t,chosen,rfl⟩ := batch_eq_some.mp assigned
      have readyH := List.all_eq_true.mp (earlier_spec chosen) (replay S p h) inJobs
      obtain ⟨y,hitY,short⟩ := short_hit μ A _ _ t stable readyH heavy
      exact ⟨y,replay_correct hne ok hitY,short.trans (le_totalCap inJobs _ _)⟩

/-- A deterministic staged learner reads no random bits. Its finite coin budget
can also serve as its simulation clock. -/
theorem det_to_random (C : Family q) (X : Oracle) (μ : FairLaw) (hd : DetGenerates C X) :
    RandomGenerates C X μ := by
  obtain ⟨D,hD,stable,term,good⟩ := hd
  let A : RandomStep q := fun z => D (z.1,z.2.length)
  have done {h n y} (hy : D (h,n) = some y) (w : Tape) : Returns A h w y :=
    ⟨n,by simpa [A,initial] using hy⟩
  refine ⟨A,.comp hD (.pair (.basic Primrec.fst.to_comp) (.comp eff_length (.basic Primrec.snd.to_comp))),fun h u v y pre => stable h _ _ y pre.length_le,?_,?_⟩
  · intro i h ne leg
    obtain ⟨n,y,hy⟩ := term i h ne leg
    exact Filter.Eventually.of_forall fun w => ⟨y,done hy w⟩
  · intro i e full legal
    obtain ⟨N,hN⟩ := good i e full legal
    refine Filter.Eventually.of_forall fun w => ⟨N,fun n hn => ?_⟩
    obtain ⟨t,y,hy,hc⟩ := hN n hn
    exact ⟨y,done hy w,hc⟩

end PromptBound
