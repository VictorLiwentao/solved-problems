module

public import SolvedProblems.PromptBoundProbability
public import SolvedProblems.PromptBoundEffective

@[expose] public section
open MeasureTheory Set

namespace PromptBound

/-- At this finite stage a strict majority of all equally likely branches has returned. -/
def ready {q} (A : RandomStep q) (h : History q) (t : ℕ) : Bool :=
  decide ((coinWords t).length < 2*((coinWords t).filter fun u => (A (h,u)).isSome).length)

/-- Maximum length of any returned word at this finite stage. -/
def cap {q} (A : RandomStep q) (h : History q) (t : ℕ) : ℕ :=
  (coinWords t).foldr (fun u b => max ((A (h,u)).getD []).length b) 0

theorem coinWords_mem {u : List Bool} {t : ℕ} : u ∈ coinWords t ↔ u.length = t := by
  induction t generalizing u with
  | zero => simp [coinWords]
  | succ t ih =>
    cases u with
    | nil => simp [coinWords]
    | cons a u =>
      cases a <;> simp [coinWords, List.mem_flatMap, ih]

theorem coinWords_length_pos (t : ℕ) : 0 < (coinWords t).length := by
  have h : List.replicate t false ∈ coinWords t := coinWords_mem.mpr (by simp)
  exact List.length_pos_of_mem h

theorem coinWords_eff {X} : Effective X coinWords := by
  have step : Effective X (fun z : (ℕ × ℕ) × List (List Bool) =>
      z.2.flatMap fun u => [false::u,true::u]) := by
    change Effective X (fun z : (ℕ × ℕ) × List (List Bool) =>
      (z.2.map (fun u => [false::u,true::u])).flatten)
    apply Effective.comp eff_flatten
    apply eff_map (g:=fun z : ((ℕ × ℕ) × List (List Bool)) × List Bool => [false::z.2,true::z.2]) (.basic Primrec.snd.to_comp)
    fun_prop
  have rr := Effective.recNat (X:=X) (n:=fun t : ℕ => t) (z:=fun _ => [[]])
    (g:=fun z : (ℕ × ℕ) × List (List Bool) => z.2.flatMap fun u => [false::u,true::u]) eff_id (eff_const _) step
  convert rr using 1
  funext t
  change coinWords t = Nat.rec [[]] (fun _ v => v.flatMap fun u => [false::u,true::u]) t
  induction t with
  | zero => rfl
  | succ n ih => change _ = List.flatMap _ _; rw [← ih]; rfl

theorem ready_eff {q X} (A : RandomStep q) (hA : Effective X A) :
    Effective X (fun p : History q × ℕ => ready A p.1 p.2) := by
  let f (p : History q × ℕ) := coinWords p.2
  have ef : Effective X f := .comp coinWords_eff (.basic Primrec.snd.to_comp)
  have pred : Effective X (fun z : (History q × ℕ) × List Bool => (A (z.1.1,z.2)).isSome) :=
    .comp eff_isSome (.comp hA (by fun_prop))
  exact .comp eff_blt (.pair (.comp eff_length ef)
    (.comp eff_mul (.pair (eff_const 2) (.comp eff_length (eff_filter ef pred)))))

theorem cap_eff {q X} (A : RandomStep q) (hA : Effective X A) :
    Effective X (fun p : History q × ℕ => cap A p.1 p.2) := by
  apply Effective.foldList (g:=fun z : ((History q × ℕ) × List Bool) × ℕ =>
    max ((A (z.1.1.1,z.1.2)).getD []).length z.2) (.comp coinWords_eff (.basic Primrec.snd.to_comp)) (eff_const 0)
  apply eff_max_comp
  · apply Effective.comp eff_length
    exact eff_getD_comp _ _ (.comp hA (by fun_prop)) (eff_const [])
  · fun_prop

private def halted {q} (A : RandomStep q) (h : History q) (t : ℕ) : Set Tape :=
  {w | (A (h,initial w t)).isSome = true}

private theorem half_iff {q} (μ : FairLaw) (A : RandomStep q) (h : History q) (t : ℕ) :
    1/2 < μ.law.real (halted A h t) ↔ ready A h t = true := by
  unfold halted ready
  rw [μ.uniform t (fun u => (A (h,u)).isSome)]
  have pos : 0 < ((coinWords t).length : ℝ) := by exact_mod_cast coinWords_length_pos t
  rw [lt_div_iff₀ pos,decide_eq_true_eq]
  constructor
  · intro ht
    have e : ((coinWords t).length : ℝ) < 2*((coinWords t).filter fun u => (A (h,u)).isSome).length := by
      linarith
    exact_mod_cast e
  · intro ht
    have e : ((coinWords t).length : ℝ) < 2*((coinWords t).filter fun u => (A (h,u)).isSome).length := by
      exact_mod_cast ht
    linarith

theorem eventually_ready {q} (μ : FairLaw) (A : RandomStep q) (h : History q)
    (stable : ∀ h u v y, List.IsPrefix u v → A (h,u)=some y → A (h,v)=some y)
    (halts : ∀ᵐ w ∂μ.law, ∃ y, Returns A h w y) :
    ∃ t, ∀ n ≥ t, ready A h n = true := by
  have mono : Monotone (halted A h) := by
    intro n m hnm w hw
    obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp hw
    exact Option.isSome_iff_exists.mpr ⟨y,stable _ _ _ _ (initial_prefix _ hnm) hy⟩
  have cover : ∀ᵐ w ∂μ.law, ∃ n, w ∈ halted A h n := by
    filter_upwards [halts] with w hw
    obtain ⟨y,n,hy⟩ := hw
    exact ⟨n,Option.isSome_iff_exists.mpr ⟨y,hy⟩⟩
  obtain ⟨t,ht⟩ := large_stage μ _ mono cover (r:=1/2) (by norm_num)
  exact ⟨t,fun n hn => (half_iff μ A h n).mp (ht.trans_le (measureReal_mono (mono hn)))⟩

private theorem len_le_fold {q} (A : RandomStep q) (h : History q)
    (U : List (List Bool)) {u : List Bool} (hu : u ∈ U) :
    ((A (h,u)).getD []).length ≤ U.foldr (fun v b => max ((A (h,v)).getD []).length b) 0 := by
  induction U with
  | nil => simp at hu
  | cons v V ih =>
    rcases List.mem_cons.mp hu with rfl|hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem short_hit {q} (μ : FairLaw) (A : RandomStep q) (K : Word q → Bool)
    (h : History q) (t : ℕ)
    (stable : ∀ h u v y, List.IsPrefix u v → A (h,u)=some y → A (h,v)=some y)
    (ok : ready A h t = true) (hitHalf : 1/2 ≤ μ.law.real (hit A K h)) :
    ∃ y, Correct K h y ∧ y.length ≤ cap A h t := by
  have gt := (half_iff μ A h t).mpr ok
  have measurable : MeasurableSet (halted A h t) := measurable_tape_test t (fun u => (A (h,u)).isSome = true)
  have both : (halted A h t ∩ hit A K h).Nonempty := by
    by_contra hnon
    have sub : hit A K h ⊆ (halted A h t)ᶜ := fun w hw hw' => hnon ⟨w,hw',hw⟩
    have bound := measureReal_mono (μ:=μ.law) sub
    rw [measureReal_compl measurable] at bound
    have total : μ.law.real univ = 1 := by simp [Measure.real]
    rw [total] at bound
    linarith
  obtain ⟨w,done,win⟩ := both
  obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp done
  obtain ⟨z,⟨n,hz⟩,hc⟩ := win
  have eq : y=z := by
    rcases le_total t n with htn|hnt
    · exact Option.some.inj ((stable _ _ _ _ (initial_prefix _ htn) hy).symm.trans hz)
    · exact Option.some.inj (hy.symm.trans (stable _ _ _ _ (initial_prefix _ hnt) hz))
  subst z
  have mem : initial w t ∈ coinWords t := coinWords_mem.mpr (by simp [initial])
  exact ⟨y,hc,by simpa [cap,hy] using len_le_fold A h _ mem⟩

end PromptBound
