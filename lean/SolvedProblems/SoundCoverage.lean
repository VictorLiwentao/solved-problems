module

public import SolvedProblems.SoundCoverageModel
public import Std

public section

namespace SoundCoverage

private theorem mem_prefix {e : Nat → Nat} {n x : Nat} :
    x ∈ history e n ↔ ∃ k < n, e k = x := by simp [history]

private theorem prefix_inside {e A} (h : Enumerates e A) (n) : Inside (history e n) A := by
  intro x hx
  obtain ⟨k, _, hk⟩ := mem_prefix.mp hx
  exact (h x).mpr ⟨k, hk⟩

/-- Include each member at its own index, filling unused positions with a member. -/
private theorem exists_text {A : Language} (hne : ∃ x, A x) : ∃ e, Enumerates e A := by
  classical
  obtain ⟨a, ha⟩ := hne
  let e := fun x => if A x then x else a
  refine ⟨e, fun x => ⟨fun hx => ⟨x, by simp [e, hx]⟩, ?_⟩⟩
  rintro ⟨k, rfl⟩
  dsimp [e]
  split <;> assumption

/-- A nested sequence of finite histories of unbounded length determines a text. -/
private theorem realize (s : Nat → List Nat)
    (step : ∀ n, (s n).IsPrefix (s (n+1))) (long : ∀ n, n ≤ (s n).length) :
    ∃ e, ∀ n, history e (s n).length = s n := by
  have mono {i j : Nat} (h : i ≤ j) : (s i).IsPrefix (s j) := by
    induction h with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (step _)
  let e := fun k => (s (k+1))[k]'(by have := long (k+1); omega)
  refine ⟨e, fun n => ?_⟩
  apply List.ext_getElem
  · simp [history]
  · intro k hk hs
    simp [history]
    let m := max (k+1) n
    exact ((mono (Nat.le_max_left (k+1) n)).getElem (by have := long (k+1); omega)).trans
      ((mono (Nat.le_max_right (k+1) n)).getElem hs).symm

/-- Success forces a finite history whose every on-target extension covers all unseen points. -/
private theorem coverage_lock {A : Language} {L : Learner} {e₀ : Nat → Nat}
    (he : Enumerates e₀ A)
    (success : ∀ e, Enumerates e A → ∃ N, ∀ n ≥ N, Covers L A (history e n)) :
    ∃ t, Inside t A ∧ ∀ s, t.IsPrefix s → Inside s A → Covers L A s := by
  classical
  apply Classical.byContradiction
  intro noLock
  have bad (t) (ht : Inside t A) :
      ∃ s, t.IsPrefix s ∧ Inside s A ∧ ¬ Covers L A s := by
    apply Classical.byContradiction
    intro noBad
    apply noLock
    refine ⟨t, ht, fun s hp hs => Classical.byContradiction fun h => ?_⟩
    exact noBad ⟨s, hp, hs, h⟩
  let extend (n : Nat) (t : {s // Inside s A}) :=
    bad (t.val ++ [e₀ n]) (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact t.property x hx
      · have eq : x = e₀ n := by simpa using hx
        exact (he x).mpr ⟨n, eq.symm⟩)
  let stages : Nat → {s // Inside s A} := Nat.rec ⟨[], by simp [Inside]⟩
    (fun n t => ⟨(extend n t).choose, (extend n t).choose_spec.2.1⟩)
  let s := fun n => (stages n).val
  have extn (n) : (s n ++ [e₀ n]).IsPrefix (s (n+1)) ∧ ¬ Covers L A (s (n+1)) :=
    ⟨(extend n (stages n)).choose_spec.1, (extend n (stages n)).choose_spec.2.2⟩
  have long (n) : n ≤ (s n).length := by
    induction n with
    | zero => omega
    | succ n ih =>
      have h := (extn n).1.length_le
      simp at h
      omega
  obtain ⟨e, agrees⟩ := realize s (fun n => (List.prefix_append ..).trans (extn n).1) long
  have full : Enumerates e A := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := (he x).mp hx
      have hm := (extn k).1.sublist.subset (a := e₀ k) (by simp)
      rw [← agrees (k+1)] at hm
      obtain ⟨j, _, hj⟩ := mem_prefix.mp hm
      exact ⟨j, hj⟩
    · rintro ⟨k, rfl⟩
      apply (stages (k+1)).property
      change e k ∈ s (k+1)
      rw [← agrees (k+1)]
      exact mem_prefix.mpr ⟨k, by have := long (k+1); omega, rfl⟩
  obtain ⟨N, hN⟩ := success e full
  apply (extn N).2
  rw [← agrees (N+1)]
  exact hN _ (by have := long (N+1); omega)

private theorem necessity {H F : Family} (nonempty : ∀ i, ∃ x, H i x)
    (ambient : ∀ i, Sub (H i) (F i)) (learn : Learnable H F) : HasWitnesses H F := by
  obtain ⟨L, good⟩ := learn
  intro i
  obtain ⟨ei, hi⟩ := exists_text (nonempty i)
  obtain ⟨t, ht, lock⟩ := coverage_lock (L := L) hi (fun e he => by
    obtain ⟨N, hN⟩ := good i e he
    exact ⟨N, fun n hn => (hN n hn).1⟩)
  refine ⟨t, ht, ?_⟩
  intro j htj hji
  obtain ⟨ej, hj⟩ := exists_text (nonempty j)
  -- Prepend the locking history to a full text for j.
  let e (k : Nat) := if h : k < t.length then t[k] else ej (k - t.length)
  have full : Enumerates e (H j) := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := (hj x).mp hx
      exact ⟨t.length + k, by simp [e, show ¬ t.length + k < t.length by omega]⟩
    · rintro ⟨k, rfl⟩
      dsimp [e]
      split
      · exact htj _ (List.getElem_mem ..)
      · exact (hj _).mpr ⟨_, rfl⟩
  obtain ⟨N, hN⟩ := good j e full
  let n := max N t.length
  have hp : t.IsPrefix (history e n) := by
    apply List.prefix_iff_getElem.mpr
    refine ⟨?_, ?_⟩
    · simpa [history] using Nat.le_max_right N t.length
    · intro k hk
      simp [history, e, hk]
  have hjn := prefix_inside full n
  intro x hx
  by_cases seen : x ∈ history e n
  · exact ambient j x (hjn x seen)
  · exact (hN n (Nat.le_max_left ..)).2 x
      (lock _ hp (fun y hy => hji y (hjn y hy)) x hx seen)

private theorem eventually_seen {A : Language} {e} (he : Enumerates e A)
    (t : List Nat) (ht : Inside t A) :
    ∃ N, ∀ n ≥ N, Inside t (fun x => x ∈ history e n) := by
  induction t with
  | nil => exact ⟨0, by simp [Inside]⟩
  | cons x xs ih =>
    obtain ⟨k, hk⟩ := (he x).mp (ht x (by simp))
    obtain ⟨M, hM⟩ := ih (fun y hy => ht y (by simp [hy]))
    refine ⟨max M (k+1), ?_⟩
    intro n hn y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact mem_prefix.mpr ⟨k, by omega, hk⟩
    · exact hM n (by omega) y hy

/-- At each finite cutoff, one time suffices to eliminate all incompatible candidates. -/
theorem eliminate {H : Family} {j e} (he : Enumerates e (H j)) (b : Nat) :
    ∃ N, ∀ n ≥ N, ∀ i < b, Inside (history e n) (H i) → Sub (H j) (H i) := by
  classical
  induction b with
  | zero => exact ⟨0, by intros; omega⟩
  | succ b ih =>
    obtain ⟨M, hM⟩ := ih
    by_cases sub : Sub (H j) (H b)
    · refine ⟨M, fun n hn i hi hs => ?_⟩
      by_cases eq : i = b
      · simpa [eq] using sub
      · exact hM n hn i (by omega) hs
    · have missing : ∃ x, H j x ∧ ¬ H b x := by
        apply Classical.byContradiction
        intro h
        exact sub (fun x hx => Classical.byContradiction fun h' => h ⟨x, hx, h'⟩)
      obtain ⟨x, hx, outside⟩ := missing
      obtain ⟨k, hk⟩ := (he x).mp hx
      refine ⟨max M (k+1), fun n hn i hi hs => ?_⟩
      by_cases eq : i = b
      · subst i
        exact False.elim (outside (hs x (mem_prefix.mpr ⟨k, by omega, hk⟩)))
      · exact hM n (by omega) i (by omega) hs

private theorem least {P : Nat → Prop} (h : ∃ i, P i) :
    ∃ i, P i ∧ ∀ k, P k → i ≤ k := by
  classical
  obtain ⟨i, hi⟩ := h
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases lower : ∃ k < i, P k
    · obtain ⟨k, hk, hpk⟩ := lower
      exact ih k hk hpk
    · exact ⟨i, hi, fun k hk => by
        apply Nat.le_of_not_gt
        exact fun hki => lower ⟨k, hki, hk⟩⟩

private theorem sufficiency {H F : Family} (hw : HasWitnesses H F) : Learnable H F := by
  classical
  let t := fun i => (hw i).choose
  let eligible (s : List Nat) (i : Nat) := Inside (t i) (fun x => x ∈ s) ∧ Inside s (H i)
  -- The choice depends only on the observed history and the fixed family.
  let L : Learner := fun s x =>
    if h : ∃ i, eligible s i then H (least h).choose x ∧ x ∉ s else False
  refine ⟨L, ?_⟩
  intro j e he
  obtain ⟨M, hM⟩ := eventually_seen he (t j) (hw j).choose_spec.1
  obtain ⟨K, hK⟩ := eliminate he (j+1)
  refine ⟨max M K, fun n hn => ?_⟩
  let s := history e n
  have hj : eligible s j := ⟨hM n (by omega), prefix_inside he n⟩
  have existsIdx : ∃ i, eligible s i := ⟨j, hj⟩
  let i := (least existsIdx).choose
  have hi := (least existsIdx).choose_spec
  have contains : Sub (H j) (H i) := hK n (by omega) i
    (Nat.lt_succ_of_le (hi.2 j hj)) hi.1.2
  have sound : Sub (H i) (F j) := (hw i).choose_spec.2 j
    (fun x hx => prefix_inside he n x (hi.1.1 x hx)) contains
  have out (x) : L s x ↔ H i x ∧ x ∉ s := by simp [L, existsIdx, i]
  exact ⟨fun x hx unseen => (out x).mpr ⟨contains x hx, unseen⟩,
         fun x hx => sound x ((out x).mp hx).1⟩

/-- The finite-witness criterion for oracle-free sound coverage. The argument
also covers nonempty finite targets, so infinitude is unnecessary. -/
theorem finiteWitnessCriterion (H F : Family)
    (nonempty : ∀ i, ∃ x, H i x) (ambient : ∀ i, Sub (H i) (F i)) :
    Learnable H F ↔ HasWitnesses H F :=
  ⟨necessity nonempty ambient, sufficiency⟩

end SoundCoverage
