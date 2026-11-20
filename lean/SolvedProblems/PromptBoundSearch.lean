module

public import SolvedProblems.PromptBoundEffective

@[expose] public section
namespace PromptBound

variable {q : ℕ}

def earlier (test : ℕ → Bool) (n : ℕ) := ((List.range (n+1)).filter test).head?

theorem earlier_mono {P : ℕ → Bool} {n m i} (le : n ≤ m) (found : earlier P n = some i) :
    earlier P m = some i := by
  induction le with
  | refl => exact found
  | step _ ih =>
    simp only [earlier,List.range_succ (n := _+1),List.filter_append,List.head?_append] at *
    rw [ih]; rfl

theorem earlier_spec {P : ℕ → Bool} {n i} (found : earlier P n = some i) : P i = true :=
  (List.mem_filter.mp (List.mem_of_mem_head? found)).2

theorem earlier_exists {P : ℕ → Bool} {n} (hn : P n = true) : ∃ i, earlier P n = some i := by
  let l := (List.range (n+1)).filter P
  have mem : n ∈ l := List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),hn⟩
  change ∃ _, l.head? = _
  cases hl : l with
  | nil => rw [hl] at mem; exact (List.not_mem_nil mem).elim
  | cons a t => exact ⟨a,rfl⟩

def totalCap {α : Type} (jobs : List α) (cost : α → ℕ → ℕ) (s : ℕ) : ℕ :=
  jobs.foldr (fun j b => max (cost j s) b) 0

theorem le_totalCap {α : Type} {jobs : List α} {j : α} (hj : j ∈ jobs) (cost : α → ℕ → ℕ) (s) :
    cost j s ≤ totalCap jobs cost s := by
  induction jobs with
  | nil => simp at hj
  | cons a l ih =>
    change _ ≤ max _ (totalCap l cost s)
    rcases List.mem_cons.mp hj with rfl|hj
    · exact Nat.le_max_left ..
    · exact (ih hj).trans (Nat.le_max_right ..)

/-- Wait until all finitely many runs pass the probability threshold, then
fix the largest length observed at the first such stage. -/
def batch {α : Type} (jobs : List α) (ready : α → ℕ → Bool) (cost : α → ℕ → ℕ) (n : ℕ) : Option ℕ :=
  let choice := earlier (fun t => jobs.all (fun j => ready j t)) n
  bif choice.isSome then some (totalCap jobs cost (choice.getD 0)) else none

theorem batch_eq_some {α : Type} {jobs : List α} {ready : α → ℕ → Bool} {cost : α → ℕ → ℕ} {n b} :
    batch jobs ready cost n = some b ↔
      ∃ t, earlier (fun s => jobs.all (fun j => ready j s)) n = some t ∧ totalCap jobs cost t = b := by
  unfold batch
  cases earlier (fun s => jobs.all fun j => ready j s) n <;> simp

theorem batch_stable {α : Type} {jobs : List α} {ready : α → ℕ → Bool} {cost : α → ℕ → ℕ} {n m b}
    (le : n ≤ m) (found : batch jobs ready cost n = some b) : batch jobs ready cost m = some b := by
  obtain ⟨t,e,h⟩ := batch_eq_some.mp found
  exact batch_eq_some.mpr ⟨t,earlier_mono le e,h⟩

theorem batch_terminates {α : Type} (jobs : List α) (ready : α → ℕ → Bool) (cost : α → ℕ → ℕ)
    (eventual : ∀ j ∈ jobs, ∃ s, ∀ t ≥ s, ready j t = true) :
    ∃ n b, batch jobs ready cost n = some b := by
  have uniform : ∃ s, ∀ t ≥ s, ∀ j ∈ jobs, ready j t = true := by
    induction jobs with
    | nil => exact ⟨0, by simp⟩
    | cons a l ih =>
      obtain ⟨s,hs⟩ := eventual a (by simp)
      obtain ⟨r,hr⟩ := ih (fun j hj => eventual j (by simp [hj]))
      refine ⟨max s r, fun t ht j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl|hj
      · exact hs _ ((Nat.le_max_left ..).trans ht)
      · exact hr _ ((Nat.le_max_right ..).trans ht) _ hj
  obtain ⟨s,hs⟩ := uniform
  obtain ⟨t,ht⟩ := earlier_exists (P := fun t => jobs.all fun j => ready j t)
    (List.all_eq_true.mpr (hs s le_rfl))
  exact ⟨s,_,batch_eq_some.mpr ⟨t,ht,rfl⟩⟩

theorem eff_batch {α β : Type} [Primcodable α] [Primcodable β] {X : Oracle}
    (jobs : β → List α) (ready : α × ℕ → Bool) (cost : α × ℕ → ℕ)
    (hjobs : Effective X jobs) (hr : Effective X ready) (hc : Effective X cost) :
    Effective X (fun z : β × ℕ => batch (jobs z.1) (fun j t => ready (j,t)) (fun j t => cost (j,t)) z.2) := by
  let test (z : (β × ℕ) × ℕ) := (jobs z.1.1).all (fun j => ready (j,z.2))
  have ht : Effective X test := eff_all (f := fun z : (β × ℕ) × ℕ => jobs z.1.1)
    (g := fun z => ready (z.2,z.1.2)) (by fun_prop) (by fun_prop)
  let accepted (z : β × ℕ) := (List.range z.2.succ).filter (fun n => test (z,n))
  have ha : Effective X accepted := eff_filter (f := fun z : β × ℕ => List.range z.2.succ)
    ht (hf := by fun_prop)
  let chosen (z : β × ℕ) := (accepted z).head?
  have he : Effective X chosen := by unfold chosen; fun_prop
  let peak (z : β × ℕ) := totalCap (jobs z.1) (fun j t => cost (j,t)) ((chosen z).getD 0)
  have hp : Effective X peak := Effective.foldList
    (f := fun z : β × ℕ => jobs z.1) (z := fun _ => 0)
    (g := fun z : ((β × ℕ) × α) × ℕ => max (cost (z.1.2,(chosen z.1.1).getD 0)) z.2)
    (by fun_prop) (by fun_prop) (by fun_prop)
  change Effective X (fun z => bif (chosen z).isSome then some (peak z) else none)
  fun_prop

end PromptBound
