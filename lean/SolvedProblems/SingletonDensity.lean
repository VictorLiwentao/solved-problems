module

public import SolvedProblems.SingletonQuota
public import SolvedProblems.SingletonDensityBounds
import Mathlib.Tactic.Linarith

public section

namespace SingletonDensity

private theorem fresh_exists (f : Finset Nat) : ∃ x, x ∉ f := by
  obtain ⟨x,_,hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show f.card < (Finset.range (f.card+1)).card by simp)
  exact ⟨x,hx⟩

/-- Schedule rank n on round n. When this rank is already seen, choose a fresh one. -/
private noncomputable def scheduled (f : Finset Nat) : Nat :=
  if f.card-1 ∈ f then (fresh_exists f).choose else f.card-1

private theorem scheduled_legal : Legal (fun h => some (scheduled h.toFinset)) := by
  intro h _ x hx eq
  have hm : scheduled h.toFinset ∈ h.toFinset := (Option.some.inj eq) ▸ List.mem_toFinset.mpr hx
  unfold scheduled at hm
  split at hm
  · exact (fresh_exists _).choose_spec hm
  · contradiction

private theorem prefix_card {e : Nat → Nat} (inj : Function.Injective e) (n) :
    (seenPrefix e n).toFinset.card = n := by
  induction n with
  | zero => simp [seenPrefix]
  | succ n ih =>
    change (e n :: seenPrefix e n).toFinset.card = n+1
    have fresh : e n ∉ (seenPrefix e n).toFinset := by
      intro h
      obtain ⟨k,lt,eq⟩ := mem_seenPrefix.mp (List.mem_toFinset.mp h)
      have := inj eq
      omega
    simp [fresh,ih]

private theorem covers {e : Nat → Nat} (inj : Function.Injective e) :
    (Set.range e)ᶜ ⊆ Outputs (fun h => some (scheduled h.toFinset)) e := by
  intro x hx
  have absent : x ∉ (seenPrefix e (x+1)).toFinset := by
    intro h
    obtain ⟨k,_,eq⟩ := mem_seenPrefix.mp (List.mem_toFinset.mp h)
    exact hx ⟨k,eq⟩
  exact ⟨x,by simp [scheduled,prefix_card inj,absent]⟩

private theorem count_mono {A B : Set Nat} (h : A ⊆ B) (n) : cnt A n ≤ cnt B n := by
  classical
  exact Finset.card_le_card (Finset.monotone_filter_right (Finset.range n) (fun _ _ hx => h hx))

private theorem count_partition (A : Set Nat) (n) : (cnt A n : ℝ) + (cnt Aᶜ n : ℝ) = n := by
  classical
  have h : cnt A n + cnt Aᶜ n = n := by
    simpa [cnt] using (Finset.range n).card_filter_add_card_filter_not (fun x => x ∈ A)
  exact_mod_cast h

/-- For every exact core density between zero and one half, a set-driven generator
attains the complementary lower density. Every legal deterministic generator admits
an injective enumeration at that core density bounding even its upper output density. -/
theorem minimax {a : ℝ} (ha : 0 ≤ a) (aHalf : a ≤ 1/2) :
    (∃ F : Finset Nat → Nat, Legal (fun h => some (F h.toFinset)) ∧
      ∀ e : Nat → Nat, Function.Injective e → Exact (Set.range e) a →
        Lower (Outputs (fun h => some (F h.toFinset)) e) (1-a)) ∧
    (∀ G : Strategy, Legal G → ∃ e : Nat → Nat, Function.Injective e ∧
      Exact (Set.range e) a ∧ Upper (Outputs G e) (1-a)) := by
  constructor
  · refine ⟨scheduled,scheduled_legal,?_⟩
    intro e inj density ε pos
    obtain ⟨N,hN⟩ := density ε pos
    refine ⟨N,fun n hn => ?_⟩
    have H : (cnt (Set.range e)ᶜ n : ℝ) ≤
        (cnt (Outputs (fun h => some (scheduled h.toFinset)) e) n : ℝ) :=
      Nat.cast_le.mpr (count_mono (covers inj) n)
    linarith [(hN n hn).2,count_partition (Set.range e) n]
  · intro G legal
    obtain ⟨q,size,inf,exactness⟩ := densityQuotas ha aHalf
    obtain ⟨e,inj,full,avoid⟩ := quotaPlay size inf G legal
    have density := exactness (Set.range e) full
    refine ⟨e,inj,density,?_⟩
    intro ε pos
    obtain ⟨N,hN⟩ := density ε pos
    refine ⟨N,fun n hn => ?_⟩
    have subset : Outputs G e ⊆ (Set.range e)ᶜ := fun x hx hr => avoid x hr hx
    have H := Nat.cast_le (α := ℝ) |>.mpr (count_mono subset n)
    linarith [(hN n hn).1,count_partition (Set.range e) n]

end SingletonDensity
