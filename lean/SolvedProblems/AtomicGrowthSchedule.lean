module

public import SolvedProblems.AtomicGrowthStages

@[expose] public section

open Filter
open scoped Topology

namespace AtomicGrowth

/-- A stage is chosen only after its entire finite prefix is known. -/
def history (make : ℕ → List Word → ℕ → Stage) : ℕ → List Word × ℕ
  | 0 => ([],0)
  | i+1 =>
    let old := history make i
    let s := make i old.1 old.2
    (old.1++s.batch,s.peak)

def schedule (make : ℕ → List Word → ℕ → Stage) (i : ℕ) : Stage :=
  make i (history make i).1 (history make i).2

theorem stages_schedule (make : ℕ → List Word → ℕ → Stage) (i : ℕ) :
    stages (fun j => (schedule make j).batch) i = (history make i).1 := by
  induction i with
  | zero => simp [stages,history]
  | succ i ih => rw [stages_add,ih]; simp [history,schedule]

theorem tolerance_tendsto : Tendsto tolerance atTop (𝓝 0) := by
  have h : Tendsto (fun i : ℕ => (i:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

/-- The low and high inequalities here occur at arbitrarily large lengths. -/
def Oscillates (C : Class) (L H : ℝ) : Prop :=
  ∀ e>0, (∃ᶠ n in atTop, growth C n < L+e) ∧ (∃ᶠ n in atTop, H-e < growth C n)

theorem schedule_oscillates {Q : Class} {L H : ℝ} (hL : 1≤L)
    (hw : ∀ n, (∑ k : Fin n, ((level Q (k.val+1)).card : ℝ)/L^(k.val+1))≤1)
    (make : ℕ → List Word → ℕ → Stage)
    (good : ∀ i p l, StageSpec Q L H i p l (make i p l)) :
    let s := fun i => (schedule make i).batch
    (∀ i, ∀ b ∈ s i, IsPerm b) ∧ Oscillates (jointClass s) L H := by
  classical
  let t := schedule make
  let s := fun i => (t i).batch
  let C := jointClass s
  have spec (i) : StageSpec Q L H i (history make i).1 (history make i).2 (t i) := good .. 
  have hp : ∀ i, ∀ b ∈ s i, IsPerm b := fun i => (spec i).perms
  refine ⟨hp,?_⟩
  change Oscillates C L H
  have hindex (i) : i < (t i).valley := (le_max_left ..).trans_lt (spec i).valley_gt
  have hs : StrictMono fun i => (t i).valley := strictMono_nat_of_lt_succ fun i => by
    have hh : (t i).peak < (t (i+1)).valley := (le_max_right ..).trans_lt (spec (i+1)).valley_gt
    exact (spec i).peak_gt.trans hh
  have low (i) : growth C (t i).valley ≤ L+tolerance i := by
    have hv := joint_valley hp i (t i).valley (level Q) (fun j hj b hb z hz hm _ =>
      (spec j).small b hb z hz (hm.trans (hs.monotone hj))) L hL hw
    change ((level C (t i).valley).card:ℝ) ≤ _ at hv
    have hpre : stages s i=(history make i).1 := stages_schedule make i
    rw [hpre] at hv
    have hb := hv.trans (spec i).absorb
    have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by positivity : 0≤((t i).valley:ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (by linarith [tolerance_pos i]) (by have := hindex i; omega)] at h
    exact h
  have high (i) : H-tolerance i < growth C (t i).peak := by
    have incl : (s i).toFinset ⊆ level C (t i).peak := by
      intro b hb
      have hm := List.mem_toFinset.mp hb
      exact mem_level.mpr ⟨hp i b hm,(spec i).lengths b hm,stage_mem_class hm (hp i b hm)⟩
    have hc : ((s i).toFinset.card:ℝ) ≤ (level C (t i).peak).card := by exact_mod_cast Finset.card_le_card incl
    exact (spec i).many.trans_le (Real.rpow_le_rpow (Nat.cast_nonneg _) hc (by positivity))
  intro e he
  have pick (N : ℕ) : ∃ i≥N, tolerance i<e := ((eventually_ge_atTop N).and (tolerance_tendsto.eventually (eventually_lt_nhds he))).exists
  constructor <;> apply frequently_atTop.mpr <;> intro N <;> obtain ⟨i,hi,hsmall⟩ := pick N
  · exact ⟨_,hi.trans (hindex i).le,(low i).trans_lt (by linarith)⟩
  · exact ⟨_,hi.trans ((hindex i).trans (spec i).peak_gt).le,(show H-e < H-tolerance i by linarith).trans (high i)⟩

end AtomicGrowth
