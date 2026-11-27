module

public import SolvedProblems.AtomicGrowthSchedule

@[expose] public section

open Filter
open scoped Topology

namespace AtomicGrowth

theorem oscillates_no_limit {C L H} (hg : L<H) (ho : Oscillates C L H) :
    ¬ ∃ x : ℝ, Tendsto (growth C) atTop (𝓝 x) := by
  rintro ⟨x,hx⟩
  obtain ⟨lo,hi⟩ := ho ((H-L)/3) (by linarith)
  have h₁ := le_of_tendsto_of_frequently hx (lo.mono fun _ hh => hh.le)
  have h₂ := ge_of_tendsto_of_frequently hx (hi.mono fun _ hh => hh.le)
  linarith

theorem full_level {C : Class} (hc : ∀ w, IsPerm w → w ∈ C) (n : ℕ) :
    (level C n).card = n.factorial := by
  classical
  unfold level
  rw [Finset.filter_eq_self.mpr (fun x hx => hc _ (by
    have h := List.mem_permutations.mp (List.mem_toFinset.mp hx)
    have he : x.length=n := by simpa using h.length_eq
    simpa [IsPerm,he] using h)),List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range),
    List.length_permutations,List.length_range]

theorem oscillates_proper {C L H} (hL : 1≤L) (ho : Oscillates C L H) : ∃ w, IsPerm w ∧ w ∉ C := by
  by_contra hc
  push Not at hc
  have hA : 0≤L+1 := by linarith
  have he : ∀ᶠ n : ℕ in atTop, (L+1)^n < (n.factorial:ℝ) := by
    have ht := (Real.summable_pow_div_factorial (L+1)).tendsto_atTop_zero
    filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn
    simpa using (div_lt_iff₀ (show 0<(n.factorial:ℝ) by exact_mod_cast Nat.factorial_pos n)).mp hn
  obtain ⟨n,hlo,hf,hn⟩ := ((ho 1 (by norm_num)).1.and_eventually (he.and (eventually_gt_atTop 0))).exists
  have hn' : 0<((n:ℝ)⁻¹) := by positivity
  have hh := Real.rpow_lt_rpow (pow_nonneg hA n) hf hn'
  rw [Real.pow_rpow_inv_natCast hA hn.ne'] at hh
  unfold growth at hlo
  rw [full_level hc] at hlo
  exact (hlo.trans hh).false

/-- Assuming precisely the grid-class input cited in the manuscript, there is
a proper atomic permutation class whose exponential growth rate does not exist.
Its members are the patterns of consecutive finite stages in an infinite
direct sum, and the two numerical thresholds are witnessed arbitrarily late. -/
theorem oscillation_from_grid_data
    (grid : ∀ w : ℕ, 4105≤w → ∃ D Q, GridFacts w D Q) :
    ∃ (w : ℕ) (s : ℕ → List Word), 4105≤w ∧
      (∀ i, ∀ b ∈ s i, IsPerm b) ∧
      (∀ u ∈ jointClass s, IsPerm u) ∧ Hereditary (jointClass s) ∧ Atomic (jointClass s) ∧
      (∃ u, IsPerm u ∧ u ∉ jointClass s) ∧
      Oscillates (jointClass s) (17*(w:ℝ)/2) (9*(w:ℝ)) ∧
      ¬ ∃ x : ℝ, Tendsto (growth (jointClass s)) atTop (𝓝 x) := by
  classical
  obtain ⟨w,hw,hscale⟩ := choose_scale
  obtain ⟨D,Q,g⟩ := grid w hw
  let L := 17*(w:ℝ)/2
  have hbig : (4105:ℝ)≤w := by exact_mod_cast hw
  have hL : 1≤L := by dsimp [L]; linarith
  have hgap : L < 9*(w:ℝ) := by dsimp [L]; linarith
  have hwg := hscale (fun n => (level Q n).card) g.count
  choose make good using grid_stage g (by linarith : 0<L)
  obtain ⟨hp,ho⟩ := schedule_oscillates hL hwg make good
  exact ⟨w,_,hw,hp,joint_perms hp,joint_hereditary _,joint_atomic hp,
    oscillates_proper hL ho,ho,oscillates_no_limit hgap ho⟩

end AtomicGrowth
