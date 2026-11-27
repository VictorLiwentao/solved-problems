module

public import SolvedProblems.AtomicGrowthCounting
public import SolvedProblems.AtomicGrowthScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Filter
open scoped Topology

namespace AtomicGrowth

noncomputable def growth (C : Class) (n : ℕ) : ℝ :=
  ((level C n).card : ℝ)^((n:ℝ)⁻¹)

/-- The grid-class facts from the cited work are explicit hypotheses. -/
structure GridFacts (w : ℕ) (D : ℕ → Class) (Q : Class) : Prop where
  hereditary : ∀ h ≥ 4, Hereditary (D h)
  peak : ∀ h ≥ 4, Tendsto (growth (D h)) atTop (𝓝 (9*(w:ℝ)))
  recurrent : ∀ v, v ∈ Q ↔ ∃ᶠ h in atTop, v ∈ D h
  count : ∀ n, 0<n → (level Q n).card ≤ 512*8^n*n^2*(n+2).choose 2*(w+513)^(n-1)

theorem grid_small {w D Q} (g : GridFacts w D Q) (m : ℕ) :
    ∃ h ≥ 4, ∀ b ∈ D h, IsPerm b → ∀ z, z.Sublist b → z.length ≤ m → standard z ∈ level Q z.length := by
  classical
  let candidates := (Finset.range (m+1)).biUnion (level Set.univ)
  have ev (u : Word) : ∀ᶠ h in atTop, u ∈ D h → u ∈ Q := by
    by_cases hu : u ∈ Q
    · exact Eventually.of_forall fun _ _ => hu
    · have hn := mt (g.recurrent u).mpr hu
      filter_upwards [not_frequently.mp hn] with h hh hmem
      exact (hh hmem).elim
  have he : ∀ᶠ h in atTop, ∀ u ∈ candidates, u ∈ D h → u ∈ Q :=
    (eventually_all_finset candidates).mpr fun u _ => ev u
  obtain ⟨h,hh,huni⟩ := ((eventually_ge_atTop 4).and he).exists
  refine ⟨h,hh,?_⟩
  intro b hb hp z hz hm
  have hzp : IsPerm (standard z) := standard_perm (hz.nodup (hp.nodup_iff.mpr List.nodup_range))
  have hin : standard z ∈ candidates := Finset.mem_biUnion.mpr ⟨z.length,Finset.mem_range.mpr (by omega),
    mem_level.mpr ⟨hzp,length_standard _,Set.mem_univ _⟩⟩
  exact mem_level.mpr ⟨hzp,length_standard _,huni _ hin (g.hereditary h hh b hb _ ⟨z,hz,rfl⟩)⟩

noncomputable def tolerance (i : ℕ) : ℝ := ((i:ℝ)+1)⁻¹
theorem tolerance_pos (i : ℕ) : 0<tolerance i := by unfold tolerance; positivity

structure Stage where
  valley : ℕ
  peak : ℕ
  batch : List Word

structure StageSpec (Q : Class) (L H : ℝ) (i : ℕ) (prior : List Word) (last : ℕ) (s : Stage) : Prop where
  valley_gt : max i last < s.valley
  peak_gt : s.valley < s.peak
  absorb : (2:ℝ)^(blocks prior).length * L^s.valley ≤ (L+tolerance i)^s.valley
  perms : ∀ b ∈ s.batch, IsPerm b
  lengths : ∀ b ∈ s.batch, b.length=s.peak
  small : ∀ b ∈ s.batch, ∀ z, z.Sublist b → z.length≤s.valley → standard z ∈ level Q z.length
  many : H-tolerance i < (s.batch.toFinset.card : ℝ)^((s.peak:ℝ)⁻¹)

theorem grid_stage {w D Q} (g : GridFacts w D Q) {L : ℝ} (hL : 0<L)
    (i : ℕ) (prior : List Word) (last : ℕ) :
    ∃ s, StageSpec Q L (9*(w:ℝ)) i prior last s := by
  classical
  let r := (L+tolerance i)/L
  have hr : 1<r := (one_lt_div hL).mpr (lt_add_of_pos_right _ (tolerance_pos i))
  obtain ⟨a,ha⟩ := pow_unbounded_of_one_lt ((2:ℝ)^(blocks prior).length) hr
  let m := max a (max i last + 1)
  have hm : max i last < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right ..)
  have hab : (2:ℝ)^(blocks prior).length * L^m ≤ (L+tolerance i)^m := by
    have hb := ha.le.trans (pow_le_pow_right₀ hr.le (show a≤m from le_max_left ..))
    unfold r at hb
    rw [div_pow] at hb
    exact (le_div_iff₀ (pow_pos hL _)).mp hb
  obtain ⟨h,hh,hsmall⟩ := grid_small g m
  have he : ∀ᶠ n in atTop, 9*(w:ℝ)-tolerance i < growth (D h) n :=
    (g.peak h hh).eventually (eventually_gt_nhds (by linarith [tolerance_pos i]))
  obtain ⟨n,hn,hg⟩ := ((eventually_gt_atTop m).and he).exists
  let batch := (level (D h) n).toList
  have hmem (b) (hb : b ∈ batch) := mem_level.mp (Finset.mem_toList.mp hb)
  exact ⟨⟨m,n,batch⟩,hm,hn,hab,(fun b hb => (hmem b hb).1),
    (fun b hb => (hmem b hb).2.1),(fun b hb => hsmall b (hmem b hb).2.2 (hmem b hb).1),
    by simpa [batch,growth] using hg⟩

end AtomicGrowth
