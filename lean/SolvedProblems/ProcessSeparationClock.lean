module

public import SolvedProblems.ProcessSeparationModel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

namespace ProcessSeparation
open Filter Set
open scoped Topology Classical

/-- At the j-th header the budget permits j+1 mistakes. The quadratic lower
bound makes the number of headers sublinear. -/
structure Clock (g : ℕ → ℝ) where
  s : ℕ → ℕ
  inc : StrictMono s
  quad : ∀ j, (j + 1)^2 ≤ s j
  budget : ∀ j, ((j + 1 : ℕ) : ℝ) ≤ g (s j)

theorem clock_exists {g : ℕ → ℝ} (hg : Monotone g) (ht : Tendsto g atTop atTop) :
    Nonempty (Clock g) := by
  classical
  have threshold (j : ℕ) : ∃ t, ((j+1 : ℕ) : ℝ) ≤ g t := by
    obtain ⟨t, h⟩ := tendsto_atTop_atTop.mp ht ((j+1 : ℕ) : ℝ)
    exact ⟨t,h _ le_rfl⟩
  let b (j : ℕ) := max ((j+1)^2) (threshold j).choose
  let s : ℕ → ℕ := Nat.rec (b 0) (fun j previous ↦ max (previous+1) (b (j+1)))
  have hb (j : ℕ) : b j ≤ s j := by
    cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_right _ _
  exact ⟨⟨s,strictMono_nat_of_lt_succ (fun j ↦
    (Nat.lt_succ_self _).trans_le (le_max_left _ _)),
    fun j ↦ (le_max_left _ _).trans (hb j),
    fun j ↦ (threshold j).choose_spec.trans (hg ((le_max_right _ _).trans (hb j)))⟩⟩

namespace Clock
variable {g : ℕ → ℝ} (C : Clock g)

private theorem reaches (T : ℕ) : ∃ j, T ≤ C.s j := ⟨T,C.inc.id_le T⟩

/-- Number of header times strictly before T. -/
noncomputable def cut (T : ℕ) : ℕ := Nat.find (C.reaches T)

theorem cut_spec (T : ℕ) : T ≤ C.s (C.cut T) := Nat.find_spec (C.reaches T)

theorem before_cut {j T : ℕ} : j < C.cut T ↔ C.s j < T := by
  constructor
  · intro h
    exact lt_of_not_ge (Nat.find_min (C.reaches T) h)
  · intro h
    by_contra! hn
    exact h.not_ge ((C.cut_spec T).trans (C.inc.monotone hn))

theorem cut_budget (nonneg : ∀ T, 0 ≤ g T) (mono : Monotone g) (T : ℕ) :
    (C.cut T : ℝ) ≤ g T := by
  cases eq : C.cut T with
  | zero => simpa using nonneg T
  | succ j =>
    have h : j < C.cut T := eq ▸ Nat.lt_succ_self j
    exact (C.budget j).trans (mono (C.before_cut.mp h).le)

theorem cut_sq (T : ℕ) : (C.cut T)^2 ≤ T := by
  cases eq : C.cut T with
  | zero => simp
  | succ j =>
    have h : j < C.cut T := eq ▸ Nat.lt_succ_self j
    exact (C.quad j).trans (C.before_cut.mp h).le

theorem headers_bound (T : ℕ) :
    ((Finset.range T).filter (fun t ↦ t ∈ Set.range C.s)).card ≤ C.cut T := by
  classical
  calc
    _ ≤ ((Finset.range (C.cut T)).image C.s).card := by
      apply Finset.card_le_card
      intro t ht
      obtain ⟨ht, j, rfl⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (C.before_cut.mpr
        (Finset.mem_range.mp ht)),rfl⟩
    _ ≤ _ := Finset.card_image_le.trans_eq (Finset.card_range _)

theorem cut_div : Tendsto (fun T ↦ (C.cut T : ℝ) / T) atTop (𝓝 0) := by
  have grows : Tendsto C.cut atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro k
    exact ⟨C.s k+1,fun T h ↦ (C.before_cut.mpr (show C.s k < T by omega)).le⟩
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp grows)
  filter_upwards [eventually_gt_atTop 0, tendsto_atTop.mp grows 1] with T hT hcut
  have hc : 0 < (C.cut T : ℝ) := by exact_mod_cast (show 0 < C.cut T by omega)
  change (C.cut T : ℝ) / T ≤ 1 / C.cut T
  apply (div_le_div_iff₀ (by exact_mod_cast hT) hc).mpr
  have sq : (C.cut T : ℝ)^2 ≤ T := by exact_mod_cast C.cut_sq T
  nlinarith only [sq]

end Clock
end ProcessSeparation
