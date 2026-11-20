module

public import SolvedProblems.PromptBoundModel
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.ENNReal.Lemmas

public section
open MeasureTheory Set Filter Topology
namespace PromptBound

theorem initial_succ {α} (e : ℕ → α) (n : ℕ) :
    initial e (n+1) = initial e n ++ [e n] := by simp [initial,List.range_succ]
theorem initial_prefix {α} (e : ℕ → α) {n m} (hnm : n ≤ m) :
    (initial e n).IsPrefix (initial e m) := by
  induction hnm with
  | refl => exact List.prefix_refl _
  | step _ ih => rw [initial_succ]; exact ih.trans (List.prefix_append ..)
theorem rounds_succ {q} (e : ℕ → Round q) (n) :
    rounds e (n+1) = e n :: rounds e n := by simp [rounds,initial_succ]

theorem measurable_tape_test (n) (f : List Bool → Prop) :
    MeasurableSet {w : Tape | f (initial w n)} := by
  let proj := fun (w : Tape) (j : Fin n) => w j.val
  have hm : Measurable proj := Measurable.of_eval fun j => measurable_pi_apply j.val
  have h : MeasurableSet {z : Fin n → Bool | f (List.ofFn z)} := Set.to_countable _ |>.measurableSet
  convert hm h using 1
  ext w
  change f (initial w n) ↔ f (List.ofFn (proj w))
  have eq : initial w n = List.ofFn (proj w) := by
    apply List.ext_getElem <;> simp [initial,proj]
  rw [eq]

@[expose] def hit {q} (A : RandomStep q) (K : Word q → Bool) (h : History q) : Set Tape :=
  {w | ∃ y, Returns A h w y ∧ Correct K h y}

theorem hit_measurable {q} (A : RandomStep q) (K) (h) : MeasurableSet (hit A K h) := by
  have eq : hit A K h = ⋃ n, {w : Tape | ∃ y, A (h,initial w n) = some y ∧ Correct K h y} := by
    ext w; simp only [hit,Returns,mem_ofPred_eq,mem_iUnion]; grind
  rw [eq]
  exact MeasurableSet.iUnion fun n => measurable_tape_test n (fun u => ∃ y, A (h,u) = some y ∧ Correct K h y)

/-- Almost-sure membership in an increasing union forces some finite stage
to have probability above any fixed threshold less than one. -/
theorem large_stage (μ : FairLaw) (E : ℕ → Set Tape) (mono : Monotone E)
    (cover : ∀ᵐ w ∂μ.law, ∃ t, w ∈ E t) {r : ℝ} (hr : r < 1) :
    ∃ t, r < μ.law.real (E t) := by
  have full : (⋃ t, E t) =ᵐ[μ.law] (Set.univ : Set Tape) := by
    filter_upwards [cover] with w hw
    exact propext (by simpa only [mem_iUnion,mem_univ,iff_true] using hw)
  have hm := tendsto_measure_iUnion_atTop (μ := μ.law) mono
  have tend := (ENNReal.tendsto_toReal (measure_ne_top μ.law _)).comp hm
  change Tendsto (fun k => μ.law.real (E k)) atTop (𝓝 (μ.law.real (⋃ t, E t))) at tend
  rw [measureReal_congr full] at tend
  exact (tend.eventually_const_lt (by simpa using hr)).exists

/-- Almost-sure eventual correctness gives a uniform late marginal bound along
each individual full text, regardless of the correlation between its outputs. -/
theorem marginal_lock_on_text {q} (μ : FairLaw) (A : RandomStep q) (K) (e)
    (good : ∀ᵐ w ∂μ.law, ∃ N, ∀ n ≥ N, w ∈ hit A K (rounds e (n+1))) :
    ∃ N, ∀ n ≥ N, (1/2 : ℝ) ≤ μ.law.real (hit A K (rounds e (n+1))) := by
  let E := fun N => {w : Tape | ∀ n ≥ N, w ∈ hit A K (rounds e (n+1))}
  have mono : Monotone E := fun _ _ h _ hw n hn => hw n (h.trans hn)
  obtain ⟨N,hN⟩ := large_stage μ E mono good (r := 1/2) (by norm_num)
  exact ⟨N,fun n hn => hN.le.trans (measureReal_mono (fun w hw => hw n hn))⟩

end PromptBound
