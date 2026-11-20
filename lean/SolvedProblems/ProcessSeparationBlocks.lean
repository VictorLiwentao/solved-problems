module

public import SolvedProblems.ProcessSeparationClock
import Mathlib.Logic.Equiv.List
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

public section

namespace ProcessSeparation
namespace Clock
open Filter Set
open scoped Topology Classical

variable {g : ℕ → ℝ} (C : Clock g)

/-- A finite list of arbitrary natural labels fits in one natural-number header. -/
private def readHeader (code t : ℕ) : ℕ :=
  ((Encodable.decode (α := List ℕ) code).getD []).getD t 0

/-- On a payload round, the most recent header is in the observed history. -/
noncomputable def learner : Strategy := fun t past ↦
  if h : ∃ j, C.s j < t ∧ t < C.s (j+1) then
    readHeader (past ⟨C.s h.choose,h.choose_spec.1⟩) t
  else 0

def concepts : Set Stream := {f | ∀ t, t ∉ range C.s → f t = prediction C.learner f t}

theorem closed_concepts : IsClosed C.concepts := by
  have desc : C.concepts = ⋂ t : {n // n ∉ range C.s},
      {f : Stream | f t = prediction C.learner f t} := by
    ext f
    simp [concepts]
  rw [desc]
  apply isClosed_iInter
  intro t
  apply isClosed_eq (continuous_apply _)
  unfold prediction learner
  split
  next h =>
    have hd : Continuous (fun n : ℕ ↦ readHeader n t) := continuous_of_discreteTopology
    exact hd.comp (continuous_apply (C.s h.choose))
  next => exact continuous_const

theorem realizable_bound (nonneg : ∀ T, 0 ≤ g T) (mono : Monotone g)
    {y : Stream} (hy : Realizable C.concepts y) (T : ℕ) :
    (mistakes (prediction C.learner y) y T : ℝ) ≤ g T := by
  obtain ⟨f,hf,matchY⟩ := hy T
  have incl : ((Finset.range T).filter (fun t ↦ prediction C.learner y t ≠ y t)) ⊆
      ((Finset.range T).filter (fun t ↦ t ∈ range C.s)) := by
    intro t ht
    obtain ⟨ht,err⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨ht,?_⟩
    by_contra h
    have ht' := Finset.mem_range.mp ht
    have eq : (fun i : Fin t ↦ f i) = (fun i : Fin t ↦ y i) :=
      funext fun i ↦ matchY _ (i.isLt.trans ht')
    exact err <| calc
      prediction C.learner y t = prediction C.learner f t := congrArg (C.learner t) eq.symm
      _ = f t := (hf t h).symm
      _ = y t := matchY _ ht'
  have hle : mistakes (prediction C.learner y) y T ≤ C.cut T :=
    (Finset.card_le_card incl).trans (C.headers_bound T)
  exact (show (mistakes (prediction C.learner y) y T : ℝ) ≤ C.cut T by exact_mod_cast hle).trans
    (C.cut_budget nonneg mono T)

private theorem between {t : ℕ} (ht : C.s 0 ≤ t) (hn : t ∉ range C.s) :
    ∃ j, C.s j < t ∧ t < C.s (j+1) := by
  have hlt : t < C.s (C.cut t) := lt_of_le_of_ne (C.cut_spec t)
    (fun h ↦ hn ⟨C.cut t,h.symm⟩)
  cases h : C.cut t with
  | zero => rw [h] at hlt; omega
  | succ j =>
    exact ⟨j,C.before_cut.mp (h ▸ Nat.lt_succ_self j), h ▸ hlt⟩

private def blockCode (y : Stream) (j : ℕ) : ℕ :=
  Encodable.encode (List.ofFn (n := C.s (j+1)) fun i ↦ y i)

private theorem read_code (y : Stream) {j t : ℕ} (ht : t < C.s (j+1)) :
    readHeader (C.blockCode y j) t = y t := by
  simp [readHeader,blockCode,List.getD_eq_getElem?_getD,ht]

/-- Install headers for any requested payload sequence; all preceding positions are zero. -/
private noncomputable def codeStream (y : Stream) (t : ℕ) : ℕ :=
  if h : t ∈ range C.s then C.blockCode y h.choose
  else if t < C.s 0 then 0 else y t

private theorem code_header (y : Stream) (j : ℕ) :
    C.codeStream y (C.s j) = C.blockCode y j := by
  let h : C.s j ∈ range C.s := ⟨j,rfl⟩
  have hj : h.choose = j := C.inc.injective h.choose_spec
  simp [codeStream,h,hj]

private theorem code_mem (y : Stream) : C.codeStream y ∈ C.concepts := by
  intro t hn
  unfold prediction learner
  split
  next h =>
    have h0 : ¬ t < C.s 0 := not_lt.mpr ((C.inc.monotone (Nat.zero_le _)).trans h.choose_spec.1.le)
    change C.codeStream y t = readHeader (C.codeStream y (C.s h.choose)) t
    rw [C.code_header]
    simp [codeStream,hn,h0,C.read_code y h.choose_spec.2]
  next h =>
    have h0 : t < C.s 0 := lt_of_not_ge (fun h0 ↦ h (C.between h0 hn))
    simp [codeStream,hn,h0]

/-- Changing just the header times and a fixed initial segment realizes any payload. -/
theorem dense_comparator (y : Stream) : ∃ f ∈ C.concepts, Tendsto (loss f y) atTop (𝓝 0) := by
  refine ⟨C.codeStream y,C.code_mem y,?_⟩
  have bound (T : ℕ) : mistakes (C.codeStream y) y T ≤ C.s 0 + C.cut T := by
    let heads := (Finset.range T).filter (fun t ↦ t ∈ range C.s)
    have incl : ((Finset.range T).filter (fun t ↦ C.codeStream y t ≠ y t)) ⊆
        Finset.range (C.s 0) ∪ heads := by
      intro t ht
      obtain ⟨hm,ne⟩ := Finset.mem_filter.mp ht
      by_cases h : t ∈ range C.s
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm,h⟩)
      · apply Finset.mem_union_left _
        by_contra! ht
        exact ne (by simp [codeStream,h,show ¬ t < C.s 0 by simpa using ht])
    exact (Finset.card_le_card incl).trans <| (Finset.card_union_le _ _).trans <|
      Nat.add_le_add (Finset.card_range _).le (C.headers_bound T)
  have lim := (tendsto_const_div_atTop_nhds_zero_nat (C.s 0 : ℝ)).add C.cut_div
  refine squeeze_zero' (Eventually.of_forall (fun T ↦ by unfold loss; positivity))
    (Eventually.of_forall fun T ↦ ?_) (by simpa using lim)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast bound T) (Nat.cast_nonneg T)

end Clock
end ProcessSeparation
