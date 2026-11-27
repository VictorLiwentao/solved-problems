module

public import SolvedProblems.UniversalWadgeReduction
public import SolvedProblems.UniversalWadgeCategory
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Clopen

@[expose] public section

namespace UniversalWadge

open Set Filter Real
open scoped Classical Topology

def realLocus {X} (I : Ideal) (f : ℕ → X → ℝ) := {x | ∀ ε : ℝ, 0 < ε → {n | ε < f n x} ∈ I.family}

/-- Logarithmic threshold coordinates let the entire real line parametrize positive thresholds. -/
def Good {X} (f : ℕ → X → ℝ) : Set (X × ℝ) := {p | ∀ n, exp p.2 ≠ f n p.1}

noncomputable def thresholdBits {X} (f : ℕ → X → ℝ) (p : Good f) : Cantor :=
  fun n => if exp p.val.2 < f n p.val.1 then true else false

theorem threshold_continuous {X} [TopologicalSpace X] (f : ℕ → X → ℝ) (cf : ∀ n, Continuous (f n)) :
    Continuous (thresholdBits f) := by
  apply continuous_pi;intro n
  apply (continuous_bool_rng true).mpr
  let below := {p : Good f | exp p.val.2 < f n p.val.1}
  let above := {p : Good f | f n p.val.1 < exp p.val.2}
  have cb : IsOpen below := isOpen_lt (Real.continuous_exp.comp (continuous_snd.comp continuous_subtype_val)) ((cf n).comp (continuous_fst.comp continuous_subtype_val))
  have ca : IsOpen above := isOpen_lt ((cf n).comp (continuous_fst.comp continuous_subtype_val)) (Real.continuous_exp.comp (continuous_snd.comp continuous_subtype_val))
  have eq : belowᶜ = above := by
    ext p;change (¬ exp p.val.2 < f n p.val.1) ↔ _
    exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) (p.property n).symm,fun h => not_lt.mpr h.le⟩
  have cl : IsClopen below := ⟨isOpen_compl_iff.mp (eq ▸ ca),cb⟩
  convert cl using 1;ext p;simp [thresholdBits,below]

theorem good_residual {X} (f : ℕ → X → ℝ) (x : X) : ∀ᵇ t : ℝ, (x,t)∈Good f := by
  apply eventually_countable_forall.mpr;intro n
  have away := residual_of_dense_open (isOpen_compl_singleton (x := Real.log (f n x))) (dense_compl_singleton _)
  filter_upwards [away] with t ht
  intro eq
  exact ht (by have h := congrArg Real.log eq;simpa only [Set.mem_singleton_iff,Real.log_exp] using h)

theorem comeager_univ_iff {X J} [TopologicalSpace J] (E : Set (X×J)) (x : X) :
    x ∈ comeagerSection E Set.univ ↔ ∀ᵇ t : J, (x,t)∈E := by
  simp only [comeagerSection,nonmeagreSection,mem_compl_iff,mem_ofPred_eq,not_not,inter_univ,IsMeagre,
    fiber,preimage_compl,compl_compl];rfl

theorem level_correct {X} (f : ℕ → X → ℝ) (I : Ideal) (E : Set (X×ℝ))
    (agree : Subtype.val ⁻¹' E = thresholdBits f ⁻¹' cantors I) : realLocus I f = comeagerSection E Set.univ := by
  ext x;rw [comeager_univ_iff]
  have localEq (t : ℝ) (h : (x,t) ∈ Good f) : (x,t)∈E ↔ {n | exp t < f n x}∈I.family := by
    let p : Good f := ⟨(x,t),h⟩
    have e := Set.ext_iff.mp agree p
    change (x,t)∈E ↔ support (thresholdBits f p)∈I.family at e
    simpa [support,thresholdBits,p] using e
  constructor
  · intro h;filter_upwards [good_residual f x] with t ht;exact (localEq t ht).mpr (h _ (exp_pos t))
  · intro h ε ep
    have both := (h.and (good_residual f x))
    have dense := dense_of_mem_residual both
    obtain ⟨t,lt,ht⟩ := dense.inter_open_nonempty (Iio (log ε)) isOpen_Iio nonempty_Iio
    have order : exp t < ε := (Real.lt_log_iff_exp_lt ep).mp lt
    exact I.shrink (fun n hn => order.trans hn) ((localEq t ht.2).mp ht.1)

/-- The variable-threshold upper bound on every Polish domain, in fact on every
topological domain. All strictly positive thresholds are tested. -/
theorem thresholdRanks {X : Type} [TopologicalSpace X] (I : Ideal) (f : ℕ → X → ℝ) (cf : ∀ n,Continuous (f n))
    (α : Ordinal.{0}) :
    (MultiplicativeClass Cantor α (cantors I) → MultiplicativeClass X α (realLocus I f)) ∧
    (AdditiveClass Cantor α (cantors I) → MultiplicativeClass X (α+1) (realLocus I f)) := by
  have transfer (β : Ordinal.{0}) (h : MultiplicativeClass Cantor β (cantors I)) : MultiplicativeClass X β (realLocus I f) := by
    have sub := additive_preimage (threshold_continuous f cf) h
    obtain ⟨T,hT,eq⟩ := relative_extension (Good f) sub
    have agree : Subtype.val ⁻¹' Tᶜ = thresholdBits f ⁻¹' cantors I := by
      rw [preimage_compl,eq,preimage_compl,compl_compl]
    rw [level_correct f I Tᶜ agree]
    exact section_multiplicative (by simpa only [MultiplicativeClass,compl_compl] using hT) Set.univ isOpen_univ
  exact ⟨transfer α,fun h => transfer (α+1) (.lowerCompl (Order.lt_succ _) h)⟩

end UniversalWadge
