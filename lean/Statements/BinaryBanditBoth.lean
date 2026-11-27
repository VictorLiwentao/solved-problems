module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Tactic.NormNum
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Data.Set.Countable

@[expose] public section

open Set MeasureTheory
open scoped Cardinal unitInterval ENNReal

namespace BinaryBandit

abbrev Arm := unitInterval
abbrev Strategy (Ω : Type*) := (t : ℕ) → (Fin t → Bool) → Ω → Arm

/-- An arm is queried after each binary transcript. At the budget the same
prescription gives the output. All choices can share a single random seed. -/
noncomputable def transcript {Ω : Type*} (A : Strategy Ω) (U : Set Arm) (ω : Ω) :
    (t : ℕ) → Fin t → Bool
  | 0 => Fin.elim0
  | t + 1 => by
    classical
    exact Fin.snoc (transcript A U ω t) (decide (A t (transcript A U ω t) ω ∈ U))

/-- The zero target and the indicators of open sets whose complements have
cardinality at most the first uncountable cardinal. -/
def Eligible (U : Set Arm) : Prop :=
  U = ∅ ∨ (U.Nonempty ∧ IsOpen U ∧ #(↥(Uᶜ)) ≤ ℵ₁)

/-- Under the zero target, every arm is optimal. Otherwise the expected reward
deficit is the probability that the output is outside the winning set. -/
def failure {Ω : Type*} (A : Strategy Ω) (m : ℕ) (U : Set Arm) : Set Ω :=
  {ω | U.Nonempty ∧ A m (transcript A U ω m) ω ∉ U}

def Learnable : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ (m : ℕ) (Ω : Type) (_s : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧ ∃ A : Strategy Ω,
        (∀ t h, Measurable (A t h)) ∧ ∀ U, Eligible U → μ (failure A m U) ≤ ε

end BinaryBandit

open Set MeasureTheory Filter
open scoped Cardinal unitInterval ENNReal Topology

namespace BinaryBandit

private theorem measurable_play {Ω : Type*} [MeasurableSpace Ω] (A : Strategy Ω)
    (hm : ∀ t h, Measurable (A t h)) (U : Set Arm) (hu : MeasurableSet U) (m : ℕ) :
    Measurable fun ω ↦ A m (transcript A U ω m) ω := by
  classical
  have step (n : ℕ) : Measurable (fun p : Ω × (Fin n → Bool) ↦ A n p.2 p.1) :=
    measurable_from_prod_countable_left (hm n)
  have hist (n : ℕ) : Measurable (fun ω ↦ transcript A U ω n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      have eval := (step n).comp (measurable_id.prodMk ih)
      have bit : Measurable (fun ω ↦ decide (A n (transcript A U ω n) ω ∈ U)) := by
        have eq (ω : Ω) : decide (A n (transcript A U ω n) ω ∈ U) =
            (if A n (transcript A U ω n) ω ∈ U then true else false) := by split <;> simp_all
        simp_rw [eq]
        exact Measurable.ite (hu.preimage eval) measurable_const measurable_const
      exact (measurable_of_countable (fun p : (Fin n → Bool) × Bool ↦ (Fin.snoc p.1 p.2 : Fin (n+1) → Bool))).comp
        (ih.prodMk bit)
  exact (step m).comp (measurable_id.prodMk (hist m))

/-- Every failure event in the definition of learning is measurable. -/
theorem failure_measurable {Ω : Type*} [MeasurableSpace Ω] (A : Strategy Ω)
    (hm : ∀ t h, Measurable (A t h)) (m : ℕ) (U : Set Arm) (hu : Eligible U) :
    MeasurableSet (failure A m U) := by
  rcases hu with rfl | ⟨hn, ho, _⟩
  · simp [failure]
  have h := ho.measurableSet.compl.preimage (measurable_play A hm U ho.measurableSet m)
  simpa [failure, hn, preimage, compl_def] using h

/-- Failure of CH makes each eligible closed losing set countable, so that the
uniform arm wins almost surely for each nonzero target without querying it. -/
theorem uniform_zero_queries (hc : ℵ₁ < (𝔠 : Cardinal.{0})) (U : Set Arm)
    (h : Eligible U) : volume (failure (fun _ _ (ω : Arm) ↦ ω) 0 U) = 0 := by
  rcases h with rfl | ⟨hn, ho, hsmall⟩
  · simp [failure]
  have hcoun : Uᶜ.Countable := by
    by_contra hunc
    obtain ⟨f, hr, _, hf⟩ := ho.isClosed_compl.exists_nat_bool_injection_of_not_countable hunc
    let g (a : ℕ → Bool) : ↥(Uᶜ) := ⟨f a, hr ⟨a,rfl⟩⟩
    have hg : Function.Injective g := fun x y he ↦ hf (congrArg Subtype.val he)
    have lower := Cardinal.mk_le_of_injective hg
    have hcard : #(ℕ → Bool) = (𝔠 : Cardinal.{0}) := by simp
    rw [hcard] at lower
    exact hc.not_ge (lower.trans hsmall)
  have he : failure (fun _ _ (ω : Arm) ↦ ω) 0 U = Uᶜ := by ext x; simp [failure, hn]
  rw [he]
  exact hcoun.measure_zero _

/-- Nested nonempty open sets with empty intersection. -/
private def win (n : ℕ) : Set Arm := {u | 0 < u.val ∧ u.val < 1 / (n + 1 : ℝ)}

private theorem win_open (n : ℕ) : IsOpen (win n) :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

private theorem win_nonempty (n : ℕ) : (win n).Nonempty := by
  have hp : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  have hu : 1 / (n + 1 : ℝ) ≤ 1 := by
    apply div_le_one_of_le₀
    · linarith [Nat.cast_nonneg (α := ℝ) n]
    · positivity
  exact ⟨⟨(1 / (n + 1 : ℝ))/2, by constructor <;> linarith⟩, by change 0 < _ ∧ _ < _; constructor <;> linarith⟩

private theorem win_antitone : Antitone win := by
  intro i j hij x hx
  exact ⟨hx.1, lt_of_lt_of_le hx.2 (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij))⟩

private theorem leaves_win (u : Arm) : ∀ᶠ n in atTop, u ∉ win n := by
  by_cases h : 0 < u.val
  · obtain ⟨n,hn⟩ := exists_nat_one_div_lt h
    exact eventually_atTop.2 ⟨n, fun j hj hmem ↦ (not_lt_of_ge (le_of_lt hn)) (win_antitone hj hmem).2⟩
  · exact Eventually.of_forall fun _ hmem ↦ h hmem.1

/-- A bound on the number of binary queries leaves finitely many possible
outputs for each random seed. Some nonempty open target makes the error larger
than any fixed threshold below one. This includes arbitrary shared randomness. -/
theorem open_target_lower_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Strategy Ω) (m : ℕ) {δ : ℝ≥0∞} (hδ : δ < 1) :
    ∃ U : Set Arm, U.Nonempty ∧ IsOpen U ∧ δ < μ (failure A m U) := by
  classical
  let safe (n : ℕ) : Set Ω := {ω | ∀ h : Fin m → Bool, A m h ω ∉ win n}
  have mono : Monotone safe := fun _ _ hij _ hx h hm ↦ hx h (win_antitone hij hm)
  have full : ⋃ n, safe n = univ := by
    apply eq_univ_of_forall
    intro ω
    have h : ∀ᶠ n in atTop, ∀ h : Fin m → Bool, A m h ω ∉ win n :=
      (Filter.eventually_all).mpr fun h ↦ leaves_win (A m h ω)
    obtain ⟨n,hn⟩ := h.exists
    exact mem_iUnion.mpr ⟨n, hn⟩
  have total : (⨆ n, μ (safe n)) = 1 := by rw [← mono.measure_iUnion, full, measure_univ]
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp (total ▸ hδ : δ < ⨆ n, μ (safe n))
  refine ⟨win n, win_nonempty n, win_open n, lt_of_lt_of_le hn (measure_mono ?_)⟩
  exact fun ω h ↦ ⟨win_nonempty n, h (transcript A (win n) ω m)⟩

/-- Hanneke and Yang's binary-bandit question: the open-target instance in
Theorem 1 is learnable exactly when the continuum exceeds aleph one. -/
theorem learnable_iff_not_CH : Learnable ↔ ℵ₁ < (𝔠 : Cardinal.{0}) := by
  constructor
  · intro learns
    by_contra! hc
    obtain ⟨m, Ω, s, μ, hp, A, _, hA⟩ := learns (1/2) (by norm_num)
    obtain ⟨U, hU, ho, hbad⟩ := open_target_lower_bound μ A m (δ := 1/2) (by norm_num)
    have eligible : Eligible U := Or.inr ⟨hU, ho, (Cardinal.mk_set_le _).trans (by simpa [Arm] using hc)⟩
    exact hbad.not_ge (hA U eligible)
  · intro hc ε _
    refine ⟨0, Arm, inferInstance, volume, inferInstance, fun _ _ ω ↦ ω, fun _ _ ↦ measurable_id, ?_⟩
    intro U hU
    rw [uniform_zero_queries hc U hU]
    exact zero_le

end BinaryBandit

open Set MeasureTheory
open scoped unitInterval ENNReal

namespace BinaryDiffuse

/-- The second bandit uses all subsets of the unit interval as measurable sets. -/
def Coord : Type := unitInterval

instance : MeasurableSpace Coord := ⊤
instance : DiscreteMeasurableSpace Coord := inferInstanceAs (@DiscreteMeasurableSpace Coord ⊤)
instance : Uncountable Coord := by
  apply Cardinal.aleph0_lt_mk_iff.mp
  rw [show Cardinal.mk Coord = Cardinal.continuum from Cardinal.mk_unitInterval]
  exact Cardinal.aleph0_lt_continuum

/-- A separate type makes the power-set sigma algebra on arms explicit. -/
def Arm : Type := Coord × Bool

instance : MeasurableSpace Arm := ⊤
instance : DiscreteMeasurableSpace Arm := inferInstanceAs (@DiscreteMeasurableSpace Arm ⊤)

def first (a : Arm) : Coord := Prod.fst a

def winSet (f : Coord → Option Bool) : Set Arm := {a | f (first a) = some (Prod.snd a)}

def Eligible (U : Set Arm) : Prop :=
  U = ∅ ∨ ∃ f : Coord → Option Bool, {x | f x = none}.Countable ∧ U = winSet f

abbrev Strategy (Ω : Type*) := (t : ℕ) → (Fin t → Bool) → Ω → Arm

noncomputable def transcript {Ω : Type*} (A : Strategy Ω) (U : Set Arm) (ω : Ω) :
    (t : ℕ) → Fin t → Bool := by
  classical
  exact Nat.rec (motive := fun t => Fin t → Bool) Fin.elim0
    (fun t history => Fin.snoc history (decide (A t history ω ∈ U)))

def failure {Ω : Type*} (A : Strategy Ω) (m : ℕ) (U : Set Arm) : Set Ω :=
  {ω | U.Nonempty ∧ A m (transcript A U ω m) ω ∉ U}

def Learnable : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ (m : ℕ) (Ω : Type) (_s : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧ ∃ A : Strategy Ω,
        (∀ t h, Measurable (A t h)) ∧ ∀ U, Eligible U → μ (failure A m U) ≤ ε

/-- A countably additive probability on the entire powerset which vanishes
on every singleton. -/
def DiffuseExists : Prop :=
  ∃ μ : Measure Coord, IsProbabilityMeasure μ ∧ ∀ x : Coord, μ {x} = 0

end BinaryDiffuse

open Set MeasureTheory Filter
open scoped ENNReal

namespace BinaryDiffuse

/-- Ask for bit zero at the sampled coordinate. A positive reply certifies that
arm; on a negative reply use bit one at the same coordinate. -/
def oneQuery : Strategy Coord
  | 0, _, x => (x, false)
  | _ + 1, h, x => (x, !(h 0))

theorem one_query_exact (μ : Measure Coord) (hn : ∀ x : Coord, μ {x} = 0)
    (U : Set Arm) (hu : Eligible U) : μ (failure oneQuery 1 U) = 0 := by
  classical
  let _ : NullSingletonClass μ := ⟨hn⟩
  rcases hu with rfl | ⟨f,hf,rfl⟩
  · simp [failure]
  apply measure_mono_null _ (hf.measure_zero μ)
  intro x hx
  have lose := hx.2
  cases he : f x with
  | none => exact he
  | some b =>
    exfalso
    apply lose
    have bit : transcript oneQuery (winSet f) x 1 0 = decide (f x = some false) := by
      change Fin.snoc (α := fun _ : Fin 1 => Bool) Fin.elim0 (decide (oneQuery 0 Fin.elim0 x ∈ winSet f)) 0 = _
      rw [Fin.snoc_zero]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rfl
    change f x = some (!(transcript oneQuery (winSet f) x 1 0))
    rw [bit, he]
    cases b <;> simp

private def atoms (μ : Measure Coord) : Set Coord := {x | 0 < μ {x}}

private theorem atoms_countable (μ : Measure Coord) [IsProbabilityMeasure μ] : (atoms μ).Countable := by
  simpa [atoms, id] using (Measure.countable_meas_level_set_pos (μ := μ) (g := id) measurable_id)

private theorem diffuse_of_residual (μ : Measure Coord) [IsProbabilityMeasure μ]
    (h : μ (atoms μ)ᶜ ≠ 0) : DiffuseExists := by
  classical
  let E := (atoms μ)ᶜ
  let ν := (μ E)⁻¹ • μ.restrict E
  refine ⟨ν, ⟨?_⟩, ?_⟩
  · rw [show ν univ = (μ E)⁻¹ * (μ.restrict E) univ from rfl, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel h (measure_ne_top _ _)
  · intro x
    change (μ E)⁻¹ * μ.restrict E {x} = 0
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    by_cases hx : x ∈ E
    · have hz : μ {x} = 0 := by simpa [E, atoms, not_lt] using hx
      rw [singleton_inter_of_mem hx, hz, mul_zero]
    · rw [singleton_inter_of_notMem hx, measure_empty, mul_zero]

/-- Without a diffuse law, every finite-budget randomized strategy fails
almost surely on one of the eligible partial labelings. -/
theorem atom_obstruction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hd : ¬ DiffuseExists) (A : Strategy Ω)
    (hm : ∀ t h, Measurable (A t h)) (m : ℕ) :
    ∃ U : Set Arm, Eligible U ∧ μ (failure A m U) = 1 := by
  classical
  let a (h : Fin m → Bool) (ω : Ω) := first (A m h ω)
  have ha (h : Fin m → Bool) : Measurable (a h) := Measurable.of_discrete.comp (hm m h)
  let ν (h : Fin m → Bool) := μ.map (a h)
  have hp (h : Fin m → Bool) : IsProbabilityMeasure (ν h) :=
    (Measure.isProbabilityMeasure_map_iff (ha h).aemeasurable).2 inferInstance
  let E := ⋃ h : Fin m → Bool, atoms (ν h)
  have cE : E.Countable := countable_iUnion fun h ↦ @atoms_countable (ν h) (hp h)
  have hit (h : Fin m → Bool) : ∀ᵐ ω ∂μ, a h ω ∈ E := by
    have hz : ν h (atoms (ν h))ᶜ = 0 := by
      by_contra hnon
      exact hd (@diffuse_of_residual (ν h) (hp h) hnon)
    rw [show ν h = μ.map (a h) from rfl, Measure.map_apply (ha h) MeasurableSet.of_discrete] at hz
    apply (ae_iff.mpr hz).mono
    exact fun ω hw ↦ mem_iUnion.mpr ⟨h, hw⟩
  let f (x : Coord) : Option Bool := if x ∈ E then none else some false
  have missing : {x | f x = none} = E := by ext; simp [f]
  have outside : ∃ x : Coord, x ∉ E := by
    by_contra! all
    exact not_countable (α := Coord) (countable_univ_iff.mp ((eq_univ_of_forall all) ▸ cE))
  obtain ⟨x,hx⟩ := outside
  have hn : (winSet f).Nonempty := ⟨(x,false), by change f x = some false; simp [f, hx]⟩
  refine ⟨winSet f, Or.inr ⟨f, missing ▸ cE, rfl⟩, ?_⟩
  have hall := ae_all_iff.mpr hit
  have hfull : failure A m (winSet f) =ᵐ[μ] univ := by
    filter_upwards [hall] with ω hw
    refine propext ⟨fun _ ↦ trivial, fun _ ↦ ⟨hn, ?_⟩⟩
    let branch := transcript A (winSet f) ω m
    change f (a branch ω) ≠ some (Prod.snd (A m branch ω))
    dsimp only [f]
    rw [ite_eq_left (hw branch)]
    intro contra
    cases contra
  rw [measure_congr hfull, measure_univ]

/-- Theorem 2. The power-set-measurable partial-label bandit is learnable
exactly when the whole powerset of the interval supports a diffuse law. -/
theorem learnable_iff_diffuse : Learnable ↔ DiffuseExists := by
  constructor
  · intro learn
    by_contra h
    obtain ⟨m, Ω, s, μ, hp, A, hm, hA⟩ := learn (1/2) (by norm_num)
    obtain ⟨U,hU,he⟩ := atom_obstruction μ h A hm m
    have hle := hA U hU
    rw [he] at hle
    norm_num at hle
  · rintro ⟨μ,hp,hn⟩ ε _
    refine ⟨1, Coord, inferInstance, μ, hp, oneQuery, fun _ _ ↦ Measurable.of_discrete, ?_⟩
    intro U hU
    rw [one_query_exact μ hn U hU]
    exact zero_le

end BinaryDiffuse

open Set MeasureTheory

namespace BinaryDiffuse

/-- The smallest sigma algebra making every allowed binary reward measurable
is the full powerset on the arms. -/
theorem reward_sigma_algebra :
    MeasurableSpace.generateFrom {U : Set Arm | Eligible U} = ⊤ := by
  classical
  let s := MeasurableSpace.generateFrom {U : Set Arm | Eligible U}
  have basic (f : Coord → Bool) :
      @MeasurableSet Arm s (winSet fun x ↦ some (f x)) := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact Or.inr ⟨_, by simp, rfl⟩
  apply top_unique
  intro T _
  let fiber (b : Bool) := winSet fun _ : Coord ↦ some b
  let graph (b : Bool) := winSet fun x ↦ some (if (show Arm from (x,b)) ∈ T then b else !b)
  have split : T = (fiber false ∩ graph false) ∪ (fiber true ∩ graph true) := by
    ext a
    obtain ⟨x,b⟩ := a
    change (show Arm from (x,b)) ∈ T ↔
      (some false = some b ∧ some (if (show Arm from (x,false)) ∈ T then false else !false) = some b) ∨
      (some true = some b ∧ some (if (show Arm from (x,true)) ∈ T then true else !true) = some b)
    cases b <;> by_cases hf : (show Arm from (x,false)) ∈ T <;>
      by_cases ht : (show Arm from (x,true)) ∈ T <;> simp [hf, ht]
  rw [split]
  exact @MeasurableSet.union Arm s _ _ (@MeasurableSet.inter Arm s _ _ (basic _) (basic _))
    (@MeasurableSet.inter Arm s _ _ (basic _) (basic _))

end BinaryDiffuse

open Set Cardinal

namespace BinaryBandit

/-- An orientation of the complete loopless graph with countable out-neighborhoods. -/
def CountableOrientation (X : Type) : Prop :=
  ∃ r : X → X → Prop, (∀ x, ¬ r x x) ∧
    (∀ x y, x ≠ y → (r x y ↔ ¬ r y x)) ∧ ∀ x, {y | r x y}.Countable

abbrev FirstUncountable := (ℵ₁ : Cardinal.{0}).ord.ToType

theorem size_first_uncountable : #FirstUncountable = ℵ₁ := by
  rw [FirstUncountable, mk_toType, Cardinal.card_ord]

instance : Uncountable FirstUncountable := Cardinal.aleph0_lt_mk_iff.mp (by
  rw [size_first_uncountable]
  exact aleph0_lt_aleph_one)

theorem countable_earlier (i : FirstUncountable) : (Iio i).Countable := by
  apply le_aleph0_iff_set_countable.mp
  exact not_lt.mp fun h ↦ (show #(Iio i) < ℵ₁ by simpa [FirstUncountable] using Cardinal.mk_Iio_lt i (by simp [FirstUncountable])).not_ge (aleph_one_le_iff.mpr h)

/-- The manuscript's alternative eligibility rule: the cardinal bound is
equivalent to admitting a complete-graph orientation of countable out-degree. -/
theorem countable_orientation_iff (X : Type) : CountableOrientation X ↔ #X ≤ ℵ₁ := by
  classical
  constructor
  · rintro ⟨r, _, complete, degree⟩
    by_contra! large
    obtain ⟨e⟩ := (le_def FirstUncountable X).mp (size_first_uncountable ▸ large.le)
    let setAt (i : FirstUncountable) : Set X := insert (e i) {y | r (e i) y}
    have bounds (i : FirstUncountable) : #(setAt i) ≤ ℵ₀ :=
      le_aleph0_iff_set_countable.mpr ((degree _).insert _)
    have small : #(⋃ i, setAt i) ≤ ℵ₁ := by
      calc _ ≤ #FirstUncountable * ⨆ i, #(setAt i) := mk_iUnion_le setAt
           _ ≤ #FirstUncountable * ℵ₀ := mul_le_mul_right (ciSup_le bounds) _
           _ = ℵ₁ := by rw [size_first_uncountable, aleph_mul_aleph0]
    have outside : ∃ z : X, z ∉ ⋃ i, setAt i := by
      by_contra! full
      rw [eq_univ_of_forall full, mk_univ] at small
      exact large.not_ge small
    obtain ⟨z,hz⟩ := outside
    have arrow (i : FirstUncountable) : r z (e i) := by
      have h : z ∉ setAt i := fun h ↦ hz (mem_iUnion_of_mem i h)
      have hne : z ≠ e i := fun he ↦ h (Or.inl he)
      exact (complete z (e i) hne).2 fun he ↦ h (Or.inr he)
    let f (i : FirstUncountable) : {y // r z y} := ⟨e i, arrow i⟩
    have one := mk_le_of_injective (f := f) (fun i j he ↦ e.injective (congrArg Subtype.val he))
    have contra : ℵ₁ ≤ ℵ₀ := size_first_uncountable ▸ one.trans (le_aleph0_iff_set_countable.mpr (degree z))
    exact (aleph_one_le_iff.mp contra).false
  · intro small
    obtain ⟨e⟩ := (le_def X FirstUncountable).mp (size_first_uncountable ▸ small)
    refine ⟨fun x y ↦ e y < e x, fun _ ↦ lt_irrefl _, ?_, ?_⟩
    · intro x y hxy
      exact ⟨fun h ↦ not_lt_of_ge h.le, fun h ↦ lt_of_le_of_ne (le_of_not_gt h) (fun he ↦ hxy (e.injective he.symm))⟩
    · intro x
      exact (countable_earlier (e x)).preimage e.injective

end BinaryBandit

open Set MeasureTheory Cardinal Function
open scoped ENNReal

namespace BinaryDiffuse

open BinaryBandit

/-- Ulam's matrix: no space of cardinality at most aleph one admits a
countably additive probability on all of its subsets vanishing on singletons. -/
theorem ulam {X : Type} [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (small : #X ≤ ℵ₁) (μ : Measure X) [IsProbabilityMeasure μ]
    (hn : ∀ x : X, μ {x} = 0) : False := by
  classical
  let _ : NullSingletonClass μ := ⟨hn⟩
  obtain ⟨e⟩ := (le_def X FirstUncountable).mp (size_first_uncountable ▸ small)
  let numbering (β : FirstUncountable) (i : Iio β) :=
    @Encodable.encode _ (countable_earlier β).toEncodable i
  have inject (β : FirstUncountable) : Injective (numbering β) :=
    @Encodable.encode_injective _ (countable_earlier β).toEncodable
  let cell (i : FirstUncountable) (j : ℕ) : Set X :=
    {x | ∃ h : i < e x, numbering (e x) ⟨i,h⟩ = j}
  have disj (j : ℕ) : Pairwise (fun i k ↦ Disjoint (cell i j) (cell k j)) := by
    intro i k hne
    apply Set.disjoint_left.mpr
    rintro x ⟨hi, ei⟩ ⟨hk, ek⟩
    exact hne (congrArg Subtype.val (inject (e x) (ei.trans ek.symm)))
  have count (j : ℕ) : {i | 0 < μ (cell i j)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun _ ↦ MeasurableSet.of_discrete) (disj j)
  have out : ∃ i : FirstUncountable, ∀ j, μ (cell i j) = 0 := by
    by_contra! hall
    have cover : (⋃ j, {i | 0 < μ (cell i j)}) = Set.univ := by
      apply eq_univ_of_forall
      intro i
      obtain ⟨j,hj⟩ := hall i
      exact mem_iUnion_of_mem j (pos_iff_ne_zero.mpr hj)
    exact not_countable (α := FirstUncountable) (countable_univ_iff.mp (cover ▸ countable_iUnion count))
  obtain ⟨i,hi⟩ := out
  let initial := e ⁻¹' Iic i
  have hc : initial.Countable := by
    exact (Iio_insert (a := i) ▸ (countable_earlier i).insert i).preimage e.injective
  have cover : initial ∪ (⋃ j, cell i j) = Set.univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : e x ≤ i
    · exact Or.inl hx
    · have hlt := lt_of_not_ge hx
      exact Or.inr (mem_iUnion_of_mem (numbering (e x) ⟨i,hlt⟩) ⟨hlt,rfl⟩)
  have z := measure_union_null (hc.measure_zero μ) (measure_iUnion_null_iff.mpr hi)
  rw [cover, measure_univ] at z
  exact one_ne_zero z

/-- Under the continuum hypothesis the discrete bandit of Theorem 2 is
unlearnable, by the Ulam-matrix argument on the actual interval. -/
theorem not_learnable_of_CH (ch : (𝔠 : Cardinal.{0}) = ℵ₁) : ¬ BinaryDiffuse.Learnable := by
  intro h
  obtain ⟨μ,hp,hn⟩ := learnable_iff_diffuse.mp h
  exact ulam (X := Coord) (by rw [show #Coord = (𝔠 : Cardinal.{0}) from mk_unitInterval, ch]) μ hn

end BinaryDiffuse
