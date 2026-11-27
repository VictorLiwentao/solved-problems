module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Separation.PerfectlyNormal
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

namespace UniversalWadge

open Set Filter
open scoped Classical Topology

abbrev Cantor := ℕ → Bool
abbrev Tests := ℕ → Cantor
abbrev Circle := AddCircle (1:ℝ)

def level (n : ℕ) := (n+2)^2

def character (n : ℕ) := 2^level n

noncomputable def dyad (j : ℕ) := (1/2:ℝ)^j

@[simp] theorem dyad_add (i j) : dyad (i+j) = dyad i * dyad j := pow_add ..

theorem dyad_pos (i) : 0 < dyad i := by unfold dyad;positivity

theorem dyad_antitone : Antitone dyad := fun _ _ h => pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem dyad_summable : Summable dyad := summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem dyad_sum : ∑' i, dyad i = 2 := by
  change (∑' i : ℕ, (1/2:ℝ)^i) = 2
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)];norm_num

theorem dyad_limit : Tendsto dyad atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem char_dyad (n : ℕ) : (character n:ℝ)*dyad (level n) = 1 := by
  unfold character dyad;push_cast;rw [← mul_pow];norm_num

noncomputable def bitValue (a : Tests) (j n : ℕ) := if a j n = true then dyad (j+2) else 0

noncomputable def digit (a : Tests) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (n+1) => bitValue a j.val n)

theorem digit_realized (a : Tests) (n) : ∃ j : Fin (n+1), digit a n = bitValue a j.val n := by
  obtain ⟨i,_,h⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun j : Fin (n+1) => bitValue a j.val n)
  exact ⟨i,h⟩

theorem digit_ge {a : Tests} {j n} (hj : j≤n) (hit : a j n=true) : dyad (j+2) ≤ digit a n := by
  have bound : bitValue a j n ≤ digit a n := Finset.le_sup' (fun i : Fin (n+1) => bitValue a i.val n) (Finset.mem_univ (⟨j,Nat.lt_succ_of_le hj⟩ : Fin (n+1)))
  simpa only [bitValue,hit,↓reduceIte] using bound

theorem digit_range (a : Tests) (n) : 0 ≤ digit a n ∧ digit a n ≤ 1/4 := by
  obtain ⟨j,r⟩ := digit_realized a n
  rw [r,bitValue];split
  · exact ⟨(dyad_pos _).le, (dyad_antitone (show 2≤j.val+2 by omega)).trans (by norm_num [dyad])⟩
  · norm_num

theorem digit_continuous (n) : Continuous (fun a => digit a n) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro j _
  exact (continuous_of_discreteTopology (f := fun b : Bool => if b=true then dyad (j.val+2) else 0)).comp
    ((continuous_apply n).comp (continuous_apply j.val))

noncomputable def term (a : Tests) (n : ℕ) := dyad (level n)*digit a n

theorem term_bound (a : Tests) (n : ℕ) : 0 ≤ term a n ∧ term a n ≤ dyad n := by
  have range := digit_range a n
  refine ⟨mul_nonneg (dyad_pos _).le range.1, ?_⟩
  apply (mul_le_of_le_one_right (dyad_pos _).le (by linarith : digit a n ≤ 1)).trans
  apply dyad_antitone;unfold level;nlinarith

theorem term_summable (a : Tests) : Summable (term a) :=
  Summable.of_nonneg_of_le (fun n => (term_bound a n).1) (fun n => (term_bound a n).2) dyad_summable

noncomputable def code (a : Tests) : Circle := ((∑' n, term a n : ℝ) : Circle)

theorem code_continuous : Continuous code :=
  (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_tsum (fun n => continuous_const.mul (digit_continuous n))
    dyad_summable (fun n a => by rw [Real.norm_eq_abs,abs_of_nonneg (term_bound a n).1];exact (term_bound a n).2))

end UniversalWadge

namespace UniversalWadge

open scoped Classical Topology

/-- Multiplying by the n-th character clears the denominators of every earlier digit. -/
theorem prior_integer (a : Tests) {i n : ℕ} (hi : i<n) :
    ∃ z : ℕ, (character n:ℝ)*term a i = z := by
  obtain ⟨j,hj⟩ := digit_realized a i
  unfold term
  rw [hj,bitValue];split
  · have bound : level i + (j.val+2) ≤ level n := by
      have m : (i+1+2)^2 ≤ (n+2)^2 := Nat.pow_le_pow_left (by omega) _
      have ji := j.isLt
      unfold level;nlinarith
    let d := level n - (level i+(j.val+2))
    have dec : level n = d+(level i+(j.val+2)) := (Nat.sub_add_cancel bound).symm
    refine ⟨2^d, ?_⟩
    rw [← dyad_add];unfold character dyad;push_cast;rw [dec,pow_add (2:ℝ) d _,mul_assoc,← mul_pow];norm_num
  · exact ⟨0,by simp⟩

noncomputable def tail (a : Tests) (n : ℕ) := ∑' j, (character n:ℝ)*term a (j+(n+1))

theorem scaled_tail_bound (a : Tests) (n j : ℕ) :
    (character n:ℝ)*term a (j+(n+1)) ≤ (dyad (n+1)/4)*dyad j := by
  let r := j+(n+1)
  have bounds : level n + (n+1+j) ≤ level r := by unfold level;dsimp [r];nlinarith
  have wd := mul_le_mul_of_nonneg_left (dyad_antitone bounds) (by positivity : 0 ≤ (character n:ℝ))
  rw [dyad_add,← mul_assoc,char_dyad,one_mul,dyad_add] at wd
  change (character n:ℝ)*(dyad (level r)*digit a r) ≤ _
  rw [← mul_assoc]
  calc
    _ ≤ (dyad (n+1)*dyad j)*(1/4) := mul_le_mul wd (digit_range a r).2 (digit_range a r).1
      (mul_nonneg (dyad_pos _).le (dyad_pos _).le)
    _ = _ := by ring

theorem tail_range (a : Tests) (n : ℕ) : 0 ≤ tail a n ∧ tail a n ≤ dyad (n+1)/2 := by
  have nn (j) : 0 ≤ (character n:ℝ)*term a (j+(n+1)) := mul_nonneg (Nat.cast_nonneg _) (term_bound a _).1
  have s := dyad_summable.mul_left (dyad (n+1)/4)
  have t := Summable.of_nonneg_of_le nn (scaled_tail_bound a n) s
  refine ⟨tsum_nonneg nn, (t.tsum_le_tsum (scaled_tail_bound a n) s).trans_eq ?_⟩
  rw [tsum_mul_left,dyad_sum];ring

theorem norm_character (a : Tests) (n : ℕ) : ‖character n • code a‖ = digit a n + tail a n := by
  let p (i) := (character n:ℝ)*term a i
  have sum : Summable p := (term_summable a).mul_left _
  let z (i : ℕ) := if h : i<n then (prior_integer a h).choose else 0
  have hz : (∑ i∈Finset.range n, p i) = ((∑ i∈Finset.range n, z i:ℕ):ℝ) := by
    push_cast;apply Finset.sum_congr rfl;intro i hi
    have lt := Finset.mem_range.mp hi
    simpa only [z,lt,↓reduceDIte] using (prior_integer a lt).choose_spec
  have mid : p n = digit a n := by dsimp [p,term];rw [← mul_assoc,char_dyad,one_mul]
  have parts : (character n:ℝ)*(∑' i, term a i) = ((∑ i∈Finset.range n, z i:ℕ):ℝ)+(digit a n+tail a n) := by
    rw [← tsum_mul_left, ← sum.sum_add_tsum_nat_add (n+1),Finset.sum_range_succ,hz,mid,add_assoc];rfl
  have clear : (((∑ i∈Finset.range n, z i:ℕ):ℝ):Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨(∑ i∈Finset.range n, z i:ℕ),by simp⟩
  change ‖character n • (((∑' i, term a i):ℝ):Circle)‖ = _
  rw [← AddCircle.coe_nsmul,nsmul_eq_mul,parts,AddCircle.coe_add,clear,zero_add]
  have r := tail_range a n
  have d := digit_range a n
  have le : dyad (n+1) ≤ 1/2 := (dyad_antitone (show 1≤n+1 by omega)).trans (by norm_num [dyad])
  rw [((AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num : (1:ℝ)≠0)).mpr (by
    rw [abs_of_nonneg (add_nonneg d.1 r.1),abs_one];linarith)), abs_of_nonneg (add_nonneg d.1 r.1)]

end UniversalWadge

namespace UniversalWadge

open Set Filter
open scoped Topology Classical

/-- A proper ideal of subsets of ℕ containing every finite set. -/
structure Ideal where
  family : Set (Set ℕ)
  finite : ∀ s : Set ℕ, s.Finite → s ∈ family
  shrink : ∀ {s t : Set ℕ}, s ⊆ t → t ∈ family → s ∈ family
  union : ∀ {s t : Set ℕ}, s∈family → t∈family → s∪t∈family
  proper : univ ∉ family

def support (a : Cantor) : Set ℕ := {n | a n=true}

def cantors (I : Ideal) : Set Cantor := {a | support a ∈ I.family}

def locus (I : Ideal) (seq : ℕ → ℕ) : Set Circle :=
  {x | ∀ ε : ℝ, 0 < ε → {n | ε < ‖seq n • x‖} ∈ I.family}

theorem ideal_finite_union (I : Ideal) (A : ℕ → Set ℕ) (h : ∀ j,A j∈I.family) (s : Finset ℕ) :
    (⋃ j∈s,A j)∈I.family := by
  induction s using Finset.induction_on with
  | empty => simpa using I.finite ∅ finite_empty
  | insert i s hi ih => simpa using I.union (h i) ih

/-- One explicit continuous code simultaneously reduces the countable power of
every ideal to the ideal-convergence subgroup for the same integer character sequence. -/
theorem productReduction : Continuous code ∧ ∀ (I : Ideal) (a : Tests),
    code a ∈ locus I character ↔ ∀ j,a j ∈ cantors I := by
  refine ⟨code_continuous, fun I a => ⟨?_,?_⟩⟩
  · intro hl j
    let ε := dyad (j+2)/2
    have ep : 0 < ε := div_pos (dyad_pos _) (by norm_num)
    have ex := hl ε ep
    apply I.shrink (t := (Finset.range j : Set ℕ) ∪ {n | ε < ‖character n • code a‖}) _ (I.union (I.finite _ (Finset.range j).finite_toSet) ex)
    intro n hit
    by_cases hn : n<j
    · exact Or.inl (Finset.mem_range.mpr hn)
    · right;change ε < ‖character n • code a‖;rw [norm_character]
      have le := digit_ge (Nat.le_of_not_gt hn) hit
      have t := (tail_range a n).1;dsimp [ε];linarith [dyad_pos (j+2)]
  · intro rows ε ep
    obtain ⟨N,hN⟩ := eventually_atTop.mp (dyad_limit.eventually (gt_mem_nhds (show 0 < ε/2 by linarith)))
    apply I.shrink (t := (Finset.range N : Set ℕ) ∪ ⋃ j∈Finset.range N, support (a j)) _
      (I.union (I.finite _ (Finset.range N).finite_toSet) (ideal_finite_union I _ rows _))
    intro n hit
    by_cases hn : n<N
    · exact Or.inl (Finset.mem_range.mpr hn)
    · right;change ε < ‖character n • code a‖ at hit;rw [norm_character] at hit
      have tl := (tail_range a n).2
      have small := hN (n+1) (by omega)
      obtain ⟨j,hd⟩ := digit_realized a n
      by_cases hj : a j.val n=true
      · have above : ε/2 < dyad (j.val+2) := by rw [hd,bitValue,ite_eq_left hj] at hit;linarith
        have little : j.val<N := by by_contra! h;linarith [hN (j.val+2) (by omega)]
        exact mem_iUnion.mpr ⟨j.val,mem_iUnion.mpr ⟨Finset.mem_range.mpr little,hj⟩⟩
      · rw [hd,bitValue,ite_eq_right hj] at hit;linarith

end UniversalWadge

namespace UniversalWadge

open Set
open scoped Classical

/-- The additive Borel classes: at positive rank α, start with open sets and close
under countable unions and complements of classes at strictly smaller ranks. -/
inductive AdditiveClass (X : Type) [TopologicalSpace X] : Ordinal.{0} → Set X → Prop
  | basic {α U} (positive : 0 < α) (h : IsOpen U) : AdditiveClass X α U
  | unions {α} (positive : 0 < α) {I : Type} [Countable I] (s : I → Set X)
      (hs : ∀ i,AdditiveClass X α (s i)) : AdditiveClass X α (⋃ i,s i)
  | lowerCompl {α β s} (low : β<α) (h : AdditiveClass X β s) : AdditiveClass X α sᶜ

def MultiplicativeClass (X : Type) [TopologicalSpace X] (α : Ordinal.{0}) (s : Set X) : Prop :=
  AdditiveClass X α sᶜ

theorem additive_positive {X} [TopologicalSpace X] {α s} (h : AdditiveClass X α s) : 0 < α := by
  induction h with | basic pos _ => exact pos | unions pos _ _ _ => exact pos | lowerCompl low _ ih => exact ih.trans low

theorem additive_baire {X} [TopologicalSpace X] {α s} (h : AdditiveClass X α s) : BaireMeasurableSet s := by
  induction h with | basic _ h => exact h.baireMeasurableSet | unions _ _ _ ih => exact .iUnion ih | lowerCompl _ _ ih => exact ih.compl

theorem additive_preimage {X Y} [TopologicalSpace X] [TopologicalSpace Y] {α s} {f : X → Y}
    (cf : Continuous f) (h : AdditiveClass Y α s) : AdditiveClass X α (f ⁻¹' s) := by
  induction h with
  | basic pos ho => exact .basic pos (ho.preimage cf)
  | unions pos u _ ih => rw [preimage_iUnion];exact .unions pos _ ih
  | lowerCompl low _ ih => exact .lowerCompl low ih

theorem relative_extension {X} [TopologicalSpace X] (G : Set X) {α s} (h : AdditiveClass G α s) :
    ∃ E : Set X, AdditiveClass X α E ∧ Subtype.val ⁻¹' E = s := by
  induction h with
  | basic pos ho =>
    obtain ⟨U,hU,eq⟩ := isOpen_induced_iff.mp ho
    exact ⟨U,.basic pos hU,eq⟩
  | unions pos u _ ih =>
    choose E hE eq using ih
    exact ⟨⋃ i,E i,.unions pos E hE,by simp only [preimage_iUnion,eq]⟩
  | lowerCompl low _ ih =>
    obtain ⟨E,hE,eq⟩ := ih
    exact ⟨Eᶜ,.lowerCompl low hE,by rw [preimage_compl,eq]⟩

end UniversalWadge

namespace UniversalWadge

open Set Filter TopologicalSpace
open scoped Classical Topology

abbrev Window {J : Type} [TopologicalSpace J] [SecondCountableTopology J] (U : Set J) :=
  {V : countableBasis J // V.val ⊆ U}

theorem nonmeagre_iff_window {J : Type} [TopologicalSpace J] [SecondCountableTopology J] [BaireSpace J]
    {S U : Set J} (Sbp : BaireMeasurableSet S) (Uo : IsOpen U) :
    ¬IsMeagre (S∩U) ↔ ∃ V : Window U, IsMeagre (Sᶜ ∩ V.val.val) := by
  constructor
  · intro nm
    obtain ⟨O,Oo,eq⟩ := Sbp.residualEq_isOpen
    obtain ⟨x,hx⟩ : (O∩U).Nonempty := by
      by_contra h;apply nm
      change ∀ᵇ t, t∉S∩U
      filter_upwards [eq] with t same
      exact fun ht => h ⟨t,same.mp ht.1,ht.2⟩
    obtain ⟨V,base,_,sub⟩ := (isBasis_countableBasis J).exists_subset_of_mem_open hx (Oo.inter Uo)
    refine ⟨⟨⟨V,base⟩,sub.trans inter_subset_right⟩,?_⟩
    change ∀ᵇ t, t∉Sᶜ∩V
    filter_upwards [eq] with t same
    exact fun ht => ht.1 (same.mpr (sub ht.2).1)
  · rintro ⟨V,me⟩ m
    have small : IsMeagre (S∩V.val.val) := m.mono (inter_subset_inter_right _ V.property)
    apply not_isMeagre_of_isOpen (isOpen_of_mem_countableBasis V.val.property) (nonempty_of_mem_countableBasis V.val.property)
    apply (small.union me).mono
    intro x hx;by_cases h : x∈S
    · exact Or.inl ⟨h,hx⟩
    · exact Or.inr ⟨h,hx⟩

def fiber {X J : Type} (E : Set (X×J)) (x : X) : Set J := (fun t => (x,t)) ⁻¹' E

def nonmeagreSection {X J : Type} [TopologicalSpace J] (E : Set (X×J)) (U : Set J) : Set X :=
  {x | ¬IsMeagre (fiber E x ∩ U)}

def comeagerSection {X J : Type} [TopologicalSpace J] (E : Set (X×J)) (U : Set J) : Set X :=
  (nonmeagreSection Eᶜ U)ᶜ

theorem section_open {X J : Type} [TopologicalSpace X] [TopologicalSpace J] [BaireSpace J]
    {E : Set (X×J)} (hE : IsOpen E) {U : Set J} (hU : IsOpen U) : IsOpen (nonmeagreSection E U) := by
  have eq : nonmeagreSection E U = Prod.fst '' (E ∩ Prod.snd ⁻¹' U) := by
    ext x; constructor
    · intro h
      have ne : (fiber E x ∩ U).Nonempty := by
        by_contra hn;exact h ((not_nonempty_iff_eq_empty.mp hn) ▸ IsMeagre.empty)
      obtain ⟨t,he,hu⟩ := ne;exact ⟨(x,t),⟨he,hu⟩,rfl⟩
    · rintro ⟨⟨x',t⟩,⟨he,hu⟩,rfl⟩
      exact not_isMeagre_of_isOpen ((hE.preimage (continuous_const.prodMk continuous_id)).inter hU) ⟨t,he,hu⟩
  rw [eq];exact isOpenMap_fst _ (hE.inter (hU.preimage continuous_snd))

theorem section_iUnion {X J I : Type} [TopologicalSpace J] [Countable I] (E : I → Set (X×J)) (U : Set J) :
    nonmeagreSection (⋃ i,E i) U = ⋃ i,nonmeagreSection (E i) U := by
  ext x; constructor
  · intro h;by_contra hn;apply h
    have me (i) : IsMeagre (fiber (E i) x ∩ U) := of_not_not (fun h => hn (mem_iUnion.mpr ⟨i,h⟩))
    simpa only [fiber,preimage_iUnion,iUnion_inter] using isMeagre_iUnion me
  · rintro hx;obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact fun h => hi (h.mono (inter_subset_inter_left _ (preimage_mono (subset_iUnion E i))))

/-- The nonmeager-section operation preserves every additive Borel class. -/
theorem section_additive {X J : Type} [TopologicalSpace X] [TopologicalSpace J]
    [SecondCountableTopology J] [BaireSpace J] {α E} (h : AdditiveClass (X×J) α E) :
    ∀ U : Set J, IsOpen U → AdditiveClass X α (nonmeagreSection E U) := by
  induction h with
  | basic pos ho => exact fun _ Uo => .basic pos (section_open ho Uo)
  | unions pos u _ ih => intro U ho;rw [section_iUnion];exact .unions pos _ (fun i => ih i U ho)
  | @lowerCompl α β E low h ih =>
    intro U ho
    have eq : nonmeagreSection Eᶜ U = ⋃ V : Window U,(nonmeagreSection E V.val.val)ᶜ := by
      ext x
      have bp := (additive_baire (additive_preimage (continuous_const.prodMk continuous_id) h)).compl (s := fiber E x)
      change (¬IsMeagre ((fiber E x)ᶜ∩U)) ↔ _
      rw [nonmeagre_iff_window bp ho]
      simp only [compl_compl,mem_iUnion,mem_compl_iff,nonmeagreSection,mem_ofPred_eq,not_not]
    rw [eq];exact .unions ((additive_positive h).trans low) _ (fun V => .lowerCompl low (ih _ (isOpen_of_mem_countableBasis V.val.property)))

/-- The comeager-section operation preserves multiplicative Borel rank. -/
theorem section_multiplicative {X J : Type} [TopologicalSpace X] [TopologicalSpace J]
    [SecondCountableTopology J] [BaireSpace J] {α E} (h : MultiplicativeClass (X×J) α E)
    (U : Set J) (hU : IsOpen U) : MultiplicativeClass X α (comeagerSection E U) := by
  simpa only [MultiplicativeClass,comeagerSection,compl_compl] using section_additive h U hU

end UniversalWadge

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

namespace UniversalWadge

open Set
open scoped Classical Topology

def Reduces {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (S : Set X) (T : Set Y) : Prop :=
  ∃ f : X → Y, Continuous f ∧ f ⁻¹' T = S

def allRows (I : Ideal) : Set Tests := {a | ∀ j,a j∈cantors I}

theorem reduces_trans {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {S : Set X} {T : Set Y} {R : Set Z} (f : Reduces S T) (g : Reduces T R) : Reduces S R := by
  obtain ⟨a,ca,ea⟩ := f;obtain ⟨b,cb,eb⟩ := g
  exact ⟨b ∘ a,cb.comp ca,by rw [preimage_comp,eb,ea]⟩

theorem rows_to_circle (I : Ideal) : Reduces (allRows I) (locus I character) :=
  ⟨code,productReduction.1,Set.ext (productReduction.2 I)⟩

theorem one_to_rows (I : Ideal) : Reduces (cantors I) (allRows I) :=
  ⟨fun x _ => x,continuous_pi (fun _ => continuous_id),by ext x; simp [allRows]⟩

/-- Countably many independent continuous reductions to the same ideal can be
combined into a single reduction to its countable power, including an empty family. -/
theorem combine {X J : Type} [TopologicalSpace X] [Countable J] (I : Ideal) (S : J → Set X)
    (h : ∀ j, Reduces (S j) (cantors I)) : Reduces (⋂ j,S j) (allRows I) := by
  let _ := Encodable.ofCountable J
  choose f cf eq using h
  let g (x : X) (n : ℕ) : Cantor := match Encodable.decode (α := J) n with
    | some j => f j x
    | none => fun _ => false
  have emp : (fun _ : ℕ => false)∈cantors I := by simpa [cantors,support] using I.finite ∅ finite_empty
  refine ⟨g,continuous_pi (fun n => ?_),Set.ext (fun x => ?_)⟩
  · dsimp [g];cases Encodable.decode (α := J) n with | some j => exact cf j | none => exact continuous_const
  · change (∀ n, g x n ∈ cantors I) ↔ _
    constructor
    · intro hx;apply mem_iInter.mpr;intro j
      have := hx (Encodable.encode j)
      rw [← eq j];simpa only [g,Encodable.encodek,Set.mem_preimage] using this
    · intro hs n;dsimp [g];cases Encodable.decode (α := J) n with
      | none => exact emp
      | some j => exact (Set.ext_iff.mp (eq j) x).mpr (mem_iInter.mp hs j)

theorem combine_rows {X J : Type} [TopologicalSpace X] [Countable J] (I : Ideal) (S : J → Set X)
    (h : ∀ j, Reduces (S j) (allRows I)) : Reduces (⋂ j,S j) (allRows I) := by
  choose f cf eq using h
  let P (p : J×ℕ) := (fun x => f p.1 x p.2) ⁻¹' cantors I
  have flat : (⋂ p, P p) = ⋂ j, S j := by
    ext x;simp only [P,mem_iInter,mem_preimage,Prod.forall]
    exact forall_congr' fun j => Set.ext_iff.mp (eq j) x
  rw [← flat];apply combine;intro p
  exact ⟨_,(continuous_apply _).comp (cf _),rfl⟩

theorem lower_classes_suffice {X : Type} [TopologicalSpace X] [PerfectlyNormalSpace X] (I : Ideal) {α : Ordinal.{0}}
    (gt : 1<α) (hard : ∀ β<α, ∀ S : Set X, AdditiveClass X β S → Reduces S (cantors I))
    {S : Set X} (h : MultiplicativeClass X α S) : Reduces S (locus I character) := by
  have aux {P : Set X} {γ} (p : AdditiveClass X γ P) : γ=α → Reduces Pᶜ (allRows I) := by
    induction p with
    | @basic γ U pos ho =>
      intro _
      obtain ⟨V,hV,eq⟩ := ho.isClosed_compl.isGδ.eq_iInter_nat
      rw [eq];exact combine I V (fun j => hard 1 gt _ (.basic zero_lt_one (hV j)))
    | unions pos u hs ih =>
      intro e;rw [compl_iUnion];exact combine_rows I _ (fun i => ih i e)
    | lowerCompl low hs _ =>
      rintro rfl;rw [compl_compl];exact reduces_trans (hard _ low _ hs) (one_to_rows I)
  apply reduces_trans _ (rows_to_circle I)
  simpa only [compl_compl] using aux h rfl

end UniversalWadge

namespace UniversalWadge

open Set Filter
open scoped Classical Topology

/-- Additive Borel codes are Borel measurable at every index. -/
theorem additive_borel {X} [TopologicalSpace X] {α S} (h : AdditiveClass X α S) : @MeasurableSet X (borel X) S := by
  let _ : MeasurableSpace X := borel X
  let _ : BorelSpace X := ⟨rfl⟩
  induction h with | basic _ ho => exact ho.measurableSet | unions _ _ _ ih => exact .iUnion ih | lowerCompl _ _ ih => exact ih.compl

theorem low_open {X} [TopologicalSpace X] {α S} (h : AdditiveClass X α S) (le : α≤1) : IsOpen S := by
  induction h with
  | basic _ ho => exact ho
  | unions _ _ _ ih => exact isOpen_iUnion (fun i => ih i le)
  | lowerCompl low h ih => exact False.elim ((not_lt_of_ge (show (1:Ordinal) ≤ _ by simpa using Order.succ_le_of_lt (additive_positive h))) (low.trans_le le))

theorem not_closed (I : Ideal) : ¬IsClosed (cantors I) := by
  intro closed
  let a (m n : ℕ) : Bool := decide (n<m)
  have limit : Tendsto a atTop (𝓝 (fun _ : ℕ => true)) := by
    apply tendsto_pi_nhds.mpr;intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with m hm;simp [a,hm]
  have small (m) : a m∈cantors I := by
    apply I.shrink (t := (Finset.range m:Set ℕ)) _ (I.finite _ (Finset.range m).finite_toSet)
    intro n hn; exact Finset.mem_range.mpr (by simpa [support,a] using hn)
  apply I.proper
  simpa [cantors,support] using closed.mem_of_tendsto limit (.of_forall small)

/-- The ideal convergence locus is an additive subgroup of the circle. -/
def convergenceSubgroup (I : Ideal) (seq : ℕ → ℕ) : AddSubgroup Circle where
  carrier := locus I seq
  zero_mem' := by
    intro ε ep
    simpa [not_lt.mpr ep.le] using I.finite (∅ : Set ℕ) finite_empty
  add_mem' := by
    intro x y hx hy ε ep
    have half : 0 < ε/2 := by linarith
    apply I.shrink _ (I.union (hx _ half) (hy _ half))
    intro n hn
    by_contra! no
    change ¬(ε/2 < ‖seq n • x‖ ∨ ε/2 < ‖seq n • y‖) at no
    push Not at no
    change ε < ‖seq n • (x+y)‖ at hn
    rw [smul_add] at hn
    linarith [norm_add_le (seq n • x) (seq n • y)]
  neg_mem' := by
    intro x hx ε ep
    simpa using hx ε ep

/-- This is the Borel Wadge alternative between two spaces. It is stated explicitly
so the transfer can be used separately from a formalization of Borel determinacy. -/
def WadgeAlternative (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Prop :=
  ∀ (S : Set X) (T : Set Y), @MeasurableSet X (borel X) S → @MeasurableSet Y (borel Y) T →
    Reduces S T ∨ Reduces Tᶜ S

def ExactRank (I : Ideal) (α : Ordinal.{0}) : Prop :=
  MultiplicativeClass Cantor α (cantors I) ∧ ∀ β<α, ¬MultiplicativeClass Cantor β (cantors I)

/-- For every ideal the fixed character subgroup has the same multiplicative upper
rank. Under the Borel Wadge alternative for the domain, exact rank implies hardness. -/
theorem rankTransfer {X : Type} [TopologicalSpace X] [PerfectlyNormalSpace X] (I : Ideal) (α : Ordinal.{0})
    (rank : ExactRank I α) (alternative : WadgeAlternative X Cantor) :
    MultiplicativeClass Circle α (locus I character) ∧
      ∀ S : Set X, MultiplicativeClass X α S → Reduces S (locus I character) := by
  refine ⟨(thresholdRanks I (fun n (x : Circle) => ‖character n • x‖)
    (fun n => (continuous_const_smul (character n)).norm) α).1 rank.1,?_⟩
  have gt : 1<α := by
    by_contra! le;exact not_closed I (isOpen_compl_iff.mp (low_open rank.1 le))
  have hard (β) (low : β<α) (S : Set X) (hS : AdditiveClass X β S) : Reduces S (cantors I) := by
    have borelI := MeasurableSet.of_compl (additive_borel rank.1)
    rcases alternative S (cantors I) (additive_borel hS) borelI with yes | no
    · exact yes
    · obtain ⟨f,cf,e⟩ := no
      have pre := additive_preimage cf hS;rw [e] at pre;exact False.elim (rank.2 β low pre)
  exact fun _ h => lower_classes_suffice I gt hard h

/-- Kwela's character version, with both rank estimates for every continuous sequence
of circle-valued characters on a topological group. -/
theorem characterRanks {G : Type} [TopologicalSpace G] [AddGroup G] (I : Ideal)
    (f : ℕ → ContinuousAddMonoidHom G Circle) (α : Ordinal.{0}) :
    (MultiplicativeClass Cantor α (cantors I) → MultiplicativeClass G α (realLocus I (fun n x => ‖f n x‖))) ∧
    (AdditiveClass Cantor α (cantors I) → MultiplicativeClass G (α+1) (realLocus I (fun n x => ‖f n x‖))) :=
  thresholdRanks I _ (fun n => (f n).continuous.norm) α

end UniversalWadge
