module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Find
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace EMX

/-- Block index j represents the manuscript parameter t = j+2. -/
abbrev width (j : ℕ) := j+2
abbrev Row (j : ℕ) := Fin (2^width j)
abbrev Col (j : ℕ) := Fin (width j)
abbrev Cell (j : ℕ) := Row j × Col j
abbrev Point := (j : ℕ) × Cell j
abbrev Holes (j : ℕ) := {s : Finset (Cell j) // s.card = width j}
abbrev Hyp := (j : ℕ) × Holes j

def support (h : Hyp) : Finset Point :=
  h.2.1ᶜ.map (Function.Embedding.sigmaMk h.1)

def omittedRow (j : ℕ) (i : Row j) : Holes j :=
  ⟨Finset.univ.image (fun k : Col j => (i,k)), by
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
    simp⟩

def baseline : Hyp := ⟨0, omittedRow 0 0⟩

/-- An ordered message of length at most d. The decoder can see an auxiliary
symbol and the sample-size bound through its choice of decoding function. -/
abbrev Message (X : Type) (d : ℕ) := (l : Fin (d+1)) × (Fin l.val → X)

def Reconstructs (d a m : ℕ) (D : Fin a → Message Point d → Hyp) : Prop :=
  ∀ xs : Fin m → Point, (∃ h : Hyp, ∀ i, xs i ∈ support h) →
    ∃ b w, (∀ i, ∃ k, w.2 i = xs k) ∧ ∀ i, xs i ∈ support (D b w)

end EMX

namespace EMX

theorem in_block {h : Hyp} {x : Point} (hx : x ∈ support h) : x.1 = h.1 := by
  obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hx
  rfl

theorem support_card (h : Hyp) : (support h).card = 2^width h.1 * width h.1 - width h.1 := by
  simp [support, Finset.card_compl, h.2.property, Cell, Row, Col]

theorem support_nonempty (h : Hyp) : (support h).Nonempty := by
  apply Finset.card_pos.mp
  rw [support_card]
  have ht : 0 < width h.1 := by simp [width]
  have hpow : 1 < 2^width h.1 := Nat.one_lt_two_pow ht.ne'
  have := Nat.mul_lt_mul_of_pos_right hpow ht
  omega

theorem support_injective_subset {h k : Hyp} (sub : support h ⊆ support k) : h = k := by
  obtain ⟨x, hx⟩ := support_nonempty h
  have eq := (in_block hx).symm.trans (in_block (sub hx))
  rcases h with ⟨j,H⟩
  rcases k with ⟨i,K⟩
  change j = i at eq
  subst i
  have setEq := Finset.eq_of_subset_of_card_le sub (by rw [support_card, support_card])
  have hc : H.valᶜ = K.valᶜ := Finset.map_injective (Function.Embedding.sigmaMk j) setEq
  have hk : H = K := Subtype.ext (compl_injective hc)
  rw [hk]

/-- Independently choose one hole per column. These are t-tuples of rows from a
2^t-element row set. -/
def onePerColumn {j : ℕ} (f : Col j → Row j) : Holes j :=
  ⟨Finset.univ.image (fun k => (f k,k)), by
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
    simp⟩

theorem onePerColumn_injective (j : ℕ) : Function.Injective (@onePerColumn j) := by
  intro f g h
  have he := congrArg Subtype.val h
  funext i
  have hi : (f i, i) ∈ (onePerColumn (j := j) f).val := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [he] at hi
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
  obtain rfl := congrArg Prod.snd hk
  exact (congrArg Prod.fst hk).symm

def liftMessage {d} (j : ℕ) (v : Message (Cell j) d) : Message Point d :=
  ⟨v.1, fun i => Sigma.mk j (v.2 i)⟩

theorem message_bound (j d : ℕ) :
    Fintype.card (Message (Cell j) d) ≤ (d+1)*(2^width j * width j)^d := by
  classical
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin (d+1), (2^width j * width j)^d := by
      apply Finset.sum_le_sum
      intro l _
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]
      apply Nat.pow_le_pow_right (Nat.mul_pos (by positivity) (by simp [width]))
      omega
    _ = _ := by simp

/-- Counting for a single block, using the complete realizable samples of one
common length. -/
theorem counting_necessary (j d a : ℕ) (D : Fin a → Message Point d → Hyp)
    (hD : Reconstructs d a (2^width j * width j - width j) D) :
    2^(width j * width j) ≤ a*(d+1)*(2^width j * width j)^d := by
  classical
  let H (f : Col j → Row j) : Hyp := ⟨j, onePerColumn f⟩
  have code (f : Col j → Row j) :
      ∃ v : Fin a × Message (Cell j) d, D v.1 (liftMessage j v.2) = H f := by
    let S := support (H f)
    let m := 2^width j * width j - width j
    let e : Fin m ≃ S := (Fintype.equivFinOfCardEq (by simpa [S] using support_card (H f))).symm
    let xs : Fin m → Point := fun i => (e i).val
    obtain ⟨b, w, hw, cov⟩ := hD xs ⟨H f, fun i => (e i).property⟩
    have getCell (i) : ∃ c : Cell j, w.2 i = Sigma.mk j c := by
      obtain ⟨k, hk⟩ := hw i
      rw [hk]
      obtain ⟨c, _, h⟩ := Finset.mem_map.mp (e k).property
      exact ⟨c, h.symm⟩
    let v : Message (Cell j) d := ⟨w.1, fun i => (getCell i).choose⟩
    have wEq : liftMessage j v = w := by
      cases w with
      | mk l f =>
        apply congrArg (Sigma.mk l)
        funext i
        exact (getCell i).choose_spec.symm
    refine ⟨(b,v), ?_⟩
    rw [wEq]
    apply Eq.symm
    apply support_injective_subset
    intro y hy
    obtain ⟨i, hi⟩ := e.surjective (⟨y,hy⟩ : S)
    simpa [xs, hi] using cov i
  have inj : Function.Injective (fun f => (code f).choose) := by
    intro f g he
    have heq : H f = H g := (code f).choose_spec.symm.trans
      ((congrArg (fun v : Fin a × Message (Cell j) d => D v.1 (liftMessage j v.2)) he).trans
        (code g).choose_spec)
    exact onePerColumn_injective j (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
  calc
    _ = Fintype.card (Col j → Row j) := by simp [Col,Row,Nat.pow_mul]
    _ ≤ Fintype.card (Fin a × Message (Cell j) d) := Fintype.card_le_of_injective _ inj
    _ ≤ _ := by
      rw [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (message_bound j d)

theorem noBoundedCompression (d a : ℕ) :
    ∃ m : ℕ, ∀ D : Fin a → Message Point d → Hyp, ¬Reconstructs d a m D := by
  let j := 4*(d+a+1)
  let t := width j
  refine ⟨2^t*t-t, ?_⟩
  intro D h
  have low := counting_necessary j d a D h
  change 2^(t*t) ≤ a*(d+1)*(2^t*t)^d at low
  have upper : a*(d+1)*(2^t*t)^d ≤ 2^(a+(d+1)+(t+t)*d) := by
    rw [Nat.pow_add 2 (a+(d+1)) _, Nat.pow_add 2 a (d+1), Nat.pow_mul 2 (t+t) d, Nat.pow_add 2 t t]
    exact Nat.mul_le_mul (Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le)
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le) _)
  have expLe := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (low.trans upper)
  dsimp [t,width,j] at expLe
  nlinarith only [expLe, Nat.zero_le (d*d), Nat.zero_le (a*a), Nat.zero_le (d*a)]

end EMX

namespace EMX

open scoped Classical

/-- A finite uniform bound on the number of candidates to examine in each block
at approximation stage s. -/
def slots (s : ℕ) := 2^(2^width s * width s)

theorem width_le_slots (s : ℕ) : s+1 ≤ slots s := by
  have h : width s ≤ 2^width s * width s := Nat.le_mul_of_pos_left _ (by positivity)
  exact (show s+1 ≤ width s by simp [width]).trans
    (h.trans Nat.lt_two_pow_self.le)

noncomputable def enumerate {α : Type} [Fintype α] (fallback : α) (k : ℕ) : α :=
  if h : k < Fintype.card α then (Fintype.equivFin α).symm ⟨k,h⟩ else fallback

theorem enumerate_hits {α : Type} [Fintype α] (fallback : α) (x : α) :
    enumerate fallback ((Fintype.equivFin α) x).val = x := by
  simp [enumerate, ((Fintype.equivFin α) x).isLt]

def rowIndex {s j} (h : s ≤ j) (u : Fin (s+1)) : Row j :=
  ⟨u.val, u.isLt.trans_le ((show s+1 ≤ width j by simp [width]; omega).trans Nat.lt_two_pow_self.le)⟩

/-- Small blocks keep every possible mask. In every larger block the first s+1
disjoint rows provide all the required alternatives. -/
noncomputable def restricted (s j : ℕ) (k : Fin (slots s)) : Hyp :=
  if h : j < s then ⟨j, enumerate (omittedRow j 0) k.val⟩
  else ⟨j, omittedRow j (rowIndex (Nat.le_of_not_gt h) (enumerate (0 : Fin (s+1)) k.val))⟩

theorem restricted_block (s j) (k) : (restricted s j k).1 = j := by
  unfold restricted; split <;> rfl

theorem small_covered {s j} (h : j < s) (z : Holes j) :
    ∃ k, restricted s j k = Sigma.mk j z := by
  classical
  have hcard : Fintype.card (Holes j) ≤ slots s := by
    calc
      _ ≤ Fintype.card (Finset (Cell j)) := Fintype.card_subtype_le _
      _ = 2^(2^width j * width j) := by simp [Cell,Row,Col]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide) (by simp [width]; omega)) (by simp [width]; omega))
  let v := (Fintype.equivFin (Holes j)) z
  exact ⟨⟨v.val, v.isLt.trans_le hcard⟩, by
    simp only [restricted, dite_eq_left h]
    exact congrArg (Sigma.mk j) (enumerate_hits _ z)⟩

theorem large_covered {s j} (h : s ≤ j) (u : Fin (s+1)) :
    ∃ k, restricted s j k = Sigma.mk j (omittedRow j (rowIndex h u)) := by
  let v := (Fintype.equivFin (Fin (s+1))) u
  have hv : v.val < s+1 := by simpa using v.isLt
  exact ⟨⟨v.val, hv.trans_le (width_le_slots s)⟩, by
    simp only [restricted, dite_eq_right (Nat.not_lt_of_ge h)]
    rw [show enumerate (0 : Fin (s+1)) v.val = u from enumerate_hits _ u]⟩

def hits {m} (xs : Fin m → Point) (h : Hyp) :=
  (Finset.univ.filter fun i => xs i ∈ support h).card

theorem attainable (s : ℕ) {m} (xs : Fin m → Point) :
    ∃ n : ℕ, ∃ v : ℕ × Fin (slots s), m - hits xs (restricted s v.1 v.2) = n :=
  ⟨_, (0, ⟨0, Nat.two_pow_pos _⟩), rfl⟩

noncomputable def best (s : ℕ) {m} (xs : Fin m → Point) : ℕ × Fin (slots s) := by
  classical
  exact (Nat.find_spec (attainable s xs)).choose

theorem best_spec (s : ℕ) {m} (xs : Fin m → Point) (v : ℕ × Fin (slots s)) :
    hits xs (restricted s v.1 v.2) ≤ hits xs (restricted s (best s xs).1 (best s xs).2) := by
  classical
  have min := (Nat.find_spec (attainable s xs)).choose_spec.trans_le
    (Nat.find_min' (attainable s xs) ⟨v,rfl⟩)
  change m - hits xs (restricted s (best s xs).1 (best s xs).2) ≤ _ at min
  have l (z : Hyp) : hits xs z ≤ m := by simpa [hits] using
    (Finset.card_le_univ (Finset.univ.filter (fun i => xs i ∈ support z)))
  have := l (restricted s v.1 v.2)
  omega

end EMX

namespace EMX

open MeasureTheory Set
open scoped ENNReal

/-- Every subset of the countable domain is measurable. -/
scoped instance pointSpace : MeasurableSpace Point := ⊤
scoped instance discretePointSpace : DiscreteMeasurableSpace Point := ⟨fun _ => trivial⟩

abbrev Learner := (m : ℕ) → (Fin m → Point) → Hyp

def deficitEvent (A : Learner) (μ : Measure Point) (m : ℕ) (ε : ℝ) : Set (Fin m → Point) :=
  {xs | ∃ h : Hyp, μ.real (support (A m xs) : Set Point) + ε < μ.real (support h : Set Point)}

/-- A single proper learner works for all accuracies and confidence levels on all
probability laws under their ordinary independent product sampling measures. -/
def Learnable : Prop := ∃ A : Learner, ∀ ε δ : ℝ, 0 < ε → 0 < δ →
  ∃ M : ℕ, ∀ m ≥ M, ∀ μ : Measure Point, IsProbabilityMeasure μ →
    Measure.pi (fun _ : Fin m => μ) (deficitEvent A μ m ε) ≤ ENNReal.ofReal δ

end EMX

namespace EMX

open MeasureTheory Set
open scoped ENNReal Classical

def rowSet {j} (i : Row j) : Set Point :=
  ↑((omittedRow j i).val.map (Function.Embedding.sigmaMk j))

theorem disjoint_rows {j} {i k : Row j} (h : i ≠ k) : Disjoint (rowSet i) (rowSet k) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hc
  have hh : (i,z) ∈ (omittedRow j k).val := by simpa [rowSet] using hx'
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hh
  exact h (congrArg Prod.fst hw).symm

theorem cover_block {j} (h : Holes j) (row : Row j) :
    (support ⟨j,h⟩ : Set Point) ⊆ (support ⟨j,omittedRow j row⟩ : Set Point) ∪ rowSet row := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
  by_cases hh : c ∈ (omittedRow j row).val
  · exact Or.inr (Finset.mem_map.mpr ⟨c, hh, rfl⟩)
  · exact Or.inl (Finset.mem_map.mpr ⟨c, Finset.mem_compl.mpr hh, rfl⟩)

theorem light_row {s j : ℕ} (large : s ≤ j) (μ : Measure Point) [IsProbabilityMeasure μ] :
    ∃ i : Fin (s+1), μ.real (rowSet (rowIndex large i)) ≤ 1/(s+1:ℝ) := by
  let R (i : Fin (s+1)) := rowSet (rowIndex large i)
  have dis : Pairwise (fun i k => Disjoint (R i) (R k)) := by
    intro i k hn
    apply disjoint_rows
    exact fun he => hn (Fin.ext (congrArg (fun i : Row j => i.val) he))
  have total : (∑ i : Fin (s+1), μ.real (R i)) ≤ 1 := by
    simpa only [probReal_univ] using
      sum_measureReal_le_measureReal_univ (s := Finset.univ) (μ := μ)
        (t := R) (fun _ _ => MeasurableSet.of_discrete) (fun _ _ _ _ h => dis h)
  have hh : (∑ _i : Fin (s+1), 1/(s+1:ℝ)) = 1 := by
    simp [ne_of_gt (show (0:ℝ) < s+1 by positivity)]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    (f := fun i : Fin (s+1) => μ.real (R i)) (g := fun _ => 1/(s+1:ℝ))
    Finset.univ_nonempty (total.trans hh.ge)
  exact ⟨i,hi⟩

/-- Some retained hypothesis loses at most 1/(s+1) compared with each member of
the full family, uniformly in the distribution and the index of its block. -/
theorem approximates (μ : Measure Point) [IsProbabilityMeasure μ] (s : ℕ) (H : Hyp) :
    ∃ v : ℕ × Fin (slots s), μ.real (support H : Set Point) ≤
      μ.real (support (restricted s v.1 v.2) : Set Point) + 1/(s+1:ℝ) := by
  classical
  obtain ⟨j,h⟩ := H
  by_cases small : j < s
  · obtain ⟨k,hk⟩ := small_covered small h
    refine ⟨(j,k), ?_⟩
    change _ ≤ μ.real (support (restricted s j k) : Set Point) + _
    rw [hk]
    exact le_add_of_nonneg_right (by positivity)
  have large : s ≤ j := Nat.le_of_not_gt small
  obtain ⟨i, hi⟩ := light_row large μ
  obtain ⟨k, hk⟩ := large_covered large i
  refine ⟨(j,k), ?_⟩
  change _ ≤ μ.real (support (restricted s j k) : Set Point) + _
  rw [hk]
  exact (measureReal_mono (μ := μ) (cover_block h (rowIndex large i))).trans
    ((measureReal_union_le (μ := μ) _ _).trans (add_le_add le_rfl hi))

end EMX

namespace EMX

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable def frequency {X : Type} {m : ℕ} (S : Set X) (xs : Fin m → X) : ℝ :=
  (∑ i, S.indicator (fun _ => (1 : ℝ)) (xs i)) / m

/-- The single-set deviation bound retains the factor μ(S), allowing a countable
union bound for families disjoint within each slot. -/
theorem frequency_tail {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {S : Set X} (hs : MeasurableSet S) {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    Measure.pi (fun _ : Fin m => μ) {xs | η ≤ |frequency S xs - μ.real S|}
      ≤ μ S * ENNReal.ofReal (1 / ((m:ℝ) * η^2)) := by
  classical
  let f := S.indicator (fun _ => (1 : ℝ))
  let ν := Measure.pi (fun _ : Fin m => μ)
  let Y (i : Fin m) (xs : Fin m → X) := f (xs i)
  let Z (xs : Fin m → X) := ∑ i, Y i xs
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hf : MemLp f 2 μ := (memLp_const (1:ℝ)).indicator hs.nullMeasurableSet
  have hY (i) : MemLp (Y i) 2 ν := hf.comp_measurePreserving (measurePreserving_eval _ i)
  have hZ : MemLp Z 2 ν := memLp_finsetSum _ fun i _ => hY i
  have intf : ∫ x, f x ∂μ = μ.real S := integral_indicator_one hs
  have intY (i) : ∫ xs, Y i xs ∂ν = μ.real S := (integral_comp_eval (μ := fun _ : Fin m => μ) (i := i) (f := f) hf.aestronglyMeasurable).trans intf
  have eZ : ∫ xs, Z xs ∂ν = m * μ.real S := by
    rw [show (∫ xs, Z xs ∂ν) = ∑ i, ∫ xs, Y i xs ∂ν from
      integral_finsetSum _ fun i _ => (hY i).integrable (by norm_num)]
    simp [intY]
  have vf : variance f μ ≤ μ.real S := by
    have sqf : f ^ 2 = f := by
      funext x
      by_cases hx : x ∈ S <;> simp [f, hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    simpa only [sqf, intf] using variance_le_expectation_sq hf.aestronglyMeasurable
  have vZ : variance Z ν ≤ m * μ.real S := by
    have h : variance Z ν = ∑ _i : Fin m, variance f μ := by
      convert variance_sum_pi (μ := fun _ : Fin m => μ) (X := fun _ => f) (fun _ => hf) using 2
      funext xs; simp [Z, Y]
    rw [h]
    simpa using mul_le_mul_of_nonneg_left vf hm'.le
  have eventSub : {xs : Fin m → X | η ≤ |frequency S xs - μ.real S|} ⊆
      {xs | (m:ℝ)*η ≤ |Z xs - ∫ xs, Z xs ∂ν|} := by
    intro xs hx
    change η ≤ |Z xs / m - μ.real S| at hx
    change (m:ℝ)*η ≤ |Z xs - ∫ xs, Z xs ∂ν|
    rw [eZ, show Z xs - (m:ℝ)*μ.real S = (m:ℝ)*(Z xs/m - μ.real S) by field_simp,
      abs_mul, abs_of_pos hm']
    exact mul_le_mul_of_nonneg_left hx hm'.le
  calc
    _ ≤ _ := measure_mono (μ := ν) eventSub
    _ ≤ _ := meas_ge_le_variance_div_sq hZ (mul_pos hm' hη)
    _ ≤ ENNReal.ofReal ((m * μ.real S) / ((m:ℝ)*η)^2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right vZ (sq_nonneg _))
    _ = _ := by
      rw [show ((m:ℝ) * μ.real S) / ((m:ℝ)*η)^2 = μ.real S * (1 / ((m:ℝ)*η^2)) by field_simp]
      rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end EMX

namespace EMX

open Set MeasureTheory
open scoped ENNReal Classical

def candidates (s j : ℕ) (k : Fin (slots s)) : Set Point := ↑(support (restricted s j k))

theorem block_disjoint (s : ℕ) (k : Fin (slots s)) :
    Pairwise (fun i j => Disjoint (candidates s i k) (candidates s j k)) := by
  intro i j ne
  apply Set.disjoint_left.mpr
  intro x hi hj
  apply ne
  have a := in_block hi
  have b := in_block hj
  rw [restricted_block] at a b
  exact a.symm.trans b

/-- Within a slot the sets for distinct blocks are disjoint, so the sum of the
single-set deviation bounds costs only one unit of probability mass. -/
theorem uniform_tail (s : ℕ) (μ : Measure Point) [IsProbabilityMeasure μ] {m : ℕ}
    (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    Measure.pi (fun _ : Fin m => μ)
      (⋃ k : Fin (slots s), ⋃ j : ℕ, {xs | η ≤ |frequency (candidates s j k) xs -
        μ.real (candidates s j k)|}) ≤ ENNReal.ofReal (slots s / ((m:ℝ)*η^2)) := by
  classical
  let ν := Measure.pi (fun _ : Fin m => μ)
  let M := ENNReal.ofReal (1 / ((m:ℝ)*η^2))
  let E (k : Fin (slots s)) (j : ℕ) := {xs : Fin m → Point |
    η ≤ |frequency (candidates s j k) xs - μ.real (candidates s j k)|}
  have forSlot (k : Fin (slots s)) : ν (⋃ j, E k j) ≤ M := by
    calc
      _ ≤ ∑' j : ℕ, ν (E k j) := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, μ (candidates s j k) * M := ENNReal.tsum_le_tsum
        (fun _ => frequency_tail μ MeasurableSet.of_discrete hm hη)
      _ = μ (⋃ j, candidates s j k) * M := by
        rw [ENNReal.tsum_mul_right, measure_iUnion (block_disjoint s k) (fun _ => MeasurableSet.of_discrete)]
      _ ≤ 1*M := mul_le_mul_of_nonneg_right (by simpa using measure_mono (μ := μ) (subset_univ (⋃ j, candidates s j k))) zero_le
      _ = M := one_mul _
  change ν (⋃ k, ⋃ j, E k j) ≤ _
  calc
    _ ≤ ∑' k, ν (⋃ j, E k j) := measure_iUnion_le _
    _ ≤ ∑' _k : Fin (slots s), M := ENNReal.tsum_le_tsum forSlot
    _ = (slots s : ℝ≥0∞) * M := by simp
    _ = _ := by
      rw [show (slots s : ℝ) / ((m:ℝ)*η^2) = slots s * (1 / ((m:ℝ)*η^2)) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

noncomputable def stageLearner (s : ℕ) : Learner :=
  fun _ xs => restricted s (best s xs).1 (best s xs).2

theorem empirical_eq {m} (h : Hyp) (xs : Fin m → Point) :
    frequency (support h : Set Point) xs = (hits xs h : ℝ) / m := by
  unfold frequency hits
  congr 1
  simpa only [Set.indicator_apply, Finset.mem_coe] using (Finset.sum_boole (R := ℝ) (fun i => xs i ∈ support h) Finset.univ)

theorem stage_bound (s : ℕ) (μ : Measure Point) [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) :
    Measure.pi (fun _ : Fin m => μ) (deficitEvent (stageLearner s) μ m (3/(s+1:ℝ)))
      ≤ ENNReal.ofReal ((slots s : ℝ) / ((m:ℝ)*(1/(s+1:ℝ))^2)) := by
  let η : ℝ := 1/(s+1:ℝ)
  have hη : 0 < η := by dsimp [η]; positivity
  apply (measure_mono _).trans (uniform_tail s μ hm hη)
  intro xs hx
  obtain ⟨h, hh⟩ := hx
  obtain ⟨v, hv⟩ := approximates μ s h
  let w := best s xs
  by_contra hout
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hout
  have a := (abs_lt.mp (hout v.2 v.1)).1
  have b := (abs_lt.mp (hout w.2 w.1)).2
  change -η < frequency (support (restricted s v.1 v.2) : Set Point) xs - _ at a
  change frequency (support (restricted s w.1 w.2) : Set Point) xs - _ < η at b
  rw [empirical_eq] at a b
  have score := div_le_div_of_nonneg_right
    (show (hits xs (restricted s v.1 v.2) : ℝ) ≤ hits xs (restricted s w.1 w.2) by
      exact_mod_cast best_spec s xs v) (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  change μ.real (support (restricted s w.1 w.2) : Set Point) + 3/(s+1:ℝ) < _ at hh
  change -η < _ - μ.real (support (restricted s v.1 v.2) : Set Point) at a
  change _ - μ.real (support (restricted s w.1 w.2) : Set Point) < η at b
  dsimp only [η] at a b
  rw [show (3:ℝ)/(s+1) = 3*(1/(s+1:ℝ)) by ring] at hh
  linarith only [hh,hv,a,b,score]

end EMX

namespace EMX

open scoped Classical

/-- Fix one cyclic successor permutation on each finite set. -/
noncomputable def cycle {X : Type} [Fintype X] [DecidableEq X] (U : Finset X) :
    Equiv.Perm X := (U.exists_cycleOn).choose

theorem escapes {X : Type} [Fintype X] [DecidableEq X] {S U : Finset X}
    (hs : S.Nonempty) (sub : S ⊆ U) (gap : (U \ S).Nonempty) :
    ∃ x ∈ S, cycle U x ∈ U \ S := by
  classical
  obtain ⟨a,ha⟩ := hs
  obtain ⟨b,hb⟩ := gap
  obtain ⟨hbU,hbS⟩ := Finset.mem_sdiff.mp hb
  have cyc : (cycle U).IsCycleOn (U : Set X) := U.exists_cycleOn.choose_spec.1
  obtain ⟨n, _, hn⟩ := cyc.exists_pow_eq (sub ha) hbU
  by_contra! h
  have stable (x) (hx : x ∈ S) : cycle U x ∈ S := by
    have inU : cycle U x ∈ U := cyc.apply_mem_iff.mpr (sub hx)
    by_contra out
    exact h x hx (Finset.mem_sdiff.mpr ⟨inU, out⟩)
  have stay (k : ℕ) : (cycle U ^ k) a ∈ S := by
    induction k with
    | zero => simpa using ha
    | succ k ih => simpa [pow_succ', Equiv.Perm.mul_apply] using stable _ ih
  exact hbS (hn ▸ stay n)

/-- Processing the anchors from the end of the list, omit the cyclic successor
among all positions which have not already been omitted. -/
noncomputable def grow {X : Type} [Fintype X] [DecidableEq X] : List X → Finset X
  | [] => ∅
  | x :: w => let omitted := grow w; insert (cycle omittedᶜ x) omitted

theorem encode_holes {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (hs : S.Nonempty)
    (k : ℕ) (hcard : k ≤ Sᶜ.card) :
    ∃ w : List X, w.length = k ∧ (∀ x ∈ w, x ∈ S) ∧
      (grow w).card = k ∧ grow w ⊆ Sᶜ := by
  induction k with
  | zero => exact ⟨[], rfl, by simp, rfl, Finset.empty_subset _⟩
  | succ k ih =>
    obtain ⟨w,hw,hwS,hg,hgS⟩ := ih (Nat.le_of_succ_le hcard)
    have sub : S ⊆ (grow w)ᶜ := by
      intro x hx
      exact Finset.mem_compl.mpr (fun hc => Finset.mem_compl.mp (hgS hc) hx)
    have gap : ((grow w)ᶜ \ S).Nonempty := by
      have card : (grow w).card < Sᶜ.card := by omega
      obtain ⟨x,hx,hg⟩ := Finset.exists_mem_notMem_of_card_lt_card card
      exact ⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hg,Finset.mem_compl.mp hx⟩⟩
    obtain ⟨x,hx,hnext⟩ := escapes hs sub gap
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hnext
    refine ⟨x::w, by simp [hw], ?_, ?_, ?_⟩
    · simpa [hx] using hwS
    · simp [grow, Finset.mem_compl.mp hin, hg]
    · exact Finset.insert_subset (Finset.mem_compl.mpr hout) hgS

end EMX

namespace EMX

open scoped Classical

def project (j : ℕ) (x : Point) : Cell j :=
  if h : x.1 = j then h ▸ x.2 else (0,0)

theorem project_mk (j) (x : Cell j) : project j ⟨j,x⟩ = x := by simp [project]

noncomputable def restore : List Point → Hyp
  | [] => baseline
  | x::xs =>
    let j := x.1
    let c := project j x
    if xs = [] then ⟨j, omittedRow j (cycle Finset.univ c.1)⟩
    else let holes := grow (List.map (project j) (x::xs))
         if h : holes.card = width j then ⟨j,⟨holes,h⟩⟩ else baseline

noncomputable def decoder {d : ℕ} (_ : Fin 1) (w : Message Point d) : Hyp := restore (List.ofFn w.2)

theorem restore_one {j : ℕ} (x : Cell j) :
    restore [Sigma.mk j x] = ⟨j,omittedRow j (cycle Finset.univ x.1)⟩ := by
  simp [restore,project_mk]

theorem restore_many {j : ℕ} {w : List (Cell j)} (hle : 2 ≤ w.length)
    (hsize : (grow w).card = width j) :
    restore (w.map (Sigma.mk j)) = ⟨j,⟨grow w,hsize⟩⟩ := by
  cases w with
  | nil => simp at hle
  | cons x w =>
    have hw : w ≠ [] := by intro eq; simp [eq] at hle
    simp [restore, List.map_map, Function.comp_def, project_mk, hw, hsize]

theorem choose_anchors {j : ℕ} (S : Finset (Cell j)) (ne : S.Nonempty)
    (realizable : ∃ h : Holes j, S ⊆ h.valᶜ) :
    ∃ w : List (Cell j), (∀ x ∈ w, x ∈ S) ∧
      (w.length = 1 ∨ (w.length = width j ∧ 2^width j ≤ S.card)) ∧
      ∀ x ∈ S, Sigma.mk j x ∈ support (restore (w.map (Sigma.mk j))) := by
  let touched := S.image Prod.fst
  have hne : touched.Nonempty := ne.image _
  by_cases full : touched = Finset.univ
  · obtain ⟨h,hh⟩ := realizable
    have enough : width j ≤ Sᶜ.card := by
      apply h.property.ge.trans
      exact Finset.card_le_card (fun x hx => Finset.mem_compl.mpr (fun hxS => Finset.mem_compl.mp (hh hxS) hx))
    obtain ⟨w,hw,inside,count,sub⟩ := encode_holes S ne (width j) enough
    have hcard : 2^width j ≤ S.card := by
      have hc := Finset.card_image_le (s := S) (f := Prod.fst)
      change touched.card ≤ _ at hc
      simpa [full,Row] using hc
    refine ⟨w,inside,Or.inr ⟨hw,hcard⟩, ?_⟩
    intro x hx
    rw [restore_many (by rw [hw]; simp [width]) count]
    apply Finset.mem_map.mpr
    exact ⟨x, Finset.mem_compl.mpr (fun bad => Finset.mem_compl.mp (sub bad) hx), rfl⟩
  · have gap : ((Finset.univ : Finset (Row j)) \ touched).Nonempty := by
      by_contra! hg
      apply full
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hn
      have hx : i ∈ Finset.univ \ touched := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩
      rw [hg] at hx
      exact Finset.notMem_empty _ hx
    obtain ⟨i,hi,hnext⟩ := escapes hne (Finset.subset_univ _) gap
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    refine ⟨[x], by simpa, Or.inl rfl, ?_⟩
    intro y hy
    rw [List.map_cons, List.map_nil, restore_one]
    apply Finset.mem_map.mpr
    refine ⟨y, Finset.mem_compl.mpr ?_, rfl⟩
    intro hy'
    obtain ⟨k, _, eq⟩ := Finset.mem_image.mp hy'
    apply (Finset.mem_sdiff.mp hnext).2
    rw [show cycle Finset.univ x.1 = y.1 from congrArg Prod.fst eq]
    exact Finset.mem_image_of_mem _ hy

end EMX

namespace EMX

open scoped Classical

theorem lift_project {j : ℕ} (x : Point) (hj : x.1 = j) : Sigma.mk j (project j x) = x := by
  obtain ⟨k,c⟩ := x
  change k = j at hj
  subst j
  simp [project_mk]

/-- A single decoder at each size bound handles all realizable samples up to
that size, including ordered lists with repetitions. -/
def Within (d m : ℕ) : Prop :=
  ∃ D : Fin 1 → Message Point d → Hyp, ∀ n ≤ m, Reconstructs d 1 n D

theorem logUpper (m : ℕ) : Within (max 1 m.log2) m := by
  let d := max 1 m.log2
  refine ⟨decoder, ?_⟩
  intro n hn xs hx
  by_cases empty : n = 0
  · subst n
    let w : Message Point d := ⟨⟨0, Nat.zero_lt_succ _⟩, Fin.elim0⟩
    exact ⟨0,w,fun i => i.elim0,fun i => i.elim0⟩
  obtain ⟨⟨j,h⟩, hh⟩ := hx
  let S := Finset.univ.image (fun i => project j (xs i))
  have loc (i) : Sigma.mk j (project j (xs i)) = xs i := lift_project _ (in_block (hh i))
  let i₀ : Fin n := ⟨0,Nat.pos_of_ne_zero empty⟩
  have hs : S.Nonempty := ⟨_,Finset.mem_image_of_mem _ (Finset.mem_univ i₀)⟩
  have fit : S ⊆ h.valᶜ := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    have hi := hh i
    rw [← loc i] at hi
    simpa [support] using hi
  obtain ⟨w,inside,size,cover⟩ := choose_anchors S hs ⟨h,fit⟩
  have hwd : w.length ≤ d := by
    rcases size with size | ⟨size,rowCount⟩
    · rw [size]; exact Nat.le_max_left .. 
    · apply (show w.length ≤ m.log2 from ?_).trans (Nat.le_max_right ..)
      rw [size]
      apply (Nat.le_log2 (by omega : m ≠ 0)).mpr
      have cardS : S.card ≤ n := by simpa [S] using
        (Finset.card_image_le (s := Finset.univ) (f := fun i => project j (xs i)))
      exact rowCount.trans (cardS.trans hn)
  let v : Message Point d := ⟨⟨w.length, Nat.lt_succ_of_le hwd⟩, fun i => Sigma.mk j w[i.val]⟩
  have dl : decoder 0 v = restore (w.map (Sigma.mk j)) := by
    exact congrArg restore (List.ofFn_getElem_eq_map w (Sigma.mk j))
  refine ⟨0, v, ?_, ?_⟩
  · intro i
    have hi : w[i.val] ∈ S := inside _ (List.getElem_mem _)
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
    exact ⟨k, (congrArg (Sigma.mk j) hk.symm).trans (loc k)⟩
  · intro i
    rw [dl, ← loc i]
    exact cover _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end EMX

namespace EMX

open scoped Classical

noncomputable def optimalSize (m : ℕ) : ℕ :=
  sInf {d : ℕ | Within d m}

theorem optimal_spec (m : ℕ) : Within (optimalSize m) m ∧ ∀ d, Within d m → optimalSize m ≤ d :=
  ⟨csInf_mem (s := {d : ℕ | Within d m}) ⟨_, logUpper m⟩,
    fun _ hd => csInf_le (OrderBot.bddBelow _) hd⟩

/-- Explicit finite-sample form of d(m) = log₂(m) + O(log log m). The optimum
ranges over all ordered messages with repetitions and a decoder at the size bound.
The upper construction uses no side information. -/
theorem logarithmicSize (m : ℕ) (hm : 2 ≤ m) :
    optimalSize m ≤ m.log2 ∧ m.log2 ≤ optimalSize m + 2*(m.log2.log2+1) := by
  let T := m.log2
  let k := T.log2+1
  let t := T-k
  let d := optimalSize m
  have hT : 1 ≤ T := (Nat.le_log2 (by omega : m ≠ 0)).mpr hm
  have up := (optimal_spec m).2 _ (logUpper m)
  rw [show max 1 m.log2 = T from Nat.max_eq_right hT] at up
  refine ⟨up, ?_⟩
  change T ≤ d+2*k
  have hk : 1 ≤ k := Nat.succ_pos _
  by_cases hsmall : t < 2
  · dsimp [t] at hsmall; omega
  have tbound : t ≤ T := Nat.sub_le .. 
  have tsize : t+k = T := Nat.sub_add_cancel (by dsimp [t] at hsmall; omega)
  have ht : 2 ≤ t := by omega
  have fit : 2^t*t-t ≤ m := by
    calc
      _ ≤ 2^t*t := Nat.sub_le ..
      _ ≤ 2^t*2^k := Nat.mul_le_mul_left _ (tbound.trans Nat.lt_log2_self.le)
      _ = 2^T := by rw [← Nat.pow_add, tsize]
      _ ≤ m := Nat.log2_self_le (by omega)
  by_cases td : t ≤ d
  · omega
  obtain ⟨D, works⟩ := (optimal_spec m).1
  have hwidth : width (t-2) = t := by dsimp [width];omega
  have low := counting_necessary (t-2) d 1 D (by rw [hwidth]; exact works _ fit)
  rw [hwidth, Nat.one_mul] at low
  have htk : t ≤ 2^k := tbound.trans Nat.lt_log2_self.le
  have hd1 : d+1 ≤ t := by omega
  have bits : (d+1)*(2^t*t)^d ≤ 2^(k+(t+k)*d) := by
    rw [Nat.pow_add 2 k _, Nat.pow_mul 2 (t+k) d, Nat.pow_add 2 t k]
    exact Nat.mul_le_mul (hd1.trans htk) (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ htk) _)
  have hlog := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (low.trans bits)
  have ar : t*t ≤ t*(d+k) := by
    have hprod := Nat.mul_le_mul_left k hd1
    nlinarith
  have t_le := Nat.le_of_mul_le_mul_left ar (by omega : 0 < t)
  omega

end EMX

namespace EMX

open Set MeasureTheory
open scoped ENNReal Classical

def budget (s : ℕ) := slots s * (s+1)^3

def stage (m : ℕ) := Nat.findGreatest (fun s => budget s ≤ m) m

noncomputable def learner : Learner := fun m xs => stageLearner (stage m) m xs

theorem learnable : Learnable := by
  refine ⟨learner, ?_⟩
  intro ε δ hε hδ
  obtain ⟨s₀, hs₀⟩ := exists_nat_gt (max (3/ε) (1/δ))
  have herr : 3 < ε * (s₀+1:ℝ) := by
    have hs := (le_max_left (3/ε) (1/δ)).trans_lt hs₀
    have := (div_lt_iff₀ hε).mp hs
    linarith
  have hconf : 1 < δ * (s₀+1:ℝ) := by
    have hs := (le_max_right (3/ε) (1/δ)).trans_lt hs₀
    have := (div_lt_iff₀ hδ).mp hs
    linarith
  refine ⟨max (budget s₀) (s₀+1), ?_⟩
  intro m hm μ hμ
  let _ := hμ
  let s := stage m
  have base : budget s₀ ≤ m := (le_max_left ..).trans hm
  have sb : s₀+1 ≤ m := (le_max_right ..).trans hm
  have sm : 0 < m := by omega
  have hs : s₀ ≤ s := Nat.le_findGreatest (P := fun j => budget j ≤ m) (by omega) base
  have budgetLe : budget s ≤ m := Nat.findGreatest_spec (P := fun j => budget j ≤ m) (by omega) base
  have hsub : (s₀ : ℝ) ≤ s := by exact_mod_cast hs
  have hden : 0 < (s : ℝ)+1 := by positivity
  have herror : (3 : ℝ)/(s+1) ≤ ε := (div_le_iff₀ hden).mpr
    (herr.le.trans (mul_le_mul_of_nonneg_left (by linarith) hε.le))
  have hconfidence : (1 : ℝ)/(s+1) ≤ δ := (div_le_iff₀ hden).mpr
    (hconf.le.trans (mul_le_mul_of_nonneg_left (by linarith) hδ.le))
  have hr : (slots s : ℝ)*((s:ℝ)+1)^3 ≤ m := by exact_mod_cast budgetLe
  have hcalc : (slots s : ℝ)/((m:ℝ)*(1/(s+1:ℝ))^2) ≤ 1/(s+1:ℝ) := by
    have hm' : (0:ℝ)<m := by exact_mod_cast sm
    field_simp
    nlinarith [hr]
  calc
    _ ≤ Measure.pi (fun _ : Fin m => μ) (deficitEvent (stageLearner s) μ m (3/(s+1:ℝ))) := by
      apply measure_mono
      rintro xs ⟨h, hh⟩
      exact ⟨h,(add_le_add le_rfl herror).trans_lt hh⟩
    _ ≤ _ := stage_bound s μ sm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hcalc.trans hconfidence)

/-- The paper’s proper EMX versus bounded monotone compression separation.
The points and hypotheses are countable, each support is finite, one learner
works for all IID laws, and each bounded decoder fails even at one fixed length. -/
theorem separation : Countable Point ∧ Countable Hyp ∧ Learnable ∧
    ∀ d a : ℕ, ∃ m : ℕ, ∀ D : Fin a → Message Point d → Hyp, ¬Reconstructs d a m D :=
  ⟨inferInstance, inferInstance, learnable, noBoundedCompression⟩

end EMX
