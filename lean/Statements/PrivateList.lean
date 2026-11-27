module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace PrivateList

abbrev Point := ℕ × ℕ
abbrev Label (k : ℕ) := Fin (k+1)
abbrev Hyp (k : ℕ) := Point → Label k

def SW (x y : Point) : Prop := x.1 < y.1 ∧ x.2 < y.2

def opposed (x y : Point) : Prop := x.1 < y.1 ∧ y.2 < x.2

/-- Different positive colors occupy strictly southwest-to-northeast blocks.
Inside a block the two orders agree, except in color two, where they are reversed. -/
def Valid {k} (h : Hyp k) : Prop :=
  {x | h x ≠ 0}.Finite ∧
  (∀ x y, h x ≠ 0 → h x < h y → SW x y) ∧
  ∀ x y, x ≠ y → h x ≠ 0 → h x = h y →
    if (h x).val = 2 then opposed x y ∨ opposed y x else SW x y ∨ SW y x

/-- All outgoing labels occur at every node because the class has k+1 labels. -/
def LittlestoneDepth (k n : ℕ) : Prop :=
  ∃ T : List (Label k) → Point, ∀ path : Fin n → Label k, ∃ h : Hyp k,
    Valid h ∧ ∀ i : Fin n, h (T ((List.ofFn path).take i.val)) = path i

/-- The permutation gives the witness order of the k+1 distinct labels. -/
def MonotoneLength (k n : ℕ) : Prop :=
  ∃ x : Fin n → Point, Function.Injective x ∧ ∃ π : Equiv.Perm (Label k),
    ∀ f : Fin n → Label k, Monotone f → ∃ h : Hyp k, Valid h ∧ ∀ i, h (x i) = π (f i)

end PrivateList

namespace PrivateList

open scoped Classical

def spike {k} (x : Point) (y : Label k) : Hyp k :=
  fun z => if z = x then y else 0

theorem spike_valid {k} (x : Point) (y : Label k) : Valid (spike x y) := by
  have loc {z} (hz : spike x y z ≠ 0) : z = x := by
    by_contra h
    exact hz (by simp [spike,h])
  refine ⟨(Set.finite_singleton x).subset (fun _ h => loc h), ?_, ?_⟩
  · intro z w nz lt
    have nw : spike x y w ≠ 0 := by
      intro hf
      rw [hf] at lt
      exact (Nat.not_lt_zero _ lt)
    have eq := (loc nz).trans (loc nw).symm
    rw [eq] at lt; exact (lt_irrefl _ lt).elim
  · intro z w ne nz eq
    exact (ne ((loc nz).trans (loc (eq ▸ nz)).symm)).elim

def first {k} (hk : 2 ≤ k) : Label k := ⟨1, by omega⟩
def second {k} (hk : 2 ≤ k) : Label k := ⟨2, by omega⟩

/-- After the first mistaken prediction of a list excluding 2, omit 2 strictly
southwest of its point and omit 1 at all other points. -/
noncomputable def omittedAfter {k} (hk : 2 ≤ k) (z x : Point) : Label k :=
  if SW x z then second hk else first hk

theorem safe_after {k} (hk : 2 ≤ k) {h : Hyp k} (hv : Valid h) {z}
    (hz : h z = second hk) (x : Point) : h x ≠ omittedAfter hk z x := by
  classical
  unfold omittedAfter
  by_cases sw : SW x z
  · rw [ite_eq_left sw]
    intro hx
    have nx : x ≠ z := by rintro rfl; exact (Nat.lt_irrefl _ sw.1)
    have comp := hv.2.2 x z nx (by simp [hx,second,Fin.ext_iff]) (hx.trans hz.symm)
    simp only [hx,second,ite_true] at comp
    obtain ⟨h1,h2⟩ := sw
    rcases comp with ⟨_,h⟩ | ⟨h,_⟩ <;> omega
  · rw [ite_eq_right sw]
    intro hx
    exact sw (hv.2.1 x z (by simp [hx,first,Fin.ext_iff]) (by rw [hx,hz]; exact Nat.lt_succ_self 1))

theorem littlestone_upper {k} (hk : 2 ≤ k) (n : ℕ) : ¬LittlestoneDepth k (n+2) := by
  classical
  rintro ⟨T, ht⟩
  let z := T []
  let v := T [second hk]
  let path : Fin (n+2) → Label k := Fin.cases (second hk) (fun _ => omittedAfter hk z v)
  obtain ⟨h,hv,ans⟩ := ht path
  have root : h z = second hk := by simpa [z,path] using ans 0
  have child : h v = omittedAfter hk z v := by
    have h1 := ans (Fin.succ (0 : Fin (n+1)))
    rw [show path (Fin.succ (0 : Fin (n+1))) = omittedAfter hk z v from rfl] at h1
    simpa [v,path,List.ofFn_succ] using h1
  exact safe_after hk hv root v child

theorem monotone_upper {k} (hk : 2 ≤ k) (n : ℕ) : ¬MonotoneLength k (n+2) := by
  classical
  rintro ⟨x, hi, π, hπ⟩
  let i : Fin (n+2) := 0
  let j : Fin (n+2) := (0 : Fin (n+1)).succ
  have ne : x i ≠ x j := fun he => (by decide : 0 ≠ 1) (congrArg Fin.val (hi he))
  have constant (v : Label k) : ∃ h : Hyp k, Valid h ∧ ∀ i, h (x i) = v := by
    obtain ⟨h, hv, h'⟩ := hπ (fun _ => π.symm v) monotone_const
    exact ⟨h,hv,by simpa using h'⟩
  obtain ⟨a,ha,fa⟩ := constant (first hk)
  obtain ⟨b,hb,fb⟩ := constant (second hk)
  have s := ha.2.2 _ _ ne (by simp [fa,first,Fin.ext_iff]) ((fa i).trans (fa j).symm)
  have o := hb.2.2 _ _ ne (by simp [fb,second,Fin.ext_iff]) ((fb i).trans (fb j).symm)
  simp [fa,first] at s
  simp [fb,second] at o
  rcases s with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases o with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;> omega

/-- Both list dimensions on the finite-support planar class are exactly one. -/
theorem dimensionOne (k : ℕ) (hk : 2 ≤ k) : ∀ n : ℕ,
    (LittlestoneDepth k n ↔ n ≤ 1) ∧ (MonotoneLength k n ↔ n ≤ 1) := by
  intro n
  have small {n} (hn : n ≤ 1) : LittlestoneDepth k n ∧ MonotoneLength k n := by
    let x : Point := (0,0)
    have doFit (f : Fin n → Label k) : ∃ h : Hyp k, Valid h ∧ ∀ i, h x = f i := by
      cases n with
      | zero => exact ⟨spike x 0,spike_valid _ _,fun i => i.elim0⟩
      | succ a =>
        have h0 : a = 0 := by omega
        subst a
        exact ⟨spike x (f 0), spike_valid _ _, fun i => by have hi : i = 0 := Fin.ext (by omega); simp [spike,hi]⟩
    constructor
    · exact ⟨fun _ => x,fun f => doFit f⟩
    · refine ⟨fun _ => x, fun i j _ => Fin.ext (by omega), Equiv.refl _,fun f _ => doFit f⟩
  by_cases hn : n ≤ 1
  · exact ⟨iff_of_true (small hn).1 hn,iff_of_true (small hn).2 hn⟩
  · obtain ⟨q,rfl⟩ : ∃ q, n = q+2 := ⟨n-2,by omega⟩
    exact ⟨iff_of_false (littlestone_upper hk q) hn,iff_of_false (monotone_upper hk q) hn⟩

end PrivateList

namespace PrivateList

noncomputable def dot {X : Type} [Fintype X] (weight v u : X → ℝ) : ℝ :=
  ∑ x, weight x * v x * u x

noncomputable def potential {X : Type} [Fintype X] (weight V w : X → ℝ) (l : ℝ) : ℝ :=
  ∑ x, weight x * (V x - l*w x)^2

theorem potential_step {X : Type} [Fintype X] (weight V w u : X → ℝ) (l : ℝ) :
    potential weight (fun x => V x + u x) w l =
      potential weight V w l + 2*dot weight V u - 2*l*dot weight w u + dot weight u u := by
  unfold potential dot
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem dot_neg {X : Type} [Fintype X] (weight v u : X → ℝ) :
    dot weight v (fun x => -u x) = -dot weight v u := by simp [dot]

theorem dot_neg_self {X : Type} [Fintype X] (weight u : X → ℝ) :
    dot weight (fun x => -u x) (fun x => -u x) = dot weight u u := by simp [dot]

/-- A threshold of height N in a margin representation forces at least d
perceptron mistakes when the binary search interval has 2^(d+1)-1 candidates. -/
theorem thresholdPerceptron {X : Type} [Fintype X] {N : ℕ} (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (u w : Fin N → X → ℝ) {a D : ℝ} (ha : 0 < a)
    (hu : ∀ i, dot p (u i) (u i) ≤ 2) (hw : ∀ i, dot p (w i) (w i) ≤ D)
    (lo : ∀ i j, j < i → dot p (w i) (u j) ≤ -a)
    (hi : ∀ i j, i < j → a ≤ dot p (w i) (u j))
    (d : ℕ) (hn : 2^(d+1)-1 ≤ N) : (d:ℝ)*a^2 ≤ 2*D := by
  let l := 2/a
  have hl : 0 < l := div_pos (by norm_num) ha
  have hla : l*a = 2 := div_mul_cancel₀ 2 ha.ne'
  have recur (n : ℕ) (s : ℕ) (hN : s + (2^(n+1)-1) ≤ N) (V : X → ℝ) :
      ∃ i : Fin N, s ≤ i.val ∧ i.val < s+(2^(n+1)-1) ∧
        2*(n:ℝ) ≤ potential p V (w i) l := by
    induction n generalizing s V with
    | zero =>
      refine ⟨⟨s,by simp at hN; omega⟩,le_rfl,by simp, ?_⟩
      simp only [Nat.cast_zero,mul_zero,potential]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (sq_nonneg _))
    | succ n ih =>
      let L := 2^(n+1)-1
      have pos : 0 < 2^(n+1) := Nat.two_pow_pos _
      have double : 2^(n+1+1)-1 = L+1+L := by
        rw [Nat.pow_succ]; dsimp [L];omega
      rw [double] at hN ⊢
      let j : Fin N := ⟨s+L,by omega⟩
      have advance (new : X → ℝ) (i : Fin N) (score : dot p V new ≤ 0)
          (margin : a ≤ dot p (w i) new) (cost : dot p new new ≤ 2) :
          potential p (fun x => V x + new x) (w i) l + 2 ≤ potential p V (w i) l := by
        rw [potential_step]
        have := mul_le_mul_of_nonneg_left margin hl.le
        linarith
      by_cases sign : dot p V (u j) ≤ 0
      · obtain ⟨i,lower,upper,deep⟩ := ih s (by change s+L ≤ _; omega) (fun x => V x + u j x)
        have lt : i < j := upper
        have step := advance (u j) i sign (hi i j lt) (hu j)
        refine ⟨i,lower,by change _ < s+L at upper; omega, ?_⟩
        push_cast; linarith
      · obtain ⟨i,lower,upper,deep⟩ := ih (s+L+1)
          (by change s+L+1+L ≤ _; omega) (fun x => V x + -u j x)
        have lt : j < i := by change j.val < i.val; dsimp [j];omega
        have negscore : dot p V (fun x => -u j x) ≤ 0 := by rw [dot_neg]; linarith
        have margin : a ≤ dot p (w i) (fun x => -u j x) := by rw [dot_neg]; linarith [lo i j lt]
        have step := advance (fun x => -u j x) i negscore margin ((dot_neg_self p _).le.trans (hu j))
        refine ⟨i,by omega,by change _ < s+L+1+L at upper;omega, ?_⟩
        push_cast; linarith
  obtain ⟨i,_,_,bound⟩ := recur d 0 (by simpa using hn) (fun _ => 0)
  have zero : potential p (fun _ => 0) (w i) l = l^2 * dot p (w i) (w i) := by
    unfold dot potential
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; ring
  rw [zero] at bound
  have est := bound.trans (mul_le_mul_of_nonneg_left (hw i) (sq_nonneg l))
  dsimp [l] at est
  field_simp at est
  nlinarith

end PrivateList

namespace PrivateList

open scoped Classical

noncomputable def mass {X : Type} (p : X → ℝ) (E : Finset X) : ℝ := ∑ x ∈ E, p x

def Law {X : Type} [Fintype X] (p : X → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

def Domination {X : Type} (scale δ : ℝ) (p q : X → ℝ) : Prop :=
  ∀ E : Finset X, mass q E ≤ scale * mass p E + δ

theorem mass_le_one {X : Type} [Fintype X] {p : X → ℝ} (hp : Law p) (E : Finset X) :
    mass p E ≤ 1 := by
  rw [← hp.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hp.1 x)

noncomputable def clip {X : Type} (scale : ℝ) (p q : X → ℝ) (x : X) : ℝ := min (q x) (scale*p x)

theorem clip_event {X : Type} [Fintype X] {p q : X → ℝ} {scale δ : ℝ}
    (priv : Domination scale δ p q) (E : Finset X) :
    mass q E - δ ≤ mass (clip scale p q) E ∧ mass (clip scale p q) E ≤ mass q E := by
  classical
  let cut := Finset.univ.filter fun x => scale*p x < q x
  have excess : ∑ x, (q x - clip scale p q x) = mass q cut - scale * mass p cut := by
    unfold mass
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    unfold clip
    by_cases h : scale*p x < q x
    · simp [h,min_eq_right h.le]
    · simp [h,min_eq_left (le_of_not_gt h)]
  have e := priv cut
  have small : ∑ x ∈ E, (q x - clip scale p q x) ≤ ∑ x, (q x - clip scale p q x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sub_nonneg.mpr (min_le_left ..))
  refine ⟨?_,Finset.sum_le_sum (fun _ _ => min_le_left ..)⟩
  rw [Finset.sum_sub_distrib, excess] at small
  unfold mass at *
  linarith

noncomputable def density {X : Type} (scale : ℝ) (p q : X → ℝ) (x : X) : ℝ := clip scale p q x / p x

theorem density_props {X : Type} [Fintype X] {p q : X → ℝ} (hp : Law p) (hq : Law q)
    {scale : ℝ} (hscale : 0 ≤ scale) (x : X) :
    p x * density scale p q x = clip scale p q x ∧ 0 ≤ density scale p q x ∧ density scale p q x ≤ scale := by
  have cn : 0 ≤ clip scale p q x := le_min (hq.1 x) (mul_nonneg hscale (hp.1 x))
  have hi : clip scale p q x ≤ scale*p x := min_le_right .. 
  unfold density
  by_cases h : p x = 0
  · rw [h,mul_zero] at hi
    simp [h, hi.antisymm cn, hscale]
  · have pos := lt_of_le_of_ne (hp.1 x) (Ne.symm h)
    exact ⟨by field_simp, div_nonneg cn pos.le, (div_le_iff₀ pos).mpr hi⟩

theorem density_norm {X : Type} [Fintype X] {p q : X → ℝ} (hp : Law p) (hq : Law q)
    {scale : ℝ} (hscale : 0 ≤ scale) : dot p (density scale p q) (density scale p q) ≤ scale := by
  calc
    _ ≤ ∑ x, scale*q x := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨he,hn,hu⟩ := density_props hp hq hscale x
      rw [he]
      have cn : 0 ≤ clip scale p q x := le_min (hq.1 x) (mul_nonneg hscale (hp.1 x))
      calc
        _ ≤ clip scale p q x * scale := mul_le_mul_of_nonneg_left hu cn
        _ ≤ q x * scale := mul_le_mul_of_nonneg_right (min_le_left ..) hscale
        _ = _ := mul_comm .. 
    _ = _ := by rw [← Finset.mul_sum,hq.2,mul_one]

end PrivateList

namespace PrivateList

open scoped Classical

noncomputable def query {X : Type} (E : Finset X) : Option X → ℝ
  | none => 1
  | some x => if x ∈ E then 1 else 0

noncomputable def weighted {X : Type} (p : X → ℝ) : Option X → ℝ
  | none => 1
  | some x => p x

noncomputable def rowVector {X : Type} (b : ℝ) (g : X → ℝ) : Option X → ℝ
  | none => b
  | some x => g x

theorem dot_query {X : Type} [Fintype X] (p g : X → ℝ) (b : ℝ) (E : Finset X) :
    dot (weighted p) (rowVector b g) (query E) = b + mass (fun x => p x * g x) E := by
  classical
  rw [dot, Fintype.sum_option]
  simp only [weighted,rowVector,query,one_mul,mul_one]
  congr 1
  simp [mass, mul_ite]

theorem square_query {X : Type} [Fintype X] (p : X → ℝ) (E : Finset X) :
    dot (weighted p) (query E) (query E) = 1 + mass p E := by
  classical
  rw [dot, Fintype.sum_option]
  simp only [weighted,query,mul_one]
  congr 1
  simp [mass, mul_ite]

theorem square_row {X : Type} [Fintype X] (p g : X → ℝ) (b : ℝ) :
    dot (weighted p) (rowVector b g) (rowVector b g) = b*b + dot p g g := by
  rw [dot,Fintype.sum_option]
  simp only [weighted,rowVector,one_mul]
  rfl

/-- A finite collection of events inducing a staggered threshold pattern must be
short when the additive privacy loss is strictly less than twice the margin.
Only one-sided domination by one common reference law is needed. -/
theorem finitePacking {X : Type} [Fintype X] {N : ℕ} (p : X → ℝ) (hp : Law p)
    (P : Fin N → X → ℝ) (law : ∀ i, Law (P i)) (E : Fin N → Finset X)
    {scale δ γ c : ℝ} (hscale : 0 ≤ scale) (hδ : 0 ≤ δ) (hδγ : δ < 2*γ)
    (hc : γ ≤ c) (hc' : c ≤ 1-γ)
    (dp : ∀ i, Domination scale δ p (P i))
    (below : ∀ i j, j < i → mass (P i) (E j) ≤ c-γ)
    (above : ∀ i j, i < j → c+γ ≤ mass (P i) (E j))
    (d : ℕ) (hn : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 2*(scale+1) := by
  let b := -c+δ/2
  let g i := density scale p (P i)
  have sqb : b*b ≤ 1 := by
    have hb : -1 ≤ b := by dsimp [b]; linarith
    have hb' : b ≤ 1 := by dsimp [b]; linarith
    nlinarith [mul_nonneg (show 0 ≤ 1+b by linarith) (show 0 ≤ 1-b by linarith)]
  have eval (i j) : dot (weighted p) (rowVector b (g i)) (query (E j)) =
      b + mass (clip scale p (P i)) (E j) := by
    rw [dot_query]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    exact (density_props hp (law i) hscale x).1
  apply thresholdPerceptron (weighted p) (by rintro (_|x) ; exacts [zero_le_one,hp.1 x])
    (fun j => query (E j)) (fun i => rowVector b (g i)) (a := γ-δ/2) (D := scale+1)
    (by linarith) _ _ _ _ d hn
  · intro j; rw [square_query]; linarith [mass_le_one hp (E j)]
  · intro i; rw [square_row]; linarith [density_norm hp (law i) hscale]
  · intro i j hj; rw [eval]; dsimp [b]
    linarith [(clip_event (dp i) (E j)).2, below i j hj]
  · intro i j hj; rw [eval]; dsimp [b]
    linarith [(clip_event (dp i) (E j)).1, above i j hj]

end PrivateList

namespace PrivateList

open MeasureTheory Set
open scoped Classical

def MeasureDominates {Ω : Type} [MeasurableSpace Ω] (scale δ : ℝ) (μ ν : Measure Ω) : Prop :=
  ∀ E : Set Ω, MeasurableSet E → ν.real E ≤ scale * μ.real E + δ

/-- Sharp-margin packing inequality on arbitrary measurable prediction spaces.
The finite quotient is the joint vector of answers to all N membership tests. -/
theorem measurePacking {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Fin N → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (E : Fin N → Set Ω) (me : ∀ j, MeasurableSet (E j))
    {scale δ γ c : ℝ} (hscale : 0 ≤ scale) (hδ : 0 ≤ δ) (hδγ : δ < 2*γ)
    (hc : γ ≤ c) (hc' : c ≤ 1-γ) (dp : ∀ i, MeasureDominates scale δ μ (P i))
    (below : ∀ i j, j < i → (P i).real (E j) ≤ c-γ)
    (above : ∀ i j, i < j → c+γ ≤ (P i).real (E j))
    (d : ℕ) (hn : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 2*(scale+1) := by
  classical
  let f (ω : Ω) (i : Fin N) : Bool := if ω ∈ E i then true else false
  have hf : Measurable f := Measurable.of_eval (fun i =>
    Measurable.ite (me i) measurable_const measurable_const)
  let atom (Q : Measure Ω) (a : Fin N → Bool) := Q.real (f ⁻¹' {a})
  have ma (Q : Measure Ω) [IsProbabilityMeasure Q] (s : Finset (Fin N → Bool)) :
      mass (atom Q) s = Q.real (f ⁻¹' (s : Set _)) :=
    sum_measureReal_preimage_singleton _ (fun a _ => hf (measurableSet_singleton a))
  have law (Q : Measure Ω) [IsProbabilityMeasure Q] : Law (atom Q) :=
    ⟨fun _ => measureReal_nonneg, by simpa [mass] using ma Q Finset.univ⟩
  let event (j : Fin N) := Finset.univ.filter fun a : Fin N → Bool => a j = true
  have ef (j) : f ⁻¹' (event j : Set _) = E j := by ext x; simp [event,f]
  apply finitePacking (atom μ) (law μ) (fun i => atom (P i)) (fun i => law (P i))
    event hscale hδ hδγ hc hc' _ _ _ d hn
  · intro i s
    rw [ma,ma]
    exact dp i _ (hf s.finite_toSet.measurableSet)
  · intro i j lt; rw [ma, ef]; exact below i j lt
  · intro i j lt; rw [ma, ef]; exact above i j lt

/-- At the endpoint δ=2γ, arbitrarily many distributions satisfy the threshold
constraints even with multiplicative privacy factor one. -/
theorem packingSharp (N : ℕ) {γ c : ℝ} (hγ : 0 ≤ γ) (hc : γ ≤ c) (hc' : c ≤ 1-γ) :
    ∃ P : Fin N → Option (Option (Fin N)) → ℝ, (∀ i, Law (P i)) ∧
      (∀ i j, Domination 1 (2*γ) (P i) (P j)) ∧
      ∃ E : Fin N → Finset (Option (Option (Fin N))),
        (∀ i j, j < i → mass (P i) (E j) = c-γ) ∧
        (∀ i j, i < j → mass (P i) (E j) = c+γ) := by
  classical
  let X := Option (Option (Fin N))
  let base : X → ℝ
    | none => c-γ
    | some none => 1-c-γ
    | some (some _) => 0
  let atom (i : Fin N) : X := some (some i)
  let P (i : Fin N) (x : X) := base x + if x = atom i then 2*γ else 0
  have bn (x) : 0 ≤ base x := by rcases x with _|(_|i) <;> dsimp [base] <;> linarith
  have total : (∑ x, base x) = 1-2*γ := by
    rw [Fintype.sum_option,Fintype.sum_option]; simp [base];ring
  have calcMass (i : Fin N) (s : Finset X) :
      mass (P i) s = mass base s + if atom i ∈ s then 2*γ else 0 := by
    unfold mass
    simp only [P,Finset.sum_add_distrib]
    exact congrArg (fun z => _ + z) (Finset.sum_ite_eq' _ _ _)
  have law (i) : Law (P i) := by
    constructor
    · intro x; unfold P; split <;> linarith [bn x]
    · rw [show (∑ x,P i x) = mass (P i) Finset.univ from rfl, calcMass, mass, total]
      simp
  let accept (j : Fin N) : X → Prop
    | none => True
    | some none => False
    | some (some i) => i < j
  let E (j) := Finset.univ.filter (accept j)
  have eb (j) : mass base (E j) = c-γ := by
    rw [mass,Finset.sum_filter,Fintype.sum_option,Fintype.sum_option]
    simp [base,accept]
  have pat (i j) : mass (P i) (E j) = c-γ + if i<j then 2*γ else 0 := by
    rw [calcMass,eb]
    simp [atom,E,accept]
  refine ⟨P,law,?_,E,?_,?_⟩
  · intro i j s
    simp only [calcMass,one_mul]
    split <;> split <;> linarith
  · intro i j h; simp [pat,not_lt.mpr h.le]
  · intro i j h; rw [pat,ite_eq_left h]; ring

end PrivateList

namespace PrivateList

open MeasureTheory Set
open scoped Classical

abbrev Sample (k m : ℕ) := Fin m → Point × Label k

def Consistent {k m} (s : Sample k m) : Prop :=
  ∃ h : Hyp k, Valid h ∧ ∀ i, h (s i).1 = (s i).2

def Neighbors {X : Type} {m} (s t : Fin m → X) : Prop :=
  ∃ i : Fin m, ∀ j, j ≠ i → s j = t j

/-- The output space may contain arbitrary improper list-valued predictors.
All probability bounds below use only measurable omission events. -/
structure Rule (k m : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  law : Sample k m → Measure Ω
  normalized : ∀ s, IsProbabilityMeasure (law s)
  predict : Ω → Point → Finset (Label k)
  listSize : ∀ ω x, (predict ω x).card ≤ k
  measurable : ∀ x y, MeasurableSet {ω | y ∉ predict ω x}

def Private {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (scale δ : ℝ) : Prop :=
  ∀ s t, Neighbors s t → MeasureDominates scale δ (A.law s) (A.law t)

noncomputable def omission {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (s : Sample k m)
    (x : Point) (y : Label k) : ℝ := (A.law s).real {ω | y ∉ A.predict ω x}

structure Template (k m : ℕ) where
  xRank : Equiv.Perm (Fin m)
  yRank : Equiv.Perm (Fin m)
  label : Fin m → Label k

def place {k m} (T : Template k m) (a b : Fin m → ℕ) : Sample k m :=
  fun i => ((a (T.xRank i),b (T.yRank i)),T.label i)

abbrev Cell (m : ℕ) := Fin (m+1) × Fin (m+1)

noncomputable def lookup {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (T : Template k m)
    (a b : Fin (m+1) → ℕ) (v : Cell m) (y : Label k) : ℝ :=
  omission A (place T (fun i => a (v.1.succAbove i)) (fun i => b (v.2.succAbove i)))
    (a v.1,b v.2) y

end PrivateList

namespace PrivateList

open Filter Set
open scoped Classical

/-- Take the value attained on an ultrafilter-large fiber of a finite coloring. -/
theorem majority_exists {C : Type} [Finite C] (f : ℕ → C) :
    ∃ c, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = c := by
  have h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ c ∈ (univ : Set C), f n = c :=
    .of_forall (fun n => ⟨_,mem_univ _,rfl⟩)
  obtain ⟨c,_,hc⟩ := (Ultrafilter.eventually_exists_mem_iff finite_univ).mp h
  exact ⟨c,hc⟩

noncomputable def preference {C : Type} [Finite C] (color : Finset ℕ → C) :
    ℕ → Finset ℕ → C
  | 0, p => color p
  | k+1, p => (majority_exists (fun x => preference color k (insert x p))).choose

theorem homogeneous {C : Type} [Finite C] (color : Finset ℕ → C) (k L : ℕ) :
    ∃ S : Finset ℕ, S.card = L ∧ ∀ T ⊆ S, T.card = k → color T = preference color k ∅ := by
  classical
  let c := preference color k ∅
  have build (n : ℕ) : ∃ S : Finset ℕ, S.card = n ∧
      ∀ T ⊆ S, T.card ≤ k → preference color (k-T.card) T = c := by
    induction n with
    | zero => exact ⟨∅,rfl,fun T hT _ => by simp [Finset.subset_empty.mp hT,c]⟩
    | succ n ih =>
      obtain ⟨S,hS,good⟩ := ih
      have all : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), ∀ T ∈ S.powerset,
          T.card < k → preference color (k-T.card-1) (insert x T) = preference color (k-T.card) T := by
        apply (Filter.eventually_all_finset _).mpr
        intro T _
        by_cases h : T.card < k
        · have hk : k-T.card = (k-T.card-1)+1 := by omega
          have y := (majority_exists (fun x => preference color (k-T.card-1) (insert x T))).choose_spec
          filter_upwards [y] with x hx h'
          conv_rhs => rw [hk]
          exact hx
        · exact .of_forall (fun _ h' => (h h').elim)
      have fresh : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), x ∉ S :=
        S.finite_toSet.compl_mem_hyperfilter
      obtain ⟨x,hx,keep⟩ := (fresh.and all).exists
      refine ⟨insert x S, by simp [hx,hS], ?_⟩
      intro T sub size
      by_cases hxt : x ∈ T
      · let U := T.erase x
        have subU : U ⊆ S := by
          intro a ha
          exact (Finset.mem_insert.mp (sub (Finset.mem_erase.mp ha).2)).resolve_left (Finset.mem_erase.mp ha).1
        have hU : U.card+1 = T.card := Finset.card_erase_add_one hxt
        have hk : U.card < k := by omega
        have eq := keep U (Finset.mem_powerset.mpr subU) hk
        rw [show insert x U = T from Finset.insert_erase hxt] at eq
        rw [show k-T.card = k-U.card-1 by omega]
        exact eq.trans (good U subU hk.le)
      · apply good T _ size
        intro a ha
        exact (Finset.mem_insert.mp (sub ha)).resolve_left (fun e => hxt (e ▸ ha))
  obtain ⟨S,hS,good⟩ := build L
  refine ⟨S,hS,fun T sub card => ?_⟩
  simpa [card,preference] using good T sub card.le

theorem preference_step {C : Type} [Finite C] (color : Finset ℕ → C) (k : ℕ) (T : Finset ℕ) :
    ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), preference color k (insert x T) = preference color (k+1) T :=
  (majority_exists (fun x => preference color k (insert x T))).choose_spec

theorem preference_map {C D : Type} [Finite C] [Finite D] (f : C → D)
    (color : Finset ℕ → C) (k : ℕ) (T : Finset ℕ) :
    preference (fun A => f (color A)) k T = f (preference color k T) := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x,ha,hb⟩ := ((preference_step (fun A => f (color A)) k T).and
      (preference_step color k T)).exists
    rw [← ha, ih, hb]

/-- A product Ramsey rectangle for two independently chosen ordered axes. -/
theorem rectangle {C : Type} [Finite C] (color : Finset ℕ → Finset ℕ → C) (k L : ℕ) :
    ∃ A B : Finset ℕ, A.card = L ∧ B.card = L ∧ ∃ c, ∀ S ⊆ A, S.card = k →
      ∀ T ⊆ B, T.card = k → color S T = c := by
  classical
  let rows S := preference (color S) k ∅
  obtain ⟨A,ha,hA⟩ := homogeneous rows k L
  let joint (T : Finset ℕ) (S : A.powerset) := color S T
  obtain ⟨B,hb,hB⟩ := homogeneous joint k L
  refine ⟨A,B,ha,hb,preference rows k ∅,?_⟩
  intro S subS cardS T subT cardT
  let I : A.powerset := ⟨S, Finset.mem_powerset.mpr subS⟩
  have h := congrFun (hB T subT cardT) I
  have ev := preference_map (fun f : A.powerset → C => f I) joint k ∅
  exact h.trans (ev.symm.trans (hA S subS cardS))

end PrivateList

namespace PrivateList

open Set MeasureTheory
open scoped Classical

noncomputable def bucket (D : ℕ) (x : ℝ) : Fin (D+1) :=
  ⟨min D ⌊D*x⌋₊,Nat.lt_succ_of_le (min_le_left ..)⟩

theorem bucket_accuracy {D : ℕ} (hD : 0 < D) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    |x - ((bucket D x).val : ℝ)/D| ≤ 1/D := by
  have pos : (0:ℝ) < D := by exact_mod_cast hD
  have lower : (⌊(D:ℝ)*x⌋₊ : ℝ) ≤ D*x := Nat.floor_le (mul_nonneg pos.le hx)
  have upper := Nat.lt_floor_add_one ((D:ℝ)*x)
  have cap : ⌊(D:ℝ)*x⌋₊ ≤ D := by
    exact_mod_cast lower.trans (by nlinarith : (D:ℝ)*x ≤ D)
  change |x - (min D ⌊(D:ℝ)*x⌋₊ : ℕ)/ (D:ℝ)| ≤ _
  rw [min_eq_right cap, abs_of_nonneg (by apply sub_nonneg.mpr; apply (div_le_iff₀ pos).mpr; linarith)]
  apply (le_div_iff₀ pos).mpr
  rw [sub_mul,div_mul_cancel₀ _ pos.ne']
  linarith

theorem order_image {l : ℕ} (g : Fin l ↪o ℕ) :
    let S := Finset.univ.image g
    ∃ h : S.card = l, S.orderEmbOfFin h = g := by
  let S := Finset.univ.image g
  have h : S.card = l := by simp [S,Finset.card_image_of_injective _ g.injective]
  refine ⟨h,?_⟩
  ext i
  exact congrFun (Finset.orderEmbOfFin_unique h (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i))
    g.strictMono).symm i

/-- Rank cells can be made simultaneously homogeneous to a prescribed mesh on
arbitrarily long independent axes. -/
theorem homogeneousRanks {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (T : Template k m)
    (L D : ℕ) (hD : 0 < D) :
    ∃ X Y : Fin L ↪o ℕ, ∃ v : Cell m → Label k → ℝ,
      (∀ i y, 0 ≤ v i y ∧ v i y ≤ 1) ∧
      ∀ a b : Fin (m+1) ↪o Fin L, ∀ i y,
        |lookup A T (fun n => X (a n)) (fun n => Y (b n)) i y - v i y| ≤ 1/D := by
  classical
  let color (S U : Finset ℕ) : Cell m → Label k → Fin (D+1) := fun i y =>
    if hS : S.card=m+1 then if hU : U.card=m+1 then
      bucket D (lookup A T (S.orderEmbOfFin hS) (U.orderEmbOfFin hU) i y) else 0 else 0
  obtain ⟨S,U,hS,hU,c,mono⟩ := rectangle color (m+1) L
  let X := S.orderEmbOfFin hS
  let Y := U.orderEmbOfFin hU
  have pos : (0:ℝ) < D := by exact_mod_cast hD
  refine ⟨X,Y,fun i y => ((c i y).val : ℝ)/D,?_,?_⟩
  · intro i y
    exact ⟨div_nonneg (Nat.cast_nonneg _) pos.le, (div_le_one pos).mpr (by exact_mod_cast Nat.le_of_lt_succ (c i y).isLt)⟩
  intro a b i y
  let f := a.trans X
  let g := b.trans Y
  let R := Finset.univ.image f
  let V := Finset.univ.image g
  have rs : R ⊆ S := by rintro _ h; obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h; exact S.orderEmbOfFin_mem hS _
  have vs : V ⊆ U := by rintro _ h; obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h; exact U.orderEmbOfFin_mem hU _
  obtain ⟨fr,ef⟩ := order_image f
  obtain ⟨gr,eg⟩ := order_image g
  change R.card = m+1 at fr
  change V.card = m+1 at gr
  change R.orderEmbOfFin fr = f at ef
  change V.orderEmbOfFin gr = g at eg
  have eq := congrFun (congrFun (mono R rs fr V vs gr) i) y
  simp only [color,dite_eq_left fr,dite_eq_left gr,ef,eg] at eq
  have law (s : Sample k m) := A.normalized s
  have pos' : 0 ≤ lookup A T f g i y := measureReal_nonneg
  have neg' : lookup A T f g i y ≤ 1 := by
    unfold lookup omission
    apply measureReal_le_one
  have est := bucket_accuracy hD pos' neg'
  rw [eq] at est
  exact est

end PrivateList

namespace PrivateList

open MeasureTheory
open scoped Classical

def AtRank {m L} (a : Fin m → Fin L) (r : Fin (m+1)) (z : Fin L) : Prop :=
  (∀ i, i.val < r.val → a i < z) ∧ (∀ i, r.val ≤ i.val → z < a i)

theorem insert_rank {m L} {a : Fin m → Fin L} (ha : StrictMono a) (r : Fin (m+1)) (z : Fin L)
    (atR : AtRank a r z) : ∃ e : Fin (m+1) ↪o Fin L, e r = z ∧ ∀ i, e (r.succAbove i) = a i := by
  let f : Fin (m+1) → Fin L := Fin.insertNth (α := fun _ => Fin L) r z a
  have increasing (i j : Fin (m+1)) : i < j → f i < f j := by
    revert j
    refine r.succAboveCases ?_ (fun u => ?_) i
    · intro j
      refine r.succAboveCases ?_ (fun v h => ?_) j
      · exact fun h => (lt_irrefl _ h).elim
      · simpa [f] using atR.2 v ((Fin.lt_succAbove_iff_le_castSucc r v).mp h)
    · intro j
      refine r.succAboveCases ?_ (fun v h => ?_) j
      · intro h
        simpa [f] using atR.1 u ((Fin.succAbove_lt_iff_castSucc_lt r u).mp h)
      · simpa [f] using ha (Fin.succAbove_lt_succAbove_iff.mp h)
  exact ⟨OrderEmbedding.ofStrictMono f (fun _ _ h => increasing _ _ h),
    Fin.insertNth_apply_same (α := fun _ => Fin L) r z a,
    fun i => Fin.insertNth_apply_succAbove (α := fun _ => Fin L) r z a i⟩

def HomogeneousOn {k m Ω L} [MeasurableSpace Ω] (A : Rule k m Ω) (T : Template k m)
    (X Y : Fin L ↪o ℕ) (v : Cell m → Label k → ℝ) (τ : ℝ) : Prop :=
  ∀ a b : Fin (m+1) ↪o Fin L, ∀ i y,
    |lookup A T (fun n => X (a n)) (fun n => Y (b n)) i y - v i y| ≤ τ

theorem local_rank {k m Ω L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ} (hom : HomogeneousOn A T X Y v τ)
    {a b : Fin m → Fin L} (ha : StrictMono a) (hb : StrictMono b) (r : Cell m) (x y : Fin L)
    (hx : AtRank a r.1 x) (hy : AtRank b r.2 y) (label : Label k) :
    |omission A (place T (X ∘ a) (Y ∘ b)) (X x,Y y) label - v r label| ≤ τ := by
  obtain ⟨u,ux,us⟩ := insert_rank ha r.1 x hx
  obtain ⟨w,wy,ws⟩ := insert_rank hb r.2 y hy
  simpa [lookup,ux,wy,us,ws,Function.comp_def] using hom u w r label

def spaced {m L} (room : 2*m+1 ≤ L) (i : Fin m) : Fin L := ⟨2*i.val+1, by omega⟩

def shifted {m L} (room : 2*m+1 ≤ L) (j i : Fin m) : Fin L :=
  ⟨if i=j then 2*i.val else 2*i.val+1, by split <;> omega⟩

theorem shifted_mono {m L} (room : 2*m+1 ≤ L) (j : Fin m) : StrictMono (shifted room j) := by
  intro a b hab
  change (if a=j then 2*a.val else 2*a.val+1) < if b=j then 2*b.val else 2*b.val+1
  have : a.val < b.val := hab
  split <;> split <;> omega

theorem shifted_rank {m L} (room : 2*m+1 ≤ L) (j : Fin m) :
    AtRank (shifted room j) j.succ (spaced room j) := by
  constructor
  · intro i hi
    change (if i=j then 2*i.val else 2*i.val+1) < 2*j.val+1
    change i.val < j.val+1 at hi
    split <;> rename_i h
    · subst i; omega
    · have : i.val ≠ j.val := fun e => h (Fin.ext e)
      omega
  · intro i hi
    change 2*j.val+1 < if i=j then 2*i.val else 2*i.val+1
    change j.val+1 ≤ i.val at hi
    split <;> omega

theorem shifted_neighbor {k m L} (T : Template k m) (room : 2*m+1 ≤ L)
    (X Y : Fin L ↪o ℕ) (i : Fin m) :
    Neighbors (place T (X ∘ spaced room) (Y ∘ spaced room))
      (place T (X ∘ shifted room (T.xRank i)) (Y ∘ shifted room (T.yRank i))) := by
  refine ⟨i,fun j h => ?_⟩
  have hx : T.xRank j ≠ T.xRank i := fun e => h (T.xRank.injective e)
  have hy : T.yRank j ≠ T.yRank i := fun e => h (T.yRank.injective e)
  simp [place,spaced,shifted,hx,hy]

theorem Neighbors.symm {X : Type} {m} {s t : Fin m → X} (h : Neighbors s t) : Neighbors t s := by
  obtain ⟨i,eq⟩ := h
  exact ⟨i,fun j h => (eq j h).symm⟩

/-- A single neighbouring replacement makes the old training point a fresh
query while preserving all within-axis sample orders. -/
theorem training_cells {k m Ω L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ δ} (hom : HomogeneousOn A T X Y v τ) (priv : Private A 2 δ)
    (room : 2*m+1 ≤ L) (i : Fin m) (lab : Label k) :
    let s := place T (X ∘ spaced room) (Y ∘ spaced room)
    let r : Cell m := ((T.xRank i).succ,(T.yRank i).succ)
    v r lab ≤ 2*omission A s (s i).1 lab + δ + τ ∧
      omission A s (s i).1 lab ≤ 2*(v r lab+τ)+δ := by
  let r : Cell m := ((T.xRank i).succ,(T.yRank i).succ)
  let s := place T (X ∘ spaced room) (Y ∘ spaced room)
  let s' := place T (X ∘ shifted room (T.xRank i)) (Y ∘ shifted room (T.yRank i))
  let z := (s i).1
  have neigh : Neighbors s s' := shifted_neighbor T room X Y i
  have close : |omission A s' z lab - v r lab| ≤ τ := local_rank hom
    (shifted_mono room _) (shifted_mono room _) r _ _ (shifted_rank ..) (shifted_rank ..) lab
  have one : omission A s' z lab ≤ 2*omission A s z lab + δ := priv s s' neigh _ (A.measurable z lab)
  have two : omission A s z lab ≤ 2*omission A s' z lab + δ := priv s' s neigh.symm _ (A.measurable z lab)
  obtain ⟨l,u⟩ := abs_le.mp close
  change v r lab ≤ 2*omission A s z lab+δ+τ ∧ omission A s z lab ≤ 2*(v r lab+τ)+δ
  constructor <;> linarith

end PrivateList

namespace PrivateList

open MeasureTheory Set
open scoped Classical

def Empirical {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (e : ℝ) : Prop :=
  ∀ s : Sample k m, Consistent s → (∑ i, omission A s (s i).1 (s i).2) ≤ m*e

theorem high_omission {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) (s : Sample k m) (x : Point) :
    ∃ y : Label k, 1/(k+1:ℝ) ≤ omission A s x y := by
  let μ := A.law s
  have prob : IsProbabilityMeasure μ := A.normalized s
  let E (y : Label k) := {w | y ∉ A.predict w x}
  have all : ⋃ y, E y = univ := by
    apply Set.eq_univ_of_forall
    intro w
    apply mem_iUnion.mpr
    by_contra! h
    have eq : A.predict w x = Finset.univ := Finset.eq_univ_of_forall (fun y => by
      by_contra hy; exact h y hy)
    have size := A.listSize w x
    simp [eq] at size
  have bound : 1 ≤ ∑ y, omission A s x y := by
    have := measureReal_iUnion_fintype_le (μ := μ) E
    rwa [all,probReal_univ] at this
  have total : (∑ _i : Label k, 1/(k+1:ℝ)) = 1 := by
    simp [ne_of_gt (show (0:ℝ)<k+1 by positivity)]
  obtain ⟨y,_,hy⟩ := Finset.exists_le_of_sum_le (f := fun _ : Label k => 1/(k+1:ℝ))
    (g := fun y => omission A s x y) Finset.univ_nonempty (total.le.trans bound)
  exact ⟨y,hy⟩

theorem low_omission {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) {s : Sample k m}
    (hm : 0 < m) (consistent : Consistent s) (y : Label k)
    (balanced : m ≤ 2*(k+1)*(Finset.univ.filter fun i => (s i).2 = y).card)
    (emp : Empirical A (1 / (200*(k+1:ℝ)^2))) :
    ∃ i, (s i).2 = y ∧ omission A s (s i).1 y ≤ 1/(100*(k+1:ℝ)) := by
  let I := Finset.univ.filter fun i => (s i).2 = y
  have proportion : (m:ℝ) ≤ 2*(k+1:ℝ)*I.card := by exact_mod_cast balanced
  have nn : 0 < I.card := by
    by_contra! hn
    have zero : I.card = 0 := by omega
    change m ≤ 2*(k+1)*I.card at balanced
    simp [zero] at balanced
    omega
  have restricted : (∑ i ∈ I, omission A s (s i).1 (s i).2) ≤ m*(1/(200*(k+1:ℝ)^2)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => measureReal_nonneg)).trans
      (emp s consistent)
  have bound : (m:ℝ)*(1/(200*(k+1:ℝ)^2)) ≤ (∑ _i ∈ I, 1/(100*(k+1:ℝ))) := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    have pos : (0:ℝ)<k+1 := by positivity
    field_simp
    nlinarith
  obtain ⟨i,hi,low⟩ := Finset.exists_le_of_sum_le (Finset.card_pos.mp nn) (restricted.trans bound)
  have lab := (Finset.mem_filter.mp hi).2
  exact ⟨i,lab,by simpa [lab] using low⟩

theorem line_radius {m} (f : Fin (m+1) → ℝ) (e : ℝ) (h : ∀ j : Fin m, |f j.succ - f j.castSucc| ≤ e)
    (i : Fin (m+1)) : |f i-f 0| ≤ i.val*e := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · simp
  · calc
      _ ≤ |f j.succ-f j.castSucc| + |f j.castSucc-f 0| := abs_sub_le .. 
      _ ≤ e + j.castSucc.val*e := add_le_add (h j) ih
      _ = _ := by simp; ring

theorem grid_jump {m} (f : Cell m → ℝ) {e : ℝ} (he : 0 ≤ e) (u v : Cell m)
    (big : 4*m*e < f u - f v) :
    (∃ j : Fin m, ∃ h, e ≤ |f (j.succ,h)-f (j.castSucc,h)|) ∨
      ∃ j : Fin m, ∃ h, e ≤ |f (h,j.succ)-f (h,j.castSucc)| := by
  by_contra! small
  obtain ⟨hs,vs⟩ := small
  have rad (a : Cell m) : |f a - f (0,0)| ≤ 2*m*e := by
    calc
      _ ≤ |f a - f (0,a.2)| + |f (0,a.2)-f (0,0)| := abs_sub_le .. 
      _ ≤ a.1.val*e+a.2.val*e := add_le_add
        (line_radius (fun i => f (i,a.2)) e (fun j => (hs j _).le) _)
        (line_radius (fun i => f (0,i)) e (fun j => (vs j _).le) _)
      _ ≤ _ := by
        have hu : (a.1.val:ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ a.1.isLt
        have hv : (a.2.val:ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ a.2.isLt
        nlinarith [mul_le_mul_of_nonneg_right hu he,mul_le_mul_of_nonneg_right hv he]
  linarith [(abs_le.mp (rad u)).2,(abs_le.mp (rad v)).1]

end PrivateList

namespace PrivateList

open MeasureTheory
open scoped Classical

/-- All data coordinates on an axis stay fixed except rank j, which sweeps a
reserved interval of N values. -/
def varying {m N L} (room : m+N+2 ≤ L) (j : Fin m) (t : Fin N) (i : Fin m) : Fin L :=
  ⟨if i < j then i.val else if i=j then j.val+t.val else i.val+N, by split_ifs <;> omega⟩

def sweep {m N L} (room : m+N+2 ≤ L) (j : Fin m) (t : Fin N) : Fin L :=
  ⟨j.val+t.val,by omega⟩

theorem varying_mono {m N L} (room : m+N+2 ≤ L) (j : Fin m) (t : Fin N) :
    StrictMono (varying room j t) := by
  intro i l hil
  have ord : i.val < l.val := hil
  simp only [varying,Fin.lt_def,Fin.ext_iff]
  split_ifs <;> omega

theorem varying_left {m N L} (room : m+N+2 ≤ L) (j : Fin m) {u t : Fin N} (ut : u<t) :
    AtRank (varying room j t) j.castSucc (sweep room j u) := by
  have : u.val < t.val := ut
  constructor <;> intro i hi <;> 
    simp only [varying,sweep,Fin.lt_def,Fin.ext_iff,Fin.val_castSucc] at * <;>
    split_ifs <;> omega

theorem varying_right {m N L} (room : m+N+2 ≤ L) (j : Fin m) {u t : Fin N} (tu : t<u) :
    AtRank (varying room j t) j.succ (sweep room j u) := by
  have : t.val < u.val := tu
  constructor <;> intro i hi <;>
    simp only [varying,sweep,Fin.lt_def,Fin.ext_iff,Fin.val_succ] at * <;>
    split_ifs <;> omega

def holding {m L} (room : m+1 ≤ L) (h : Fin (m+1)) (i : Fin m) : Fin L :=
  ⟨if i.val < h.val then i.val else i.val+1,by split <;> omega⟩

def spare {m L} (room : m+1 ≤ L) (h : Fin (m+1)) : Fin L := ⟨h.val,by omega⟩

theorem holding_mono {m L} (room : m+1 ≤ L) (h : Fin (m+1)) : StrictMono (holding room h) := by
  intro i j lt
  have : i.val < j.val := lt
  simp only [holding,Fin.lt_def]
  split <;> split <;> omega

theorem holding_rank {m L} (room : m+1 ≤ L) (h : Fin (m+1)) :
    AtRank (holding room h) h (spare room h) := by
  constructor <;> intro i hi <;> simp [holding,spare,Fin.lt_def,hi,Nat.not_lt.mpr]

theorem sweep_neighbor {k m N L} (T : Template k m) (room : m+N+2 ≤ L) (j : Fin m)
    (X : Fin L ↪o ℕ) (b : Fin m → ℕ) (u t : Fin N) :
    Neighbors (place T (X ∘ varying room j u) b) (place T (X ∘ varying room j t) b) := by
  refine ⟨T.xRank.symm j,fun i h => ?_⟩
  have hn : T.xRank i ≠ j := fun he => h (T.xRank.eq_symm_apply.mpr he)
  simp [place,varying,hn]

/-- Reversing the two axes lets exactly the same sweep test vertical rank-cell jumps. -/
def swappedRule {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) : Rule k m Ω where
  law s := A.law (fun i => ((s i).1.swap,(s i).2))
  normalized _ := A.normalized _
  predict w x := A.predict w x.swap
  listSize w x := A.listSize w x.swap
  measurable x y := A.measurable x.swap y

def swappedTemplate {k m} (T : Template k m) : Template k m := ⟨T.yRank,T.xRank,T.label⟩

theorem swapped_private {k m Ω} [MeasurableSpace Ω] {A : Rule k m Ω} {scale δ}
    (h : Private A scale δ) : Private (swappedRule A) scale δ := by
  intro s t ⟨i,eq⟩
  exact h _ _ ⟨i,fun j hj => by simp [eq j hj]⟩

theorem swapped_homogeneous {k m Ω L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ} (h : HomogeneousOn A T X Y v τ) :
    HomogeneousOn (swappedRule A) (swappedTemplate T) Y X (fun r => v r.swap) τ :=
  fun a b i y => h b a i.swap y

end PrivateList

namespace PrivateList

open MeasureTheory Set
open scoped Classical

/-- Threshold inequalities allow either orientation of the two neighboring rank
cells, since complementing every event reverses the pattern. -/
theorem orientedPacking {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Fin N → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (E : Fin N → Set Ω) (me : ∀ j, MeasurableSet (E j))
    {δ γ τ l h : ℝ} (hδ : 0 ≤ δ) (hδγ : δ < 2*γ) (hτ : 0 ≤ τ)
    (lr : 0 ≤ l ∧ l ≤ 1) (hr : 0 ≤ h ∧ h ≤ 1) (gap : 2*γ+2*τ ≤ |h-l|)
    (priv : ∀ i j, MeasureDominates 2 δ (P i) (P j))
    (below : ∀ i j, j < i → |(P i).real (E j) - l| ≤ τ)
    (above : ∀ i j, i < j → |(P i).real (E j) - h| ≤ τ)
    (d : ℕ) (hN : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 6 := by
  have nonempty : 0 < N := by
    have : 1 < 2^(d+1) := Nat.one_lt_two_pow (by omega); omega
  let i₀ : Fin N := ⟨0,nonempty⟩
  rw [show (6:ℝ) = 2*(2+1) by norm_num]
  by_cases dir : l ≤ h
  · rw [abs_of_nonneg (sub_nonneg.mpr dir)] at gap
    apply measurePacking (P i₀) P E me (c := (l+h)/2) (by norm_num) hδ hδγ
      (by linarith [lr.1]) (by linarith [hr.2]) (priv i₀) _ _ d hN
    · intro i j lt
      linarith [(abs_le.mp (below i j lt)).2]
    · intro i j lt
      linarith [(abs_le.mp (above i j lt)).1]
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge dir))] at gap
    apply measurePacking (P i₀) P (fun j => (E j)ᶜ) (fun j => (me j).compl)
      (c := 1-(l+h)/2) (by norm_num) hδ hδγ (by linarith [lr.2])
      (by linarith [hr.1]) (priv i₀) _ _ d hN
    · intro i j lt
      rw [probReal_compl_eq_one_sub (me _)]
      linarith [(abs_le.mp (below i j lt)).1]
    · intro i j lt
      rw [probReal_compl_eq_one_sub (me _)]
      linarith [(abs_le.mp (above i j lt)).2]

theorem horizontal_bound {k m Ω N L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ δ γ} (hom : HomogeneousOn A T X Y v τ) (priv : Private A 2 δ)
    (range : ∀ i y, 0 ≤ v i y ∧ v i y ≤ 1) (room : m+N+2 ≤ L)
    (hδ : 0 ≤ δ) (hδγ : δ < 2*γ) (hτ : 0 ≤ τ)
    (j : Fin m) (z : Fin (m+1)) (y : Label k)
    (jump : 2*γ+2*τ ≤ |v (j.succ,z) y - v (j.castSucc,z) y|)
    (d : ℕ) (hN : 2^(d+1)-1 ≤ N) : (d:ℝ)*(γ-δ/2)^2 ≤ 6 := by
  have size : m+1 ≤ L := by omega
  let b := holding size z
  let coord := spare size z
  let s (i : Fin N) := place T (X ∘ varying room j i) (Y ∘ b)
  let P (i : Fin N) := A.law (s i)
  have inst (i) : IsProbabilityMeasure (P i) := A.normalized _
  let E (i : Fin N) := {ω | y ∉ A.predict ω (X (sweep room j i),Y coord)}
  apply orientedPacking P E (fun i => A.measurable _ _) hδ hδγ hτ (range _ _) (range _ _) jump _ _ _ d hN
  · intro i u; exact priv _ _ (sweep_neighbor T room j X (Y ∘ b) i u)
  · intro i u lt
    exact local_rank hom (varying_mono room j i) (holding_mono size z) (j.castSucc,z) _ _ (varying_left room j lt) (holding_rank size z) y
  · intro i u lt
    exact local_rank hom (varying_mono room j i) (holding_mono size z) (j.succ,z) _ _ (varying_right room j lt) (holding_rank size z) y

end PrivateList

namespace PrivateList

open MeasureTheory
open scoped Classical

/-- A two-axis realizable template with balanced label counts precludes even a
private improper empirical list learner at the given fixed accuracy. -/
theorem template_impossible {k m Ω} [MeasurableSpace Ω] (T : Template k m) (hm : 0 < m)
    (balanced : ∀ y, m ≤ 2*(k+1)*(Finset.univ.filter fun i => T.label i = y).card)
    (fits : ∀ a b : Fin m → ℕ, StrictMono a → StrictMono b → Consistent (place T a b))
    (A : Rule k m Ω) {δ : ℝ} (hδ : 0 ≤ δ) (small : δ ≤ 1/(1000*(k+1:ℝ)*m))
    (priv : Private A 2 δ) : ¬Empirical A (1/(200*(k+1:ℝ)^2)) := by
  intro emp
  let D := 1000*(k+1)*m
  let τ : ℝ := 1/D
  let γ : ℝ := 5*τ
  have hD : 0 < D := by dsimp [D]; positivity
  have τp : 0 < τ := by dsimp [τ]; positivity
  have sm : δ ≤ τ := by simpa [τ,D] using small
  have margin : δ < 2*γ := by dsimp [γ]; linarith
  have apos : 0 < γ-δ/2 := by linarith
  obtain ⟨d,hd⟩ := exists_nat_gt (6/(γ-δ/2)^2)
  let N : ℕ := 2^(d+1)
  let L := 2*m + N + 4
  have bigN : m+N+2 ≤ L := by change _ ≤ 2*m+N+4;omega
  have room : 2*m+1 ≤ L := by
    change 2*m+1 ≤ 2*m+N+4
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _
  obtain ⟨X,Y,v,range,huniform⟩ := homogeneousRanks A T L D hD
  have hom : HomogeneousOn A T X Y v τ := huniform
  let s := place T (X ∘ spaced room) (Y ∘ spaced room)
  have inc : StrictMono (@spaced m L room) := by intro i j h; have : i.val < j.val := h; change 2*i.val+1 < 2*j.val+1; omega
  have hs : Consistent s := fits _ _ (X.strictMono.comp inc) (Y.strictMono.comp inc)
  let i₀ : Fin m := ⟨0,hm⟩
  obtain ⟨y,high⟩ := high_omission A s (s i₀).1
  obtain ⟨i,lab,low⟩ := low_omission A hm hs y (balanced y) emp
  let cell (i : Fin m) : Cell m := ((T.xRank i).succ,(T.yRank i).succ)
  have high' : omission A s (s i₀).1 y ≤ 2*(v (cell i₀) y+τ)+δ := (training_cells hom priv room i₀ y).2
  have low' : v (cell i) y ≤ 2*omission A s (s i).1 y+δ+τ := (training_cells hom priv room i y).1
  have eq : (m:ℝ)*τ = (1/(k+1:ℝ))/1000 := by
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    dsimp [τ,D]; push_cast; field_simp
  have mi : (1:ℝ) ≤ m := by exact_mod_cast hm
  have smallτ : τ ≤ m*τ := le_mul_of_one_le_left τp.le mi
  have gap : 4*(m:ℝ)*(2*γ+2*τ) < v (cell i₀) y - v (cell i) y := by
    dsimp [γ]
    have pos : 0 < (1/(k+1:ℝ)) := by positivity
    rw [show (1:ℝ)/(100*(k+1)) = (1/(k+1:ℝ))/100 by rw [mul_comm, div_div]] at low
    nlinarith only [high,low,high',low',smallτ,sm,eq,pos]
  have bound : (d:ℝ)*(γ-δ/2)^2 ≤ 6 := by
    obtain jump | jump := grid_jump (fun t => v t y) (e := 2*γ+2*τ)
      (by dsimp [γ]; positivity) _ _ gap
    · obtain ⟨j,z,hj⟩ := jump
      exact horizontal_bound hom priv range bigN hδ margin τp.le j z y hj d (Nat.sub_le ..)
    · obtain ⟨j,z,hj⟩ := jump
      exact horizontal_bound (swapped_homogeneous hom) (swapped_private priv) (fun t => range t.swap)
        bigN hδ margin τp.le j z y hj d (Nat.sub_le ..)
  exact (not_lt.mpr bound) ((div_lt_iff₀ (sq_pos_of_pos apos)).mp hd)

end PrivateList

namespace PrivateList

open scoped Classical

theorem valid_extension {I : Type} [Finite I] {k} (x : I → Point) (hx : Function.Injective x)
    (c : I → Label k) (blocks : ∀ i j, c i ≠ 0 → c i < c j → SW (x i) (x j))
    (inside : ∀ i j, i ≠ j → c i ≠ 0 → c i = c j → if (c i).val = 2 then
      opposed (x i) (x j) ∨ opposed (x j) (x i) else SW (x i) (x j) ∨ SW (x j) (x i)) :
    ∃ h : Hyp k, Valid h ∧ ∀ i, h (x i) = c i := by
  let h := Function.extend x c (fun _ => 0)
  have agrees (i) : h (x i) = c i := hx.extend_apply _ _ _
  have witnessed {u} (hu : h u ≠ 0) : ∃ i, x i = u := by
    by_contra hn; exact hu (Function.extend_apply' c _ _ hn)
  refine ⟨h, ⟨(Set.finite_range x).subset fun _ hu => witnessed hu, ?_, ?_⟩, agrees⟩
  · intro u v h₁ h₂
    obtain ⟨i,rfl⟩ := witnessed h₁
    obtain ⟨j,rfl⟩ := witnessed (ne_of_gt ((Fin.pos_iff_ne_zero.mpr h₁).trans h₂))
    simp only [agrees] at h₁ h₂
    exact blocks i j h₁ h₂
  · intro u v huv h₁ h₂
    obtain ⟨i,rfl⟩ := witnessed h₁
    obtain ⟨j,rfl⟩ := witnessed (h₂ ▸ h₁)
    simp only [agrees] at h₁ h₂ ⊢
    exact inside i j (fun e => huv (congrArg x e)) h₁ h₂

/-- Lexicographic positive-label blocks, reversing the vertical order exactly in color two. -/
def turn {k n} (p : Label k × Fin n) : Label k × Fin n :=
  (p.1, if p.1.val = 2 then p.2.rev else p.2)

theorem turn_turn {k n} (p : Label k × Fin n) : turn (turn p) = p := by
  rcases p with ⟨y,j⟩; by_cases hy : y.val = 2 <;> simp [turn,hy]

def balancedTemplate (k n : ℕ) : Template k ((k+1)*n) where
  xRank := Equiv.refl _
  yRank := (finProdFinEquiv.symm.trans (Equiv.mk turn turn turn_turn turn_turn)).trans finProdFinEquiv
  label i := (finProdFinEquiv.symm i).1

theorem balanced_counts (k n) (y : Label k) :
    (Finset.univ.filter fun i => (balancedTemplate k n).label i = y).card = n := by
  let f (j : Fin n) := finProdFinEquiv (y,j)
  have injective : Function.Injective f := fun _ _ h => congrArg Prod.snd (finProdFinEquiv.injective h)
  have eq : (Finset.univ.filter fun i => (balancedTemplate k n).label i = y) = Finset.univ.image f := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro h
      exact ⟨(finProdFinEquiv.symm i).2, by change (finProdFinEquiv.symm i).1 = y at h; change finProdFinEquiv (_,_) = _; rw [← h]; exact finProdFinEquiv.apply_symm_apply i⟩
    · rintro ⟨j,rfl⟩; exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (y,j))
  rw [eq,Finset.card_image_of_injective _ injective];simp

private theorem block_lt {k n} {y z : Label k} {i j : Fin n} (lt : y < z) :
    finProdFinEquiv (y,i) < finProdFinEquiv (z,j) := by
  change i.val+n*y.val < j.val+n*z.val
  have bound := Nat.mul_le_mul_left n (show y.val+1 ≤ z.val from lt)
  rw [Nat.mul_succ] at bound
  have := i.isLt
  omega

private theorem same_lt {k n} {y : Label k} {i j : Fin n} (lt : i < j) :
    finProdFinEquiv (y,i) < finProdFinEquiv (y,j) := by
  change i.val+n*y.val < j.val+n*y.val
  exact Nat.add_lt_add_right lt _

theorem balanced_fits (k n) (a b : Fin ((k+1)*n) → ℕ) (ha : StrictMono a) (hb : StrictMono b) :
    Consistent (place (balancedTemplate k n) a b) := by
  let e : Label k × Fin n ≃ Fin ((k+1)*n) := finProdFinEquiv
  let x (p : Label k × Fin n) : Point := (a (e p), b (e (turn p)))
  have inj : Function.Injective x := fun _ _ h => e.injective (ha.injective (congrArg Prod.fst h))
  have blocks (p q : Label k × Fin n) (_ : p.1 ≠ 0) (hpq : p.1 < q.1) : SW (x p) (x q) :=
    ⟨ha (block_lt hpq), hb (block_lt hpq)⟩
  have inside (p q : Label k × Fin n) (ne : p ≠ q) (_ : p.1 ≠ 0) (eq : p.1 = q.1) :
      if p.1.val = 2 then opposed (x p) (x q) ∨ opposed (x q) (x p)
      else SW (x p) (x q) ∨ SW (x q) (x p) := by
    rcases p with ⟨y,i⟩; rcases q with ⟨z,j⟩; change y=z at eq; subst z
    have ij : i ≠ j := fun h => ne (h ▸ rfl)
    by_cases hy : y.val = 2
    · simp only [hy, ↓reduceIte]
      rcases lt_or_gt_of_ne ij with lt|gt
      · left; exact ⟨ha (same_lt lt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ (Fin.rev_lt_rev.mpr lt))⟩
      · right; exact ⟨ha (same_lt gt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ (Fin.rev_lt_rev.mpr gt))⟩
    · simp only [hy, ↓reduceIte]
      rcases lt_or_gt_of_ne ij with lt|gt
      · left; exact ⟨ha (same_lt lt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ lt)⟩
      · right; exact ⟨ha (same_lt gt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ gt)⟩
  obtain ⟨h,hv,hit⟩ := valid_extension x inj Prod.fst blocks inside
  refine ⟨h,hv,fun i => ?_⟩
  have hi := hit (e.symm i)
  change h (a (e (e.symm i)), b (e (turn (e.symm i)))) = _ at hi
  rw [e.apply_symm_apply] at hi
  exact hi

end PrivateList

namespace PrivateList

open scoped Classical

/-- Expectation for an exactly uniform finite population. -/
noncomputable def avg {I : Type} [Fintype I] (f : I → ℝ) := (∑ i, f i) / Fintype.card I

theorem avg_mono {I : Type} [Fintype I] {f g : I → ℝ} (h : ∀ i, f i ≤ g i) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h i) (Nat.cast_nonneg _)

theorem avg_const {I : Type} [Fintype I] [Nonempty I] (c : ℝ) : avg (fun _ : I => c) = c := by
  simp [avg, ne_of_gt (show (0:ℝ) < Fintype.card I by exact_mod_cast Fintype.card_pos)]

theorem avg_add {I : Type} [Fintype I] (f g : I → ℝ) :
    avg (fun i => f i + g i) = avg f + avg g := by simp [avg,Finset.sum_add_distrib,add_div]

theorem avg_mul {I : Type} [Fintype I] (a : ℝ) (f : I → ℝ) :
    avg (fun i => a*f i) = a*avg f := by rw [avg,← Finset.mul_sum,avg,mul_div_assoc]

theorem avg_sum {I J : Type} [Fintype I] [Fintype J] (f : I → J → ℝ) :
    avg (fun i => ∑ j, f i j) = ∑ j, avg (fun i => f i j) := by
  simp only [avg,div_eq_mul_inv, ← Finset.sum_mul];rw [Finset.sum_comm]

theorem avg_equiv {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J) (f : J → ℝ) :
    avg (fun i => f (e i)) = avg f := by rw [avg,avg,e.sum_comp,Fintype.card_congr e]

theorem avg_prod {I J : Type} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    avg f = avg (fun i => avg (fun j => f (i,j))) := by
  rw [avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  simp only [avg,div_eq_mul_inv,← Finset.sum_mul];ring

theorem avg_eval {I J : Type} [DecidableEq I] [Fintype I] [Fintype J] [Nonempty J] (i : I) (f : J → ℝ) :
    avg (fun u : I → J => f (u i)) = avg f := by
  let e := Equiv.funSplitAt i J
  calc
    _ = avg (fun p : J × ({j // j ≠ i} → J) => f p.1) := avg_equiv e _
    _ = _ := by rw [avg_prod];simp only [avg_const]

theorem avg_eval₂ {I J : Type} [DecidableEq I] [Fintype I] [Fintype J] [Nonempty J] {i j : I} (h : j ≠ i)
    (f : J → J → ℝ) : avg (fun u : I → J => f (u i) (u j)) = avg (fun a => avg (f a)) := by
  let e := Equiv.funSplitAt i J
  calc
    _ = avg (fun p : J × ({j // j ≠ i} → J) => f p.1 (p.2 ⟨j,h⟩)) := avg_equiv e _
    _ = _ := by
      rw [avg_prod];exact congrArg avg (funext fun a => avg_eval (⟨j,h⟩ : {t // t≠i}) (f a))

noncomputable def oneIf (p : Prop) : ℝ := if p then 1 else 0

theorem avg_single {I : Type} [Fintype I] (i : I) : avg (fun j => oneIf (j=i)) = 1/Fintype.card I := by
  simp [avg,oneIf]

theorem avg_hit_bound {s m : ℕ} [NeZero m] (x : Fin m) :
    avg (fun u : Fin s → Fin m => oneIf (∃ i, u i = x)) ≤ s/m := by
  calc
    _ ≤ avg (fun u : Fin s → Fin m => ∑ i, oneIf (u i=x)) := by
      apply avg_mono; intro u; by_cases h : ∃ i, u i = x
      · obtain ⟨i,hi⟩ := h
        have le := Finset.single_le_sum (f := fun j => oneIf (u j=x))
          (fun j _ => by unfold oneIf; split <;> norm_num) (Finset.mem_univ i)
        simpa [oneIf,hi,show ∃ i, u i = x from ⟨i,hi⟩] using le
      · simp [oneIf,show ∀ i, u i ≠ x from fun i hi => h ⟨i,hi⟩]
    _ = _ := by
      have each (i : Fin s) : avg (fun u : Fin s → Fin m => oneIf (u i=x)) = 1/(m:ℝ) :=
        (avg_eval i (fun a => oneIf (a=x))).trans (by simpa only [Fintype.card_fin] using avg_single x)
      rw [avg_sum];simp only [each,Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem avg_collision_bound {s m : ℕ} [NeZero m] :
    avg (fun u : Fin s → Fin m => oneIf (¬Function.Injective u)) ≤ s^2/m := by
  let F (u : Fin s → Fin m) (i j : Fin s) := if i=j then 0 else oneIf (u i=u j)
  have nn (u i j) : 0 ≤ F u i j := by dsimp [F,oneIf]; split <;> (try split) <;> norm_num
  calc
    _ ≤ avg (fun u => ∑ i, ∑ j, F u i j) := by
      apply avg_mono;intro u
      by_cases h : Function.Injective u
      · simp only [oneIf,h,not_true_eq_false,↓reduceIte]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => nn ..
      · obtain ⟨i,j,hit,ne⟩ : ∃ i j, u i=u j ∧ i≠j := by
          by_contra! all; exact h (fun i j e => all i j e)
        have a := Finset.single_le_sum (f := F u i) (fun j _ => nn u i j) (Finset.mem_univ j)
        have b := Finset.single_le_sum (f := fun i => ∑ j, F u i j) (fun i _ => Finset.sum_nonneg fun j _ => nn u i j) (Finset.mem_univ i)
        simpa [oneIf,h,F,ne,hit] using a.trans b
    _ = ∑ i, ∑ j, avg (fun u => F u i j) := by simp only [avg_sum]
    _ ≤ ∑ _i : Fin s, ∑ _j : Fin s, (1/(m:ℝ)) := by
      apply Finset.sum_le_sum;intro i _;apply Finset.sum_le_sum;intro j _
      by_cases h : i=j
      · simp [F,h,avg_const]
      · simp only [F,h,↓reduceIte]
        apply (avg_eval₂ (Ne.symm h) (fun a b : Fin m => oneIf (a=b))).le.trans
        have each (a : Fin m) : avg (fun b : Fin m => oneIf (a=b)) = 1/(m:ℝ) := by
          simpa only [eq_comm,Fintype.card_fin] using avg_single (I := Fin m) a
        simp only [each,avg_const,le_refl]
    _ = _ := by simp;ring

end PrivateList

namespace PrivateList

open MeasureTheory Set
open scoped Classical

def omitted {k s Ω} [MeasurableSpace Ω] (A : Rule k s Ω) (z : Point × Label k) : Set Ω :=
  {ω | z.2 ∉ A.predict ω z.1}

/-- Risk on the uniform distribution of a finite labeled population, counting multiplicities. -/
noncomputable def risk {k s m Ω} [MeasurableSpace Ω] (A : Rule k s Ω) (t : Sample k m) (ω : Ω) : ℝ :=
  avg fun i => (omitted A (t i)).indicator (fun _ => (1:ℝ)) ω

/-- The usual PAC guarantee specialized to arbitrary finitely supported uniform
labeled populations and exactly IID samples of size `s`. -/
def PopulationPAC {k s Ω} [MeasurableSpace Ω] (A : Rule k s Ω) (α β : ℝ) : Prop :=
  ∀ m, 0 < m → ∀ t : Sample k m, Consistent t →
    avg (fun u : Fin s → Fin m => (A.law (t ∘ u)).real {ω | α < risk A t ω}) ≤ β

theorem avg_omissions {k s m Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω) (t : Sample k m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {α : ℝ} (hα : 0 ≤ α) :
    avg (fun i => μ.real (omitted A (t i))) ≤ α + μ.real {ω | α < risk A t ω} := by
  let f (i : Fin m) := (omitted A (t i)).indicator (fun _ => (1:ℝ))
  have meas (i) : Measurable (f i) := measurable_const.indicator (A.measurable _ _)
  have intg (i) : Integrable (f i) μ := (integrable_const _).indicator (A.measurable _ _)
  have F : Measurable (risk A t) :=
    (Finset.measurable_fun_sum _ (fun i _ => meas i)).div_const _
  let E := {ω | α < risk A t ω}
  have mE : MeasurableSet E := measurableSet_lt measurable_const F
  have hInt : (∫ ω, risk A t ω ∂μ) = avg (fun i => μ.real (omitted A (t i))) := by
    change (∫ ω, (∑ i, f i ω) / (Fintype.card (Fin m):ℝ) ∂μ) = _
    simp only [integral_div,integral_finsetSum _ (fun i _ => intg i)]
    have fi (i) : (∫ ω, f i ω ∂μ) = μ.real (omitted A (t i)) := integral_indicator_one (A.measurable _ _)
    simp only [avg,fi]
  have riskInt : Integrable (risk A t) μ :=
    (integrable_finsetSum _ (fun i _ => intg i)).div_const _
  have failInt : Integrable (E.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator mE
  have cInt : (∫ _ : Ω, α ∂μ) = α := by simp
  have fail : (∫ ω, E.indicator (fun _ => (1:ℝ)) ω ∂μ) = μ.real E := integral_indicator_one mE
  rw [← hInt]
  apply LE.le.trans (b := ∫ ω, α+E.indicator (fun _ => (1:ℝ)) ω ∂μ)
  swap
  · rw [integral_add (integrable_const α) failInt,cInt,fail]
  apply integral_mono riskInt ((integrable_const _).add failInt)
  intro ω
  change risk A t ω ≤ α + E.indicator (fun _ => (1:ℝ)) ω
  by_cases h : ω ∈ E
  · rw [Set.indicator_of_mem h]
    have le : risk A t ω ≤ 1 := by
      calc
        _ ≤ avg (fun _ : Fin m => (1:ℝ)) := avg_mono (fun i => by dsimp [Set.indicator];split <;> norm_num)
        _ = _ := avg_const _
    linarith
  · rw [Set.indicator_of_notMem h,add_zero]
    exact le_of_not_gt h

end PrivateList

namespace PrivateList

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable def mixture {I Ω : Type} [Fintype I] [MeasurableSpace Ω] (μ : I → Measure Ω) : Measure Ω :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, μ i

theorem mixture_probability {I Ω : Type} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : I → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (mixture μ) := by
  constructor
  rw [mixture,Measure.smul_apply,Measure.finsetSum_apply]
  simp [smul_eq_mul,ENNReal.inv_mul_cancel (show (Fintype.card I : ℝ≥0∞) ≠ 0 by exact_mod_cast Fintype.card_ne_zero) (by simp)]

theorem mixture_real {I Ω : Type} [Fintype I] [MeasurableSpace Ω] (μ : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (E : Set Ω) : (mixture μ).real E = avg (fun i => (μ i).real E) := by
  rw [mixture,measureReal_ennreal_smul_apply,measureReal_def,Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  simp [avg,measureReal_def,div_eq_inv_mul]

/-- An IID draw with repeated indices is replaced by a fixed dataset independent of the population. -/
noncomputable def subsample {k m s} (t : Sample k m) (u : Fin s → Fin m) : Sample k s :=
  if Function.Injective u then t ∘ u else fun _ => ((0,0),0)

noncomputable def resample {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω) : Rule k m Ω where
  law t := mixture (fun u => A.law (subsample t u))
  normalized t := by
    let (u : Fin s → Fin m) := A.normalized (subsample t u)
    exact mixture_probability _
  predict := A.predict
  listSize := A.listSize
  measurable := A.measurable

theorem resample_real {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω)
    (t : Sample k m) (E : Set Ω) : ((resample A).law t).real E = avg (fun u => (A.law (subsample t u)).real E) := by
  let (u : Fin s → Fin m) := A.normalized (subsample t u)
  exact mixture_real _ _

theorem resample_private {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω)
    {δ : ℝ} (hδ : 0 ≤ δ) (priv : Private A 2 δ) : Private (resample (m := m) A) 2 (δ*(s/m)) := by
  rintro t t' ⟨x,hx⟩ E hE
  rw [resample_real,resample_real]
  have bound (u : Fin s → Fin m) : (A.law (subsample t' u)).real E ≤
      2*(A.law (subsample t u)).real E + δ*oneIf (∃ i, u i=x) := by
    by_cases inj : Function.Injective u
    · by_cases hit : ∃ i, u i=x
      · obtain ⟨i,hi⟩ := hit
        have adj : Neighbors (t ∘ u) (t' ∘ u) := ⟨i,fun j ne => hx _ (fun hj => ne (inj (hj.trans hi.symm)))⟩
        simpa [subsample,inj,oneIf,show ∃ i, u i=x from ⟨i,hi⟩] using priv _ _ adj E hE
      · have eq : t ∘ u = t' ∘ u := funext fun i => hx _ (fun h => hit ⟨i,h⟩)
        simp only [subsample,inj,↓reduceIte,eq,oneIf,hit,mul_zero,add_zero]
        linarith [measureReal_nonneg (μ := A.law (t' ∘ u)) (s := E)]
    · simp only [subsample,inj,↓reduceIte]
      have corr : 0 ≤ δ*oneIf (∃ i, u i=x) := mul_nonneg hδ (by unfold oneIf;split <;> norm_num)
      linarith [measureReal_nonneg (μ := A.law (fun _ => ((0,0),0))) (s := E)]
  exact (avg_mono bound).trans (by rw [avg_add,avg_mul,avg_mul]; gcongr; exact avg_hit_bound x)

end PrivateList

namespace PrivateList

open MeasureTheory Set
open scoped Classical

theorem avg_comm {I J : Type} [Fintype I] [Fintype J] (f : I → J → ℝ) :
    avg (fun i => avg (f i)) = avg (fun j => avg (fun i => f i j)) := by
  simp only [avg,div_eq_mul_inv,← Finset.sum_mul];rw [Finset.sum_comm];ring

theorem resample_empirical {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω)
    {α β : ℝ} (hα : 0 ≤ α) (pac : PopulationPAC A α β) :
    Empirical (resample (m := m) A) (α+β+s^2/m) := by
  intro t fit
  let E (i : Fin m) := omitted A (t i)
  let bad := {ω | α < risk A t ω}
  let B : Rule k m Ω := resample A
  have prob (t : Sample k s) := A.normalized t
  let q (u : Fin s → Fin m) (i : Fin m) := (A.law (subsample t u)).real (E i)
  have bound (u : Fin s → Fin m) : avg (q u) ≤
      α + (A.law (t ∘ u)).real bad + oneIf (¬Function.Injective u) := by
    by_cases h : Function.Injective u
    · simpa [q,subsample,h,oneIf,E,bad] using avg_omissions A t (A.law (t ∘ u)) hα
    · have le : avg (q u) ≤ 1 := (avg_mono (g := fun _ => (1:ℝ)) (fun i => measureReal_le_one)).trans_eq (avg_const _)
      simp only [oneIf,h,not_false_eq_true,↓reduceIte]
      linarith [measureReal_nonneg (μ := A.law (t ∘ u)) (s := bad)]
  have each (i : Fin m) : omission B t (t i).1 (t i).2 = avg (fun u => q u i) := resample_real A t (E i)
  have av : avg (fun i => omission B t (t i).1 (t i).2) ≤ α+β+s^2/m := by
    calc
      _ = avg (fun u => avg (q u)) := by simp only [each];exact avg_comm _
      _ ≤ _ := avg_mono bound
      _ ≤ _ := by
        rw [avg_add,avg_add,avg_const]
        exact add_le_add (add_le_add_right (pac m (NeZero.pos _) _ fit) α) avg_collision_bound
  change (∑ i, omission B t (t i).1 (t i).2) ≤ _
  simpa only [mul_comm (m:ℝ)] using (div_le_iff₀ (show (0:ℝ) < m by exact_mod_cast NeZero.pos m)).mp
    (show (∑ i, omission B t (t i).1 (t i).2) / m ≤ α+β+s^2/m by simpa [avg] using av)

end PrivateList

namespace PrivateList

open MeasureTheory

/-- The planar finite-support class answers the private list-learning question negatively.
Both list dimensions equal one. For each sample size `s`, approximate privacy at ε=1/10
and δ≤1/(1000(k+1)(s+1)) rules out the displayed fixed PAC accuracy and confidence,
even for improper outputs and even just on uniform realizable finite populations. -/
theorem separation (k : ℕ) (hk : 2 ≤ k) :
    (∀ n, (LittlestoneDepth k n ↔ n ≤ 1) ∧ (MonotoneLength k n ↔ n ≤ 1)) ∧
    ∀ (s : ℕ) (Ω : Type) [MeasurableSpace Ω] (A : Rule k s Ω) (δ : ℝ),
      0 ≤ δ → δ ≤ 1/(1000*(k+1:ℝ)*(s+1:ℝ)) → Private A (Real.exp (1/10)) δ →
      ¬PopulationPAC A (1/(800*(k+1:ℝ)^2)) (1/(800*(k+1:ℝ)^2)) := by
  refine ⟨dimensionOne k hk, ?_⟩
  intro s Ω _ A δ hδ small priv pac
  let q := k+1
  let n := 400*q*(s+1)^2
  let m := q*n
  have hp : 0 < m := by dsimp [m,n,q]; positivity
  let : NeZero m := ⟨hp.ne'⟩
  have hm : (0:ℝ) < m := by exact_mod_cast hp
  have hq : (0:ℝ) < k+1 := by positivity
  have sp : (0:ℝ) < s+1 := by positivity
  have scale : Real.exp (1/10) ≤ 2 := (Real.exp_le_two_add_div_two_sub (x := 1/10) (by norm_num) (by norm_num)).trans (by norm_num)
  have pr : Private A 2 δ := fun t t' adj E hE => (priv t t' adj E hE).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right scale measureReal_nonneg) _)
  let B : Rule k m Ω := resample A
  have err : (s:ℝ)^2/m ≤ 1/(400*(k+1:ℝ)^2) := by
    apply (div_le_div_iff₀ hm (by positivity)).mpr
    dsimp [m,n,q];push_cast;nlinarith [sq_nonneg (s:ℝ),sq_nonneg (k:ℝ)]
  have dsmall : δ*((s:ℝ)/m) ≤ 1/(1000*(k+1:ℝ)*m) := by
    calc
      _ ≤ (1/(1000*(k+1:ℝ)*(s+1:ℝ)))*(s/m) := mul_le_mul_of_nonneg_right small (by positivity)
      _ ≤ _ := by field_simp; nlinarith
  let T := balancedTemplate k n
  have balanced (y) : m ≤ 2*(k+1)*(Finset.univ.filter fun i => T.label i=y).card := by
    rw [show (Finset.univ.filter fun i => T.label i=y).card = n from balanced_counts k n y]
    change (k+1)*n ≤ _
    calc _ ≤ 2*((k+1)*n) := Nat.le_mul_of_pos_left _ (by decide)
         _ = _ := by rw [Nat.mul_assoc]
  apply template_impossible T hp balanced (balanced_fits k n) B (mul_nonneg hδ (by positivity)) dsmall
    (resample_private A hδ pr)
  intro t fit
  have e := resample_empirical (m := m) A (by positivity) pac t fit
  apply e.trans
  apply mul_le_mul_of_nonneg_left _ hm.le
  have eq : 1/(800*(k+1:ℝ)^2)+1/(800*(k+1:ℝ)^2)+1/(400*(k+1:ℝ)^2) = 1/(200*(k+1:ℝ)^2) := by field_simp;ring
  rw [← eq];exact add_le_add_right err _

end PrivateList
