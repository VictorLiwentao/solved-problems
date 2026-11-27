module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Minimal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Standalone verification of the quantitative hidden-pair lower bound and
the negative answer at every positive inverse-polynomial confidence exponent. -/

namespace MISQueries

/-- An answer is legal when it is an inclusion-maximal independent subset of the query. -/
def Legal {V : Type*} (G : SimpleGraph V) (Q A : Finset V) : Prop :=
  Maximal (fun S : Finset V => S ⊆ Q ∧ ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y) A

abbrev Oracle (V : Type*) := Finset V → Finset V

def LegalOracle {V : Type*} (G : SimpleGraph V) (O : Oracle V) : Prop := ∀ Q, Legal G Q (O Q)

/-- A deterministic nonadaptive learner consists of a list of queries, followed by
a decoder acting on the list of oracle answers. -/
abbrev Strategy (n t : ℕ) :=
  (Fin t → Finset (Fin n)) × ((Fin t → Finset (Fin n)) → SimpleGraph (Fin n))

/-- A finite distribution on *all* deterministic behaviors models arbitrary coins.
Both the spaces of query schedules and answer decoders are finite. -/
def Distribution {X : Type*} [Fintype X] (w : X → ℝ) : Prop := (∀ x, 0 ≤ w x) ∧ ∑ x, w x = 1

noncomputable def error {n t : ℕ} (w : Strategy n t → ℝ) (G : SimpleGraph (Fin n)) (O : Oracle (Fin n)) : ℝ := by
  classical
  exact ∑ s, w s * (if s.2 (fun i => O (s.1 i)) = G then 0 else 1)

noncomputable def DegreeBound {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ) : Prop := by
  classical
  exact ∀ v, G.degree v ≤ D

/-- The guarantee quantifies over every legal oracle, including the worst choices
of maximal independent answers, on every graph with the stated upper degree bound. -/
def Learns {n t : ℕ} (w : Strategy n t → ℝ) (D : ℕ) (ε : ℝ) :=
  ∀ (G : SimpleGraph (Fin n)), DegreeBound G D → ∀ O, LegalOracle G O → error w G O ≤ ε

end MISQueries

namespace MISQueries

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A clique on `e ∪ B` with the distinguished pair optionally deleted.
Every other vertex is isolated. -/
def hidden (e B : Finset V) (keep : Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ x ∈ e ∪ B ∧ y ∈ e ∪ B ∧ (keep = true ∨ ¬(x ∈ e ∧ y ∈ e))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.imp id (fun h' k => h' k.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype V] in
theorem pair_spanned {e : Finset V} (he : e.card = 2) {x y : V}
    (hx : x ∈ e) (hy : y ∈ e) (hxy : x ≠ y) : e = {x,y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
  · simp [he,hxy]

omit [Fintype V] in
theorem hidden_distinct {e : Finset V} (he : e.card = 2) (B : Finset V) : hidden e B false ≠ hidden e B true := by
  obtain ⟨x,y,hn, rfl⟩ := Finset.card_eq_two.mp he
  intro h
  have ha : (hidden {x,y} B true).Adj x y := ⟨hn, by simp, by simp, .inl rfl⟩
  rw [← h] at ha
  exact ha.2.2.2.elim (by decide) (fun h' => h' ⟨by simp, by simp⟩)

theorem hidden_degree {e B : Finset V} (hc : e.card = 2) {D : ℕ} (hB : B.card < D) (keep : Bool) :
    DegreeBound (hidden e B keep) D := by
  classical
  intro x
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hx : x ∈ e ∪ B
  · have hs : (hidden e B keep).neighborFinset x ⊆ (e ∪ B).erase x := by
      intro y hy
      have ha := ((hidden e B keep).mem_neighborFinset ..).mp hy
      exact Finset.mem_erase.mpr ⟨ha.1.symm,ha.2.2.1⟩
    have hle := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hx] at hle
    have hu := Finset.card_union_le e B
    omega
  · have hempty : (hidden e B keep).neighborFinset x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun _ h => hx (((hidden e B keep).mem_neighborFinset ..).mp h).2.1
    simp [hempty]

omit [DecidableEq V] in
theorem legal_exists (G : SimpleGraph V) (Q : Finset V) : ∃ A, Legal G Q A := by
  let P (S : Finset V) := S ⊆ Q ∧ ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y
  have h0 : P ∅ := by simp [P]
  obtain ⟨A,_,hA⟩ := exists_maximal_ge_of_wellFoundedGT P ∅ h0
  exact ⟨A,hA⟩

omit [Fintype V] [DecidableEq V] in
theorem legal_congr {G H : SimpleGraph V} {Q A : Finset V}
    (hh : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y ↔ H.Adj x y) (h : Legal G Q A) : Legal H Q A := by
  have hcond (T : Finset V) :
      (T ⊆ Q ∧ ∀ x ∈ T, ∀ y ∈ T, ¬G.Adj x y) ↔ (T ⊆ Q ∧ ∀ x ∈ T, ∀ y ∈ T, ¬H.Adj x y) := by
    constructor <;> rintro ⟨hT,hi⟩ <;> refine ⟨hT, fun x hx y hy he => hi _ hx _ hy ?_⟩
    · exact (hh _ (hT hx) _ (hT hy)).2 he
    · exact (hh _ (hT hx) _ (hT hy)).1 he
  exact ⟨(hcond A).1 h.1, fun T hT hsub => h.2 ((hcond T).2 hT) hsub⟩

omit [Fintype V] in
/-- A queried blocker masks the hidden bit: choose that blocker and every
queried outside isolate. This one answer is maximal under either edge status. -/
theorem blocker_answer {e B Q : Finset V} {b : V} (hb : b ∈ B) (hbe : b ∉ e) (hq : b ∈ Q) (k : Bool) :
    Legal (hidden e B k) Q (insert b (Q \ (e ∪ B))) := by
  classical
  constructor
  · refine ⟨Finset.insert_subset hq (Finset.sdiff_subset), ?_⟩
    intro x hx y hy ha
    rcases Finset.mem_insert.mp hx with rfl | hi
    · rcases Finset.mem_insert.mp hy with rfl | hj
      · exact ha.1 rfl
      · exact (Finset.mem_sdiff.mp hj).2 ha.2.2.1
    · exact (Finset.mem_sdiff.mp hi).2 ha.2.1
  · intro T ht hsub v hv
    by_cases he : v ∈ e ∪ B
    · by_cases hvb : v = b
      · exact Finset.mem_insert.mpr (.inl hvb)
      · have hadj : (hidden e B k).Adj v b := ⟨hvb, he, Finset.mem_union_right _ hb, .inr fun h => hbe h.2⟩
        exact False.elim (ht.2 v hv b (hsub (Finset.mem_insert_self ..)) hadj)
    · exact Finset.mem_insert.mpr (.inr (Finset.mem_sdiff.mpr ⟨ht.1 hv,he⟩))

omit [Fintype V] in
/-- When the distinguished pair is not queried in full, the two induced
query graphs have exactly the same edges. -/
theorem omitted_pair {e Q : Finset V} (hc : e.card = 2) (hn : ¬e ⊆ Q) (B : Finset V) :
    ∀ x ∈ Q, ∀ y ∈ Q, (hidden e B false).Adj x y ↔ (hidden e B true).Adj x y := by
  intro x hx y hy
  constructor
  · exact fun h => ⟨h.1,h.2.1,h.2.2.1,.inl rfl⟩
  · intro h
    refine ⟨h.1,h.2.1,h.2.2.1,.inr ?_⟩
    rintro ⟨he,he'⟩
    apply hn
    rw [pair_spanned hc he he' h.1]
    exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)

/-- The two fixed deterministic oracles agree on every query except a query
containing both endpoints and containing no blocker. -/
theorem coupled_oracles {e B : Finset V} (hc : e.card = 2) (hdis : Disjoint e B) :
    ∃ O : Bool → Oracle V, (∀ k, LegalOracle (hidden e B k) (O k)) ∧
      ∀ Q, (¬e ⊆ Q ∨ ¬Disjoint Q B) → O false Q = O true Q := by
  classical
  have hQ (Q : Finset V) : ∃ f : Bool → Finset V, (∀ k, Legal (hidden e B k) Q (f k)) ∧
      ((¬e ⊆ Q ∨ ¬Disjoint Q B) → f false = f true) := by
    by_cases hQB : Disjoint Q B
    · by_cases hfull : e ⊆ Q
      · exact ⟨fun k => (legal_exists (hidden e B k) Q).choose,
          fun k => (legal_exists (hidden e B k) Q).choose_spec, fun h => (h.elim (· hfull) (· hQB)).elim⟩
      · obtain ⟨A,hA⟩ := legal_exists (hidden e B false) Q
        exact ⟨fun _ => A, fun k => by cases k; exact hA; exact legal_congr (omitted_pair hc hfull B) hA,
          fun _ => rfl⟩
    · obtain ⟨b,hbQ,hbB⟩ := Finset.not_disjoint_iff.mp hQB
      exact ⟨fun _ => insert b (Q \ (e ∪ B)),
        blocker_answer hbB (fun he => Finset.disjoint_left.mp hdis he hbB) hbQ, fun _ => rfl⟩
  exact ⟨fun k Q => (hQ Q).choose k, fun k Q => (hQ Q).choose_spec.1 k,
    fun Q => (hQ Q).choose_spec.2⟩

end MISQueries

namespace MISQueries

variable {V : Type*} [DecidableEq V]

/-- Exact expectation after independently including each listed coordinate with
probability `p`; repeated coordinates, if present, are included by union. -/
noncomputable def average (p : ℝ) : List V → (Finset V → ℝ) → ℝ
  | [], f => f ∅
  | x :: xs, f => (1-p) * average p xs f + p * average p xs (fun S => f (insert x S))

namespace average

theorem const (p : ℝ) (xs : List V) (r : ℝ) : average p xs (fun _ => r) = r := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [average, ih]; ring

theorem add (p : ℝ) (xs : List V) (f g : Finset V → ℝ) :
    average p xs (fun S => f S + g S) = average p xs f + average p xs g := by
  induction xs generalizing f g with
  | nil => rfl
  | cons x xs ih => simp only [average, ih]; ring

theorem scale (p : ℝ) (xs : List V) (r : ℝ) (f : Finset V → ℝ) :
    average p xs (fun S => r * f S) = r * average p xs f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [average, ih]; ring

theorem sum {I : Type*} (p : ℝ) (xs : List V) (T : Finset I) (f : I → Finset V → ℝ) :
    average p xs (fun S => ∑ i ∈ T, f i S) = ∑ i ∈ T, average p xs (f i) := by
  classical
  induction T using Finset.induction with
  | empty => simp [const]
  | @insert i T hi ih => simp only [Finset.sum_insert hi, add, ih]

theorem mono {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) {f g : Finset V → ℝ} (h : ∀ S, f S ≤ g S) :
    average p xs f ≤ average p xs g := by
  induction xs generalizing f g with
  | nil => exact h ∅
  | cons x xs ih =>
    apply add_le_add (mul_le_mul_of_nonneg_left (ih h) (sub_nonneg.mpr hp'))
      (mul_le_mul_of_nonneg_left (ih (fun S => h (insert x S))) hp)

theorem nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) {f : Finset V → ℝ} (h : ∀ S, 0 ≤ f S) :
    0 ≤ average p xs f := by simpa only [const] using mono hp hp' xs h

/-- Positive correlation for increasing functions under biased independent coins. -/
theorem harris {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) (f g : Finset V → ℝ)
    (hf : Monotone f) (hg : Monotone g) :
    average p xs f * average p xs g ≤ average p xs (fun S => f S * g S) := by
  induction xs generalizing f g with
  | nil => rfl
  | cons x xs ih =>
    let f' := fun S => f (insert x S)
    let g' := fun S => g (insert x S)
    have h0 := ih f g hf hg
    have h1 := ih f' g' (fun _ _ h => hf (Finset.insert_subset_insert _ h))
      (fun _ _ h => hg (Finset.insert_subset_insert _ h))
    have df : 0 ≤ average p xs f' - average p xs f := sub_nonneg.mpr (mono hp hp' xs (fun S => hf (Finset.subset_insert _ S)))
    have dg : 0 ≤ average p xs g' - average p xs g := sub_nonneg.mpr (mono hp hp' xs (fun S => hg (Finset.subset_insert _ S)))
    have hex := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) (mul_nonneg df dg)
    dsimp only [average]
    change _ ≤ (1-p)*average p xs (fun S => f S * g S) + p*average p xs (fun S => f' S * g' S)
    calc
      _ ≤ (1-p)*(average p xs f * average p xs g) + p*(average p xs f' * average p xs g') := by
        dsimp only [f',g'] at *; linarith only [hex]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hp')) (mul_le_mul_of_nonneg_left h1 hp)

/-- Harris for all events in a list (or for nonnegative, increasing observables). -/
theorem harris_prod {I : Type*} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V)
    (T : Finset I) (f : I → Finset V → ℝ) (hm : ∀ i, Monotone (f i)) (hpos : ∀ i S, 0 ≤ f i S) :
    (∏ i ∈ T, average p xs (f i)) ≤ average p xs (fun S => ∏ i ∈ T, f i S) := by
  classical
  induction T using Finset.induction with
  | empty => simp [const]
  | @insert i T hi ih =>
    simp only [Finset.prod_insert hi]
    exact (mul_le_mul_of_nonneg_left ih (nonneg hp hp' xs (hpos i))).trans
      (harris hp hp' xs (f i) _ (hm i) (fun _ _ hab => Finset.prod_le_prod₀ (fun j _ => hpos j _) (fun j _ => hm j hab)))

end average
end MISQueries

namespace MISQueries
variable {V : Type*} [DecidableEq V]

/-- A numerical indicator for finite probability calculations. -/
noncomputable def bit (p : Prop) : ℝ := by classical exact if p then 1 else 0
@[simp] theorem bit_pos {p : Prop} (h : p) : bit p = 1 := by simp [bit,h]
@[simp] theorem bit_neg {p : Prop} (h : ¬p) : bit p = 0 := by simp [bit,h]
theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by classical by_cases h : p <;> simp [h]
theorem bit_le_one (p : Prop) : bit p ≤ 1 := by classical by_cases h : p <;> simp [h]
theorem bit_mono {p q : Prop} (h : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [hp,h hp]
  · simpa only [bit_neg hp] using bit_nonneg q

theorem bit_not (p : Prop) : bit (¬p) = 1 + -1 * bit p := by
  classical
  by_cases h : p <;> simp [h,bit]

theorem avoidance (p : ℝ) (xs : List V) (R : Finset V) :
    average p xs (fun S => bit (Disjoint S R)) = (1-p) ^ (xs.filter (fun x => decide (x ∈ R))).length := by
  induction xs with
  | nil => simp [average,bit]
  | cons x xs ih =>
    by_cases hx : x ∈ R <;>
      simp [average, Finset.disjoint_insert_left, hx, average.const, ih, pow_succ] <;> ring

theorem hit_probability [Fintype V] (p : ℝ) (R : Finset V) :
    average p Finset.univ.toList (fun S => bit (¬Disjoint S R)) = 1 - (1-p)^R.card := by
  classical
  let xs : List V := Finset.univ.toList
  have hset : (xs.filter (fun x => decide (x ∈ R))).toFinset = R := by ext; simp [xs]
  have hn := List.toFinset_card_of_nodup ((Finset.nodup_toList (Finset.univ : Finset V)).filter (fun x => decide (x ∈ R)))
  rw [hset] at hn
  simp_rw [bit_not]
  rw [average.add, average.const, average.scale, avoidance, ← hn]
  ring

/-- The exponential moment of the number of blockers is at most (1+p)^n. -/
theorem size_moment {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) :
    average p xs (fun S => (2 : ℝ)^S.card) ≤ (1+p)^xs.length := by
  induction xs with
  | nil => simp [average]
  | cons x xs ih =>
    have step : average p xs (fun S => (2 : ℝ)^(insert x S).card) ≤ 2 * average p xs (fun S => (2 : ℝ)^S.card) := by
      rw [← average.scale]
      apply average.mono hp hp' xs
      intro S
      rw [mul_comm, ← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) (Finset.card_insert_le ..)
    simp only [average, List.length_cons, pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left step hp,
      mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+p by linarith)]

/-- Markov's bound discards trials on which the degree promise might fail. -/
theorem bad_probability {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (xs : List V) (D : ℕ) :
    average p xs (fun S => bit (D ≤ S.card)) ≤ (1+p)^xs.length / 2^D := by
  have h : average p xs (fun S => bit (D ≤ S.card)) ≤
      (2^D : ℝ)⁻¹ * average p xs (fun S => (2 : ℝ)^S.card) := by
    rw [← average.scale]
    apply average.mono hp hp' xs
    intro S
    by_cases hs : D ≤ S.card
    · rw [bit_pos hs, ← div_eq_inv_mul]
      exact (one_le_div₀ (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) hs)
    · rw [bit_neg hs]; positivity
  rw [div_eq_inv_mul]
  exact h.trans (mul_le_mul_of_nonneg_left (size_moment hp hp' xs) (by positivity))

end MISQueries

namespace MISQueries

/-- With k spare vertices the chance of seeing a blocker dominates this exponential.
The quadratic bound makes the charge summable over the pairs inside one query. -/
theorem hit_ge_exp {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1) {k : ℕ} (hk : 0 < k) :
    Real.exp (-(4 / (p * k)^2)) ≤ 1 - (1-p)^k := by
  let r := p * k
  have hr : 0 < r := mul_pos hp (by exact_mod_cast hk)
  have hpow : (1-p)^k ≤ Real.exp (-r) := by
    calc
      _ ≤ (Real.exp (-p)) ^ k := by
        apply pow_le_pow_left₀ (sub_nonneg.mpr hp') _ _
        linarith [Real.add_one_le_exp (-p)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; dsimp [r]; ring
  have hE : 1 < Real.exp r := Real.one_lt_exp_iff.mpr hr
  have hsq : r^2/4 ≤ Real.exp r - 1 := by
    have he : 1 + r/2 ≤ Real.exp (r/2) := by linarith [Real.add_one_le_exp (r/2)]
    have he2 := pow_le_pow_left₀ (show 0 ≤ 1+r/2 by linarith) he 2
    rw [sq (Real.exp _), ← Real.exp_add, show r/2+r/2 = r by ring] at he2
    nlinarith only [he2, hr]
  have hrec : 1/(Real.exp r-1) ≤ 4/r^2 := by
    apply (div_le_div_iff₀ (by linarith) (sq_pos_of_pos hr)).mpr
    nlinarith only [hsq]
  have hbase : 0 < 1-Real.exp (-r) := by rw [Real.exp_neg]; exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hE)
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
  rw [Real.log_inv] at hlog
  have hid : (1-Real.exp (-r))⁻¹ - 1 = 1/(Real.exp r-1) := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos r), ne_of_gt (sub_pos.mpr hE)]
    ring
  rw [hid] at hlog
  calc
    _ ≤ Real.exp (Real.log (1-Real.exp (-r))) := by
      apply Real.exp_le_exp.mpr
      change -(4/r^2) ≤ _
      linarith
    _ = 1-Real.exp (-r) := Real.exp_log hbase
    _ ≤ 1-(1-p)^k := sub_le_sub_left hpow _

/-- Charge paid by an included pair in a query. Queries of size two are removed
before applying this bound. -/
noncomputable def charge (p : ℝ) (q : ℕ) : ℝ := 4/(p*(q-2 : ℕ))^2

theorem charge_nonneg (p : ℝ) (q : ℕ) : 0 ≤ charge p q := by unfold charge; positivity

theorem real_choose_two (n : ℕ) : 2*(n.choose 2 : ℝ) = n*(n-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show (n+1).choose 2 = n.choose 1 + n.choose 2 from Nat.choose_succ_succ ..,
      Nat.choose_one_right, Nat.cast_add, Nat.cast_succ]
    linarith only [ih]

theorem paid_per_query {p : ℝ} (hp : 0 < p) {q : ℕ} (hq : 3 ≤ q) :
    (q.choose 2 : ℝ) * charge p q ≤ 36 / p^2 := by
  let k := q-2
  have hk : (0:ℝ) < k := by exact_mod_cast (show 0 < k by dsimp [k]; omega)
  have hqk : (q:ℝ) ≤ 3*k := by exact_mod_cast (show q ≤ 3*k by dsimp [k]; omega)
  have hsq := pow_le_pow_left₀ (show 0 ≤ (q:ℝ) by positivity) hqk 2
  have hc := real_choose_two q
  have hq0 : 0 ≤ (q:ℝ) := by positivity
  unfold charge
  change (q.choose 2 : ℝ) * (4/(p*k)^2) ≤ 36 / p^2
  field_simp [ne_of_gt hp, ne_of_gt hk]
  nlinarith only [hc,hsq,hq0,sq_nonneg (k:ℝ)]

end MISQueries

namespace MISQueries

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def miss (Q : Fin t → Finset V) (e S : Finset V) : Prop := ∀ i, ¬e ⊆ Q i ∨ ¬Disjoint S (Q i \ e)

noncomputable def cost (p : ℝ) (Q : Fin t → Finset V) (e : Finset V) : ℝ :=
  ∑ i, if e ⊆ Q i then charge p (Q i).card else 0

/-- All unordered pairs, and those left over after removing explicit pair queries. -/
def pairs (V : Type*) [Fintype V] : Finset (Finset V) := Finset.univ.powersetCard 2

def remaining (Q : Fin t → Finset V) : Finset (Finset V) := pairs V \ Finset.univ.image Q

omit [DecidableEq V] in
theorem pair_mem {e : Finset V} : e ∈ pairs V ↔ e.card = 2 := by simp [pairs]

theorem product_bits {I : Type*} (T : Finset I) (P : I → Prop) :
    ∏ i ∈ T, bit (P i) = bit (∀ i ∈ T, P i) := by
  classical
  induction T using Finset.induction with
  | empty => simp [bit]
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, ih, Finset.forall_mem_insert]
    by_cases ha : P i <;> by_cases hb : ∀ j ∈ T, P j <;> simp [ha,hb,bit]

theorem miss_for_pair {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1) (Q : Fin t → Finset V)
    {e : Finset V} (he : e ∈ remaining Q) :
    Real.exp (-cost p Q e) ≤ average p Finset.univ.toList (fun S => bit (miss Q e S)) := by
  classical
  have hec := pair_mem.mp (Finset.mem_sdiff.mp he).1
  have hne (i : Fin t) : Q i ≠ e := fun h => (Finset.mem_sdiff.mp he).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h⟩)
  let F (i : Fin t) (S : Finset V) := bit (¬e ⊆ Q i ∨ ¬Disjoint S (Q i \ e))
  have hm (i : Fin t) : Monotone (F i) := by
    intro S T hST
    exact bit_mono (Or.imp id (fun hdis d => hdis (d.mono_left hST)))
  have hprod := average.harris_prod hp.le hp' Finset.univ.toList Finset.univ F hm (fun _ _ => bit_nonneg _)
  have ident (S : Finset V) : ∏ i, F i S = bit (miss Q e S) := by
    rw [show (∏ i, F i S) = _ from product_bits Finset.univ _]
    simp [miss]
  simp_rw [ident] at hprod
  apply le_trans _ hprod
  rw [cost, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
  intro i _
  by_cases hsub : e ⊆ Q i
  · have hcard : 2 < (Q i).card := hec ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, (hne i).symm⟩)
    simp only [hsub, ite_true, F, not_true_eq_false, false_or, charge]
    rw [hit_probability, Finset.card_sdiff_of_subset hsub, hec]
    exact hit_ge_exp hp hp' (by omega)
  · simp [F, hsub, average.const]

theorem remaining_card (Q : Fin t → Finset V) : (pairs V).card ≤ (remaining Q).card + t := by
  classical
  have sub : pairs V ⊆ remaining Q ∪ Finset.univ.image Q := by
    intro e he
    by_cases h : e ∈ Finset.univ.image Q
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_union_le (remaining Q) (Finset.univ.image Q)
  have h3 : (Finset.univ.image Q).card ≤ t := by simpa using (Finset.card_image_le (f := Q) (s := Finset.univ))
  omega

theorem cost_sum {p : ℝ} (hp : 0 < p) (Q : Fin t → Finset V) :
    (∑ e ∈ remaining Q, cost p Q e) ≤ t * (36/p^2) := by
  classical
  unfold cost
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : Fin t, (36/p^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      let E := (remaining Q).filter fun e => e ⊆ Q i
      have hsub : E ⊆ (Q i).powersetCard 2 := by
        intro e he
        obtain ⟨he,hq⟩ := Finset.mem_filter.mp he
        exact Finset.mem_powersetCard.mpr ⟨hq,pair_mem.mp (Finset.mem_sdiff.mp he).1⟩
      have hc : E.card ≤ (Q i).card.choose 2 := by simpa only [Finset.card_powersetCard] using Finset.card_le_card hsub
      have hc' : (E.card : ℝ) ≤ ((Q i).card.choose 2 : ℝ) := by exact_mod_cast hc
      apply (mul_le_mul_of_nonneg_right hc' (charge_nonneg p (Q i).card)).trans
      by_cases h : 3 ≤ (Q i).card
      · exact paid_per_query hp h
      · have hz : (Q i).card - 2 = 0 := by omega
        simp only [charge, hz, Nat.cast_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), div_zero, mul_zero]
        positivity
    _ = _ := by simp

end MISQueries

namespace MISQueries

/-- The source uses independent blockers with this sampling probability. -/
noncomputable def rate (n D : ℕ) : ℝ := D / (4*n)
noncomputable def exponent (t D : ℕ) : ℝ := 4608*t/(D:ℝ)^2

theorem rate_pos {n D : ℕ} (hn : 0<n) (hd : 0<D) : 0 < rate n D := by unfold rate; positivity

theorem rate_le_one {n D : ℕ} (hn : 0<n) (hd : D ≤ n) : rate n D ≤ 1 := by
  unfold rate
  apply (div_le_one (by positivity)).mpr
  have h : (D:ℝ) ≤ n := by exact_mod_cast hd
  linarith

theorem pair_count (n : ℕ) : (pairs (Fin n)).card = n.choose 2 := by simp [pairs]

/-- Sum the supporting tangent to exp at the negative mean charge. -/
theorem exp_sum_lower {I : Type*} (T : Finset I) (f : I → ℝ) (m : ℝ)
    (h : ∑ x ∈ T, f x ≤ T.card * m) : T.card * Real.exp (-m) ≤ ∑ x ∈ T, Real.exp (-f x) := by
  have hx (x : I) : Real.exp (-m)*(1+m - f x) ≤ Real.exp (-f x) := by
    rw [show -f x = -m+(m-f x) by ring, Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith only [Real.add_one_le_exp (m-f x)]
  apply le_trans _ (Finset.sum_le_sum (fun x _ => hx x))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  nlinarith only [mul_nonneg (Real.exp_pos (-m)).le (sub_nonneg.mpr h)]

/-- Every fixed schedule misses a uniformly hidden pair with probability at least
one half of exp(-4608 t / Δ²), before discarding over-degree blocker samples. -/
theorem schedule_bound {n D t : ℕ} (hn : 2 ≤ n) (hd : 0 < D) (hdn : D ≤ n)
    (ht : 2*t ≤ n.choose 2) (Q : Fin t → Finset (Fin n)) :
    ((n.choose 2:ℝ)/2)*Real.exp (-exponent t D) ≤
      ∑ e ∈ pairs (Fin n), average (rate n D) Finset.univ.toList (fun S => bit (miss Q e S)) := by
  classical
  let R := remaining Q
  have hsurv := remaining_card Q
  rw [pair_count] at hsurv
  have hN : n.choose 2 ≤ 2*R.card := by dsimp [R]; omega
  have hNr : (n.choose 2 : ℝ) ≤ 2*R.card := by exact_mod_cast hN
  have hnn : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hcap : (n:ℝ)^2 ≤ 8*R.card := by nlinarith only [real_choose_two n,hNr,mul_nonneg (show 0 ≤ (n:ℝ) by positivity) (sub_nonneg.mpr hnn)]
  have hp := rate_pos (n:=n) (by omega) hd
  have hp' := rate_le_one (n:=n) (by omega) hdn
  have hb : (∑ e ∈ R, cost (rate n D) Q e) ≤ R.card * exponent t D := by
    apply (cost_sum hp Q).trans
    unfold rate exponent
    field_simp [ne_of_gt (show (0:ℝ)<D by exact_mod_cast hd),ne_of_gt (show (0:ℝ)<n by positivity)]
    nlinarith only [mul_nonneg (show 0 ≤ (t:ℝ) by positivity) (sub_nonneg.mpr hcap)]
  have hpart := exp_sum_lower R (cost (rate n D) Q) (exponent t D) hb
  calc
    _ ≤ R.card * Real.exp (-exponent t D) := mul_le_mul_of_nonneg_right (by linarith only [hNr]) (Real.exp_pos _).le
    _ ≤ _ := hpart
    _ ≤ ∑ e ∈ R, average (rate n D) Finset.univ.toList (fun S => bit (miss Q e S)) :=
      Finset.sum_le_sum (fun e he => miss_for_pair hp hp' Q he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun _ _ _ => average.nonneg hp.le hp' _ (fun _ => bit_nonneg _))

/-- With p = Δ/(4n), the discarded degree tail is at most exp(-Δ/4). -/
theorem degree_tail {n D : ℕ} (hn : 0<n) (hd : 0 < D) (hdn : D ≤ n) :
    average (rate n D) (Finset.univ : Finset (Fin n)).toList (fun S => bit (D ≤ S.card)) ≤
      Real.exp (-(D:ℝ)/4) := by
  let p := rate n D
  have hp : 0 ≤ p := (rate_pos hn hd).le
  have hb := bad_probability hp (rate_le_one hn hdn) (Finset.univ : Finset (Fin n)).toList D
  simp only [Finset.length_toList, Finset.card_univ, Fintype.card_fin] at hb
  apply hb.trans
  have hbase : 1+p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have up := pow_le_pow_left₀ (show 0 ≤ 1+p by linarith) hbase n
  rw [←Real.exp_nat_mul] at up
  have hnz : (n:ℝ) ≠ 0 := by positivity
  have hpval : (n:ℝ)*p = D/4 := by dsimp [p,rate]; field_simp
  rw [hpval] at up
  have hlog : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hlo : Real.exp ((D:ℝ)/2) ≤ (2:ℝ)^D := by
    calc
      _ ≤ Real.exp ((D:ℝ)*Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg (show 0 ≤ (D:ℝ) by positivity) (sub_nonneg.mpr hlog)]
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  apply le_trans (div_le_div₀ (Real.exp_pos _).le up (Real.exp_pos _) hlo)
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

end MISQueries

namespace MISQueries

/-- Average over the algorithm's coins for this fixed hidden pair and blockers.
If the degree bound holds, a missed pair forces an error on at least one of
the two bits for the two *fixed* legal oracles. -/
theorem ambiguity {n D t : ℕ} (w : Strategy n t → ℝ) (hw : Distribution w) {ε : ℝ}
    (hε : 0 ≤ ε) (learns : Learns w D ε) {e : Finset (Fin n)} (he : e.card = 2) (S : Finset (Fin n)) :
    (∑ s, w s * bit (miss s.1 e S)) ≤ 2*ε + bit (D ≤ S.card) := by
  classical
  by_cases hv : S.card < D
  · rw [bit_neg (not_le.mpr hv), add_zero]
    let B := S \ e
    have hb : B.card < D := (Finset.card_le_card Finset.sdiff_subset).trans_lt hv
    have hd : Disjoint e B := Finset.disjoint_sdiff
    obtain ⟨O,hO,agree⟩ := coupled_oracles he hd
    let G := hidden e B
    let loss (s : Strategy n t) (k : Bool) : ℝ := if s.2 (fun i => O k (s.1 i)) = G k then 0 else 1
    have upper (k : Bool) : (∑ s, w s * loss s k) ≤ ε := learns (G k) (hidden_degree he hb k) (O k) (hO k)
    have inevitable (s : Strategy n t) : bit (miss s.1 e S) ≤ loss s false + loss s true := by
      by_cases hm : miss s.1 e S
      · rw [bit_pos hm]
        have hans : (fun i => O false (s.1 i)) = (fun i => O true (s.1 i)) := by
          funext i
          apply agree
          rcases hm i with h | h
          · exact .inl h
          · obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp h
            exact .inr (Finset.not_disjoint_iff.mpr ⟨x,(Finset.mem_sdiff.mp hy).1,Finset.mem_sdiff.mpr ⟨hx,(Finset.mem_sdiff.mp hy).2⟩⟩)
        have hgraph : G false ≠ G true := hidden_distinct he B
        simp only [loss, hans]
        split_ifs with h₁ h₂ <;> norm_num
        exact hgraph (h₁.symm.trans h₂)
      · rw [bit_neg hm]
        unfold loss
        split_ifs <;> norm_num
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => mul_le_mul_of_nonneg_left (inevitable s) (hw.1 s))
    simp_rw [mul_add, Finset.sum_add_distrib] at hsum
    linarith only [hsum,upper false,upper true]
  · rw [bit_pos (Nat.le_of_not_gt hv)]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => mul_le_mul_of_nonneg_left (bit_le_one (miss s.1 e S)) (hw.1 s))
    simpa only [mul_one,hw.2] using hsum.trans (show (∑ s, w s * 1) ≤ 2*ε+1 by simp [hw.2,hε])

end MISQueries

namespace MISQueries

/-- The hidden-pair lower bound from the draft, with absolute constants. It
holds for any distribution on all deterministic nonadaptive schedules and
answer decoders, uniformly over every legal maximal-independent-set oracle. -/
theorem randomized_lower {n D t : ℕ} (hn : 2 ≤ n) (hd : 0 < D) (hdn : D ≤ n-1)
    (ht : 2*t ≤ n.choose 2) (w : Strategy n t → ℝ) (hw : Distribution w) {ε : ℝ}
    (hε : 0 ≤ ε) (learns : Learns w D ε) :
    Real.exp (-(4608*t/(D:ℝ)^2))/4 - Real.exp (-(D:ℝ)/4) ≤ ε := by
  classical
  let E := pairs (Fin n)
  let xs := (Finset.univ : Finset (Fin n)).toList
  let p := rate n D
  let m := exponent t D
  have hp := (rate_pos (n:=n) (by omega) hd).le
  have hp' := rate_le_one (n:=n) (by omega) (show D ≤ n by omega)
  have he (e : Finset (Fin n)) (he : e ∈ E) :
      average p xs (fun S => ∑ s, w s * bit (miss s.1 e S)) ≤ 2*ε + Real.exp (-(D:ℝ)/4) := by
    apply (average.mono hp hp' xs (ambiguity w hw hε learns (pair_mem.mp he))).trans
    rw [average.add, average.const]
    exact add_le_add le_rfl (degree_tail (n := n) (by omega) hd (by omega))
  have hsub (s : Strategy n t) : (n.choose 2 : ℝ)/2 * Real.exp (-m) ≤
      ∑ e ∈ E, average p xs (fun S => bit (miss s.1 e S)) := schedule_bound hn hd (by omega) ht _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => mul_le_mul_of_nonneg_left (hsub s) (hw.1 s))
  rw [← Finset.sum_mul, hw.2, one_mul] at hsum
  simp_rw [Finset.mul_sum] at hsum
  rw [Finset.sum_comm] at hsum
  have hupper := Finset.sum_le_sum he
  simp_rw [average.sum, average.scale] at hupper
  have hraw := hsum.trans hupper
  rw [Finset.sum_const, nsmul_eq_mul, show E.card = n.choose 2 from pair_count n] at hraw
  have hN : (0:ℝ) < n.choose 2 := by exact_mod_cast (Nat.choose_pos hn)
  have htmp : (n.choose 2:ℝ)*(Real.exp (-m)/2) ≤ (n.choose 2:ℝ)*(2*ε+Real.exp (-(D:ℝ)/4)) := by linarith only [hraw]
  have hdiv := (mul_le_mul_iff_right₀ hN).mp htmp
  change Real.exp (-m)/4 - Real.exp (-(D:ℝ)/4) ≤ ε
  linarith only [hdiv, Real.exp_pos (-(D:ℝ)/4)]

end MISQueries

namespace MISQueries

/-- The dense lower estimate gives a direct finite obstruction at every inverse
polynomial failure level. -/
theorem confidence_obstruction {n D t : ℕ} (hn : 2 ≤ n) (hd : 0 < D) (hdn : D ≤ n-1)
    (ht : 2*t ≤ n.choose 2) (a : ℝ) (size : 4*(a*Real.log n) ≤ D)
    (gap : exponent t D + Real.log 8 < a*Real.log n) (w : Strategy n t → ℝ) (hw : Distribution w) :
    ¬Learns w D ((n:ℝ)^(-a)) := by
  intro h
  let z := a*Real.log n
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n:ℝ)^(-a) = Real.exp (-z) := by rw [Real.rpow_def_of_pos hn']; congr 1; dsimp [z]; ring
  have hbound := randomized_lower hn hd hdn ht w hw (Real.rpow_nonneg hn'.le _) h
  rw [he] at hbound
  have htail : Real.exp (-(D:ℝ)/4) ≤ Real.exp (-z) := Real.exp_le_exp.mpr (by dsimp [z]; linarith only [size])
  have hstrict := Real.exp_lt_exp.mpr (show Real.log 8 + -z < -exponent t D by dsimp [z]; linarith only [gap])
  rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<8)] at hstrict
  change Real.exp (-exponent t D)/4 - _ ≤ Real.exp (-z) at hbound
  linarith

theorem square_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith only [ih, hk, Nat.mul_le_mul_left k hk]

theorem log_two_bounds : (1:ℝ)/2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  · linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

/-- Negative answer to Michel and Scott's high-confidence question. For any
fixed coefficient and any positive inverse-polynomial exponent, arbitrarily
large labeled graphs violate the proposed Δ² log(n/Δ) nonadaptive query bound. -/
theorem no_log_ratio_bound (a : ℝ) (ha : 0 < a) (C n₀ : ℕ) :
    ∃ n D : ℕ, n₀ ≤ n ∧ 2 ≤ n ∧ 0 < D ∧ D ≤ n-1 ∧
      ∀ (t : ℕ), t ≤ C * D^2 * Nat.log 2 (n/D) →
        ∀ w : Strategy n t → ℝ, Distribution w → ¬Learns w D ((n:ℝ)^(-a)) := by
  let k := C+4
  obtain ⟨m,hm⟩ := exists_nat_gt (max (max (max (k:ℝ) n₀) (8*a)) (2*(4608*C*k+4)/a))
  have hm₁ : (k:ℝ) < m := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hm))
  have hm₂ : (n₀:ℝ) < m := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hm))
  have hm₃ : 8*a < m := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hm)
  have hm₄ : 2*(4608*C*k+4) < (m:ℝ)*a := (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hm)
  have hkm : k < m := by exact_mod_cast hm₁
  have hk : 4 ≤ k := by dsimp [k]; omega
  let D := 2^m
  let r := 2^k
  let n := D*r
  have hd : 0 < D := by dsimp [D]; positivity
  have hr : 2 ≤ r := by dsimp [r]; exact (by decide : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hn : 2 ≤ n := by dsimp [n]; nlinarith only [hd,hr,Nat.mul_le_mul_left D hr]
  have hdn : D ≤ n-1 := by dsimp [n]; have := Nat.mul_le_mul_left D hr; omega
  have hn₀ : n₀ ≤ n := by
    have h₀ : n₀ < m := by exact_mod_cast hm₂
    have h₁ : m < D := Nat.lt_two_pow_self
    omega
  refine ⟨n,D,hn₀,hn,hd,hdn,?_⟩
  intro t ht w hw
  have hratio : Nat.log 2 (n/D) = k := by simp [n, D, r, Nat.log_pow]
  rw [hratio] at ht
  have hnr : (n:ℝ) = (D:ℝ)*r := by dsimp [n]; push_cast; rfl
  have hc : (C:ℝ) ≤ k := by exact_mod_cast (show C ≤ k by dsimp [k]; omega)
  have hkr : (4:ℝ)*k ≤ r := by
    have hh : k^2 ≤ r := square_le_two_pow hk
    exact_mod_cast (show 4*k ≤ r by nlinarith only [hh,Nat.mul_le_mul_right k hk])
  have htr : (t:ℝ) ≤ C*(D:ℝ)^2*k := by exact_mod_cast ht
  have hcap : 2*t ≤ n.choose 2 := by
    have hrr : 8*(C:ℝ)*k ≤ (r:ℝ)^2 := by
      have hks : 0 ≤ (k:ℝ) := by positivity
      nlinarith only [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*k) hkr 2, mul_nonneg (sub_nonneg.mpr hc) hks, sq_nonneg (k:ℝ)]
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hnlo : (n:ℝ)^2 ≤ 4*(n.choose 2:ℝ) := by
      nlinarith only [real_choose_two n, mul_nonneg (by positivity : 0 ≤ (n:ℝ)) (sub_nonneg.mpr hn')]
    rw [hnr] at hnlo
    have hcap' : 2*(t:ℝ) ≤ (n.choose 2:ℝ) := by nlinarith only [htr,hnlo,mul_nonneg (sq_nonneg (D:ℝ)) (sub_nonneg.mpr hrr)]
    exact_mod_cast hcap'
  have hl : Real.log (n:ℝ) = ((m:ℝ)+k)*Real.log 2 := by
    dsimp [n,D,r]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  apply confidence_obstruction hn hd hdn hcap a _ _ w hw
  · have hlog : Real.log (n:ℝ) ≤ 2*m := by rw [hl]; nlinarith only [hm₁, mul_nonneg (by positivity : 0 ≤ (m:ℝ)+k) (sub_nonneg.mpr log_two_bounds.2)]
    have hdlarge : m^2 ≤ D := square_le_two_pow (by omega)
    have hdr : (m:ℝ)^2 ≤ D := by exact_mod_cast hdlarge
    nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hlog), mul_nonneg (show 0 ≤ (m:ℝ) by positivity) (sub_nonneg.mpr hm₃.le), hdr]
  · have hex : exponent t D ≤ 4608*C*k := by
      unfold exponent
      apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hd))).mpr
      linarith only [htr]
    have hl₈ : Real.log 8 ≤ 3 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
      norm_num1
      linarith only [log_two_bounds.2]
    have hlm : (m:ℝ)/2 ≤ Real.log n := by
      rw [hl]
      nlinarith only [mul_nonneg (show 0 ≤ (m:ℝ) by positivity) (sub_nonneg.mpr log_two_bounds.1),
        mul_nonneg (show 0 ≤ (k:ℝ) by positivity) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
    nlinarith only [hm₄, hex, hl₈, mul_nonneg ha.le (sub_nonneg.mpr hlm)]

end MISQueries
