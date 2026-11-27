module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace SymmetricERM

abbrev Point (B r : ℕ) := Fin B × Fin r
abbrev Label (r : ℕ) := Finset (Fin r)
abbrev Code (B r : ℕ) := Equiv.Perm (Label r) × (Fin B → Label r)
abbrev Sample (B r m : ℕ) := Fin m → Point B r × Label r
abbrev Learner (B r : ℕ) := (m : ℕ) → Sample B r m → Code B r

/-- Points of a mask carry its code, and the other points carry the empty code.
One permutation relabels all blocks at once. -/
def classify {B r} (c : Code B r) (x : Point B r) : Label r :=
  c.1 (if x.2 ∈ c.2 x.1 then c.2 x.1 else ∅)

def mistakes {B r m} (c : Code B r) (s : Sample B r m) : ℕ :=
  (Finset.univ.filter fun i => classify c (s i).1 ≠ (s i).2).card

def ERM {B r} (A : Learner B r) : Prop :=
  ∀ m s c, mistakes (A m s) s ≤ mistakes c s

def Symmetric (B r : ℕ) : Prop :=
  ∀ (e : Equiv.Perm (Label r)) (c : Code B r), ∃ c', ∀ x, classify c' x = e (classify c x)

def NShatters {B r} (S : Finset (Point B r)) : Prop :=
  ∃ f g : Point B r → Label r, (∀ x ∈ S, f x ≠ g x) ∧
    ∀ T ⊆ S, ∃ c : Code B r, ∀ x ∈ S,
      classify c x = if x ∈ T then f x else g x

noncomputable def dimension (B r : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (@NShatters B r)).sup Finset.card

def Law {X : Type} [Fintype X] (p : X → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

noncomputable def risk {B r} (p : Point B r → ℝ) (t c : Code B r) : ℝ :=
  ∑ x, if classify c x = classify t x then 0 else p x

/-- Failure probability at error 1/4 under an ordered sample of independent draws. -/
noncomputable def failure {B r} (A : Learner B r) (m : ℕ) (p : Point B r → ℝ)
    (t : Code B r) : ℝ := by
  classical
  exact ∑ xs : Fin m → Point B r, if (1/4 : ℝ) <
    risk p t (A m (fun i => (xs i, classify t (xs i)))) then ∏ i, p (xs i) else 0

def Threshold {B r} (A : Learner B r) (n : ℕ) : Prop :=
  ∀ m ≥ n, ∀ p, Law p → ∀ t, failure A m p t ≤ 1/4

end SymmetricERM

namespace SymmetricERM

open scoped Classical

def emptyCode (B r : ℕ) : Code B r := (Equiv.refl _, fun _ => ∅)

theorem symmetry (B r : ℕ) : Symmetric B r :=
  fun e c => ⟨(c.1.trans e, c.2), fun _ => rfl⟩

def Fits {B r} {ι : Type} (c : Code B r) (s : ι → Point B r × Label r) : Prop :=
  ∀ i, classify c (s i).1 = (s i).2

theorem no_mistakes {B r m} {c : Code B r} {s : Sample B r m} :
    mistakes c s = 0 ↔ Fits c s := by
  classical
  simp [mistakes, Finset.filter_eq_empty_iff, Fits]

/-- A deterministic empirical minimizer, also defined on inconsistent samples. -/
noncomputable def minimizer {B r} (m : ℕ) (s : Sample B r m) : Code B r := by
  classical
  let h : ∃ n : ℕ, ∃ c : Code B r, mistakes c s = n :=
    ⟨_, emptyCode B r, rfl⟩
  exact (Nat.find_spec h).choose

theorem minimizer_erm {B r} : ERM (@minimizer B r) := by
  classical
  intro m s c
  let h : ∃ n : ℕ, ∃ c : Code B r, mistakes c s = n := ⟨_, emptyCode B r, rfl⟩
  exact (Nat.find_spec h).choose_spec.trans_le (Nat.find_min' h ⟨c, rfl⟩)

def Seen {B r} {ι : Type} (e : Equiv.Perm (Label r)) (s : ι → Point B r × Label r)
    (b : Fin B) (i : ι) : Prop := (s i).1.1 = b ∧ (s i).2 ≠ e ∅

/-- Each represented block keeps one observed nonbackground mask, with empty fallback. -/
noncomputable def decode {B r} {ι : Type} (e : Equiv.Perm (Label r))
    (s : ι → Point B r × Label r) : Code B r := by
  classical
  exact (e, fun b => if h : ∃ i, Seen e s b i then e.symm (s h.choose).2 else ∅)

theorem observed_mask {B r ι} {c : Code B r} {s : ι → Point B r × Label r}
    (hc : Fits c s) {i b} (h : Seen c.1 s b i) :
    c.1.symm (s i).2 = c.2 b := by
  obtain ⟨hb, hy⟩ := h
  rw [← hc i]
  unfold classify
  split
  · simp [hb]
  · rename_i hx
    exact (hy ((hc i).symm.trans (by simp [classify, hx]))).elim

theorem decoded_mask {B r ι} {c : Code B r} {s : ι → Point B r × Label r}
    (hc : Fits c s) (b : Fin B) :
    (decode c.1 s).2 b = if ∃ i, Seen c.1 s b i then c.2 b else ∅ := by
  classical
  by_cases h : ∃ i, Seen c.1 s b i
  · simpa [decode, h] using observed_mask hc h.choose_spec
  · simp [decode, h]

theorem decode_fits {B r ι} {c : Code B r} {s : ι → Point B r × Label r}
    (hc : Fits c s) : Fits (decode c.1 s) s := by
  classical
  intro i
  unfold classify
  rw [decoded_mask hc]
  by_cases h : ∃ j, Seen c.1 s (s i).1.1 j
  · simpa [h, decode, classify] using hc i
  · have hy : (s i).2 = c.1 ∅ := by
      by_contra hy
      exact h ⟨i, rfl, hy⟩
    simp [h, decode, hy]

noncomputable def good {B r} (m : ℕ) (s : Sample B r m) : Code B r := by
  classical
  exact if h : ∃ c, Fits c s then decode h.choose.1 s else minimizer m s

theorem good_erm {B r} : ERM (@good B r) := by
  classical
  intro m s c
  unfold good
  split
  · rename_i h
    rw [no_mistakes.mpr (decode_fits h.choose_spec)]
    exact Nat.zero_le _
  · exact minimizer_erm m s c

/-- The fit reconstructed on the whole sample is determined by at most one retained
labeled observation from each block. -/
theorem compressed {B r m} {s : Sample B r m} (hs : ∃ c, Fits c s) :
    ∃ e : Equiv.Perm (Label r), ∃ I : Finset (Fin m), I.card ≤ B ∧
      good m s = decode e (fun i : I => s i) := by
  classical
  let c := hs.choose
  have hc : Fits c s := hs.choose_spec
  let blocks := Finset.univ.filter fun b : Fin B => ∃ i, Seen c.1 s b i
  have rep (b : blocks) : ∃ i, Seen c.1 s b i :=
    (Finset.mem_filter.mp b.property).2
  let I := Finset.univ.image fun b : blocks => (rep b).choose
  have equivObs (b : Fin B) :
      (∃ i : Fin m, Seen c.1 s b i) ↔ (∃ i : I, Seen c.1 (fun j : I => s j) b i) := by
    constructor
    · intro h
      let b' : blocks := ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      exact ⟨⟨(rep b').choose, Finset.mem_image.mpr ⟨b', Finset.mem_univ _, rfl⟩⟩,
        (rep b').choose_spec⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, hi⟩
  refine ⟨c.1, I, (Finset.card_image_le.trans ?_), ?_⟩
  · simpa [blocks] using Finset.card_le_univ blocks
  · unfold good
    rw [dite_eq_left hs]
    apply Prod.ext
    · rfl
    funext b
    change (decode c.1 s).2 b = (decode c.1 (fun j : I => s j)).2 b
    rw [decoded_mask hc, decoded_mask (c := c) (s := fun j : I => s j) (fun i => hc i),
      equivObs b]

end SymmetricERM

namespace SymmetricERM

open scoped Classical

theorem dimension_bounds {B r : ℕ} (hr : 0 < r) : B ≤ dimension B r ∧ dimension B r ≤ B*r := by
  classical
  let z : Fin r := ⟨0, hr⟩
  let S := Finset.univ.image (fun b : Fin B => (b,z))
  have hs : NShatters S := by
    refine ⟨fun _ => {z}, fun _ => ∅, fun _ _ => by simp, ?_⟩
    intro T hT
    refine ⟨(Equiv.refl _, fun b => if (b,z) ∈ T then {z} else ∅), ?_⟩
    intro x hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases hb : (b,z) ∈ T <;> simp [classify, hb]
  constructor
  · have hcard : S.card = B := by
      rw [show S = _ from rfl, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
      simp
    apply hcard.ge.trans
    exact Finset.le_sup (s := Finset.univ.filter (@NShatters B r)) (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  · apply Finset.sup_le
    intro T _
    simpa using Finset.card_le_univ T

def unseen {B r m} (s : Sample B r m) (b : Fin B) : Label r :=
  Finset.univ.filter fun j => ∀ i, (s i).1 ≠ (b,j)

noncomputable def bad {B r} (m : ℕ) (s : Sample B r m) : Code B r := by
  classical
  exact if ∀ i, (s i).2 = ∅ then (Equiv.refl _, unseen s) else minimizer m s

theorem bad_unseen {B r m} {s : Sample B r m} (h : ∀ i, (s i).2 = ∅) (x : Point B r) :
    classify (bad m s) x ≠ ∅ ↔ ∀ i, (s i).1 ≠ x := by
  classical
  by_cases hx : ∀ i, (s i).1 ≠ x
  · have hj : x.2 ∈ unseen s x.1 := by simpa [unseen] using hx
    simpa [bad, h, classify, hj, hx] using Finset.ne_empty_of_mem hj
  · simp [bad, h, classify, unseen, hx]

theorem bad_erm {B r} : ERM (@bad B r) := by
  intro m s c
  by_cases h : ∀ i, (s i).2 = ∅
  · have hf : Fits (bad m s) s := by
      intro i
      rw [h i]
      by_contra hn
      exact (bad_unseen h _ |>.mp hn) i rfl
    rw [no_mistakes.mpr hf]
    exact Nat.zero_le _
  · simpa [bad, h] using minimizer_erm m s c

theorem sample_mass {X : Type} [Fintype X] {p : X → ℝ} (hp : Law p) {ι : Type}
    [Fintype ι] [DecidableEq ι] : (∑ xs : ι → X, ∏ i, p (xs i)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : ι) (x : X) => p x)]
  simp [hp.2]

/-- On the uniform law and constant background target, at most one point per draw
can cease to be an error; this holds for each sample, including repeated draws. -/
theorem bad_lower {B r m : ℕ} (hpos : 0 < B*r) (hm : 2*m ≤ B*r) :
    ∃ p, Law p ∧ ∃ t : Code B r, failure bad m p t = 1 := by
  classical
  let N := B*r
  let p := fun _ : Point B r => 1/(N : ℝ)
  let t := emptyCode B r
  have hN : (0 : ℝ) < N := by exact_mod_cast hpos
  have hn : Fintype.card (Point B r) = N := by simp [N]
  have hp : Law p := ⟨fun _ => by dsimp [p]; positivity, by simp [p, hn, ne_of_gt hN]⟩
  have hz (x : Point B r) : classify t x = ∅ := by simp [t, emptyCode, classify]
  have excessive (xs : Fin m → Point B r) :
      (1/4 : ℝ) < risk p t (bad m (fun i => (xs i, classify t (xs i)))) := by
    let seen := Finset.univ.image xs
    let s : Sample B r m := fun i => (xs i, classify t (xs i))
    have hs (i) : (s i).2 = ∅ := hz _
    have pointwise (x : Point B r) :
        classify (bad m s) x = classify t x ↔ x ∈ seen := by
      rw [hz]
      simpa [seen, s] using not_congr (bad_unseen hs x)
    have hcard : seen.card ≤ m := by simpa [seen] using Finset.card_image_le (s := Finset.univ) (f := xs)
    have nmiss : N ≤ 2 * seenᶜ.card := by
      rw [Finset.card_compl, hn]
      change 2 * m ≤ N at hm
      omega
    have hrisk : risk p t (bad m s) = seenᶜ.card / (N : ℝ) := by
      unfold risk
      simp_rw [pointwise]
      rw [Finset.sum_ite]
      have he : (Finset.univ.filter fun x => x ∉ seen) = seenᶜ := by ext; simp
      simp [he, p, div_eq_mul_inv]
    change (1/4 : ℝ) < risk p t (bad m s)
    rw [hrisk, lt_div_iff₀ hN]
    have : (N : ℝ) ≤ 2 * (seenᶜ.card : ℝ) := by exact_mod_cast nmiss
    linarith
  refine ⟨p, hp, t, ?_⟩
  unfold failure
  simp only [ite_eq_left (excessive _)]
  exact sample_mass hp

end SymmetricERM

namespace SymmetricERM

open scoped Classical

noncomputable def hit {B r} (p : Point B r → ℝ) (t c : Code B r) (x : Point B r) : ℝ :=
  if classify c x = classify t x then p x else 0

theorem hit_nonnegative {B r} {p : Point B r → ℝ} (hp : Law p) (t c x) : 0 ≤ hit p t c x := by
  unfold hit
  split <;> simp [hp.1]

theorem hit_risk {B r} {p : Point B r → ℝ} (hp : Law p) (t c : Code B r) :
    (∑ x, hit p t c x) + risk p t c = 1 := by
  unfold risk hit
  rw [← Finset.sum_add_distrib, ← hp.2]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp

/-- Independent retained draws determine the reconstruction; other coordinates must
agree with it. -/
noncomputable def reconstructionTerm {B r m} (I : Finset (Fin m)) (p : Point B r → ℝ)
    (t : Code B r) (D : (I → Point B r) → Code B r)
    (a : I → Point B r) (v : {i : Fin m // i ∉ I} → Point B r) : ℝ :=
  if (1/4 : ℝ) < risk p t (D a) then
    (∏ i, p (a i)) * ∏ j, hit p t (D a) (v j) else 0

theorem term_nonnegative {B r m} (I : Finset (Fin m)) {p : Point B r → ℝ}
    (hp : Law p) (t D a v) : 0 ≤ reconstructionTerm I p t D a v := by
  unfold reconstructionTerm
  split
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => hp.1 _)
      (Finset.prod_nonneg fun _ _ => hit_nonnegative hp _ _ _)
  · exact le_rfl

theorem term_sum_le {B r m} (I : Finset (Fin m)) {p : Point B r → ℝ}
    (hp : Law p) (t D) :
    (∑ xs : Fin m → Point B r,
      reconstructionTerm I p t D (fun i => xs i) (fun j => xs j))
      ≤ (3/4 : ℝ)^(m - I.card) := by
  classical
  let splitSample := Equiv.piEquivPiSubtypeProd (· ∈ I) (fun _ => Point B r)
  rw [show (∑ xs : Fin m → Point B r, reconstructionTerm I p t D
          (fun i => xs i) (fun j => xs j)) =
      ∑ a, ∑ v, reconstructionTerm I p t D a v from
    (splitSample.sum_comp (fun av => reconstructionTerm I p t D av.1 av.2)).trans
      (Fintype.sum_prod_type' _)]
  have n : Fintype.card {i : Fin m // i ∉ I} = m - I.card := by
    rw [Fintype.card_subtype_compl]; simp
  calc
    _ ≤ ∑ a : I → Point B r, (∏ i, p (a i)) * (3/4 : ℝ) ^ (m - I.card) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases h : (1/4 : ℝ) < risk p t (D a)
      · simp only [reconstructionTerm, ite_eq_left h, ← Finset.mul_sum]
        rw [← Fintype.prod_sum (fun (_ : {i : Fin m // i ∉ I}) x => hit p t (D a) x)]
        simp only [Finset.prod_const, Finset.card_univ, n]
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => hp.1 _)
        apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hit_nonnegative hp _ _ _)
        linarith [hit_risk hp t (D a)]
      · simp only [reconstructionTerm, ite_eq_right h, Finset.sum_const_zero]
        exact mul_nonneg (Finset.prod_nonneg fun _ _ => hp.1 _) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, sample_mass hp, one_mul]

def observe {B r} {ι : Type} (t : Code B r) (xs : ι → Point B r) :
    ι → Point B r × Label r := fun i => (xs i, classify t (xs i))

theorem erm_fits {B r m} {A : Learner B r} (hA : ERM A) (t : Code B r) (xs : Fin m → Point B r) :
    Fits (A m (observe t xs)) (observe t xs) := by
  apply no_mistakes.mp
  apply Nat.eq_zero_of_le_zero
  exact (hA m _ t).trans (no_mistakes.mpr (fun _ => rfl)).le

/-- Union over reconstructions from all permutations and at most B retained sample indices. -/
theorem compression_bound {B r m} {p : Point B r → ℝ} (hp : Law p) (t : Code B r) :
    failure good m p t ≤ (Fintype.card (Equiv.Perm (Label r)) : ℝ) *
      ∑ I : Finset (Fin m), if I.card ≤ B then (3/4 : ℝ) ^ (m - I.card) else 0 := by
  classical
  let term (e : Equiv.Perm (Label r)) (I : Finset (Fin m)) (xs : Fin m → Point B r) : ℝ :=
    if I.card ≤ B then reconstructionTerm I p t (fun a => decode e (observe t a))
      (fun i => xs i) (fun j => xs j) else 0
  have nonneg e I xs : 0 ≤ term e I xs := by
    unfold term; split
    · exact term_nonnegative _ hp _ _ _ _
    · exact le_rfl
  unfold failure
  calc
    _ ≤ ∑ xs : Fin m → Point B r, ∑ e : Equiv.Perm (Label r), ∑ I : Finset (Fin m), term e I xs := by
      apply Finset.sum_le_sum
      intro xs _
      let s := observe t xs
      change (if (1/4 : ℝ) < risk p t (good m s) then _ else _) ≤ _
      split
      · rename_i big
        obtain ⟨e, I, hI, hd⟩ := compressed (s := s) ⟨t, fun _ => rfl⟩
        have hh : Fits (good m s) s := erm_fits good_erm t xs
        have key : term e I xs = ∏ i, p (xs i) := by
          unfold term reconstructionTerm
          simp only [ite_eq_left hI]
          change (if 1/4 < risk p t (decode e (fun i : I => s i)) then _ else _) = _
          rw [← hd, ite_eq_left big]
          have each (j : {i : Fin m // i ∉ I}) :
              hit p t (good m s) (xs j) = p (xs j) := by
            exact ite_eq_left (hh j)
          change (∏ i : I, p (xs i)) *
            (∏ j : {i : Fin m // i ∉ I}, hit p t (decode e (fun i : I => s i)) (xs j)) = _
          rw [← hd]
          simp_rw [each]
          have instEq : Finset.Subtype.fintype I = Subtype.fintype (· ∈ I) :=
            Subsingleton.elim _ _
          rw [instEq]
          exact Fintype.prod_subtype_mul_prod_subtype (· ∈ I) (fun i => p (xs i))
        rw [← key]
        exact (Finset.single_le_sum (fun I _ => nonneg e I xs) (Finset.mem_univ I)).trans
          (Finset.single_le_sum (fun e' _ => Finset.sum_nonneg (fun I _ => nonneg e' I xs))
            (Finset.mem_univ e))
      · exact Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun I _ => nonneg e I xs))
    _ = ∑ e : Equiv.Perm (Label r), ∑ I : Finset (Fin m), ∑ xs : Fin m → Point B r, term e I xs := by
      rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (f := fun xs I => term _ I xs)]
    _ ≤ ∑ _e : Equiv.Perm (Label r), ∑ I : Finset (Fin m),
        if I.card ≤ B then (3/4 : ℝ)^(m-I.card) else 0 := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro I _
      by_cases h : I.card ≤ B
      · simpa [term, h] using term_sum_le I hp t (fun a => decode e (observe t a))
      · simp [term, h]
    _ = _ := by simp

end SymmetricERM

namespace SymmetricERM

open scoped Classical

/-- Paying a factor of eight per retained index lets the binomial theorem sum over
all index sets, without any rounding conventions for binomial-tail estimates. -/
theorem index_weight (B m : ℕ) :
    (∑ I : Finset (Fin m), if I.card ≤ B then (3/4 : ℝ) ^ (m - I.card) else 0)
      ≤ 8^B * (7/8 : ℝ)^m := by
  classical
  have expand :
      (∑ I : Finset (Fin m), (1/8 : ℝ)^I.card * (3/4 : ℝ)^(m-I.card)) = (7/8 : ℝ)^m := by
    simpa only [Finset.prod_const, Finset.card_univ, Finset.card_compl, Fintype.card_fin, show (1/8:ℝ) + 3/4 = 7/8 by norm_num] using
      (Fintype.prod_add (fun _ : Fin m => (1/8 : ℝ)) (fun _ => (3/4 : ℝ))).symm
  rw [← expand, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  by_cases h : I.card ≤ B
  · rw [ite_eq_left h, ← mul_assoc]
    apply le_mul_of_one_le_left (by positivity)
    have hi : (1 : ℝ) = 8^I.card * (1/8 : ℝ)^I.card := by rw [← mul_pow]; norm_num
    exact hi.le.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (by positivity))
  · rw [ite_eq_right h]
    positivity

theorem perm_count (r : ℕ) :
    Fintype.card (Equiv.Perm (Label r)) ≤ 2^(4^r) := by
  rw [Fintype.card_perm, Fintype.card_finset, Fintype.card_fin]
  apply (Nat.factorial_le_pow _).trans
  rw [← Nat.pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  calc
    r * 2^r ≤ 2^r * 2^r := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
    _ = 4^r := by rw [← Nat.mul_pow]

theorem good_upper (r : ℕ) : Threshold (@good (4^r) r) (64 * 4^r) := by
  intro m hm p hp t
  let B := 4^r
  have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
  calc
    _ ≤ _ := compression_bound hp t
    _ ≤ ((2 : ℝ)^B) * (8^B * (7/8 : ℝ)^m) := by
      apply mul_le_mul _ (index_weight _ _) _ (by positivity)
      · exact_mod_cast perm_count r
      · apply Finset.sum_nonneg
        intro I _
        split <;> positivity
    _ ≤ 2^B * (8^B * (7/8 : ℝ)^(64 * B)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ = (16 * (7/8 : ℝ)^64)^B := by rw [pow_mul, mul_pow, ← mul_assoc, ← mul_pow]; norm_num
    _ ≤ (1/4 : ℝ)^B := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ ≤ 1/4 := by simpa using (pow_le_pow_of_le_one (a := (1/4 : ℝ)) (by norm_num) (by norm_num) hB)

end SymmetricERM

namespace SymmetricERM

open scoped Classical

/-- Every empirical minimizer on this finite class has a finite distribution-free
threshold. Thus the separation compares ordinary sample complexities. -/
theorem finite_threshold {B r} {A : Learner B r} (hA : ERM A) :
    ∃ n : ℕ, Threshold A n := by
  classical
  let C := Fintype.card (Code B r)
  have hC : (0 : ℝ) < C := by
    have : 0 < C := @Fintype.card_pos_iff (Code B r) _ |>.mpr ⟨emptyCode B r⟩
    exact_mod_cast this
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1/4 / C by positivity)
    (show (3/4:ℝ) < 1 by norm_num)
  refine ⟨n, ?_⟩
  intro m hm p hp t
  let mass (c : Code B r) (xs : Fin m → Point B r) : ℝ :=
    if (1/4:ℝ) < risk p t c then ∏ i, hit p t c (xs i) else 0
  have nonneg c xs : 0 ≤ mass c xs := by unfold mass; split <;>
    first | exact Finset.prod_nonneg fun _ _ => hit_nonnegative hp _ _ _ | exact le_rfl
  unfold failure
  calc
    _ ≤ ∑ xs : Fin m → Point B r, ∑ c : Code B r, mass c xs := by
      apply Finset.sum_le_sum
      intro xs _
      let c := A m (observe t xs)
      change (if (1/4:ℝ) < risk p t c then _ else _) ≤ _
      split
      · rename_i h
        have he : mass c xs = ∏ i, p (xs i) := by
          have each (i) : hit p t c (xs i) = p (xs i) := ite_eq_left (erm_fits hA t xs i)
          simp only [mass, ite_eq_left h, each]
        exact he.ge.trans (Finset.single_le_sum
          (f := fun c' : Code B r => mass c' xs) (fun c' _ => nonneg c' xs) (Finset.mem_univ c))
      · exact Finset.sum_nonneg (fun _ _ => nonneg _ _)
    _ = ∑ c : Code B r, ∑ xs : Fin m → Point B r, mass c xs := Finset.sum_comm
    _ ≤ ∑ _c : Code B r, (3/4:ℝ)^m := by
      apply Finset.sum_le_sum
      intro c _
      by_cases h : (1/4:ℝ) < risk p t c
      · simp only [mass, ite_eq_left h]
        rw [← Fintype.sum_pow]
        apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hit_nonnegative hp _ _ _)
        linarith [hit_risk hp t c]
      · simp only [mass, ite_eq_right h, Finset.sum_const_zero]
        positivity
    _ = (3/4:ℝ)^m * C := by simp [C, mul_comm]
    _ ≤ 1/4 := by
      apply (le_div_iff₀ hC).mp
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm).trans hn.le

end SymmetricERM

namespace SymmetricERM

/-- The usual least finite realizable, distribution-free sample threshold for error
and failure probability one quarter. -/
def ExactThreshold {B r} (A : Learner B r) (n : ℕ) : Prop :=
  Threshold A n ∧ ∀ k, Threshold A k → n ≤ k

private theorem threshold_pos {B r} (hB : 0 < B) (hr : 0 < r) (A : Learner B r) :
    ¬Threshold A 0 := by
  classical
  intro h
  let z : Point B r := (⟨0,hB⟩, ⟨0,hr⟩)
  let c := A 0 (fun i => i.elim0)
  let u : Code B r := (Equiv.refl _, fun _ => {z.2})
  have hdis : ∃ t : Code B r, classify c z ≠ classify t z := by
    by_cases hv : classify c z = ∅
    · refine ⟨u, ?_⟩
      rw [hv]
      simp [u, classify]
    · exact ⟨emptyCode B r, by simpa [emptyCode, classify] using hv⟩
  obtain ⟨t, ht⟩ := hdis
  let p := fun x : Point B r => if x = z then (1:ℝ) else 0
  have hp : Law p := ⟨fun x => by dsimp [p]; split <;> norm_num, by simp [p]⟩
  have high : risk p t c = 1 := by
    unfold risk
    calc
      _ = ∑ x : Point B r, p x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = z
        · subst x; simp [ht]
        · simp [p, hx]
      _ = 1 := hp.2
  have eqc (xs : Fin 0 → Point B r) : A 0 (observe t xs) = c := by
    unfold c; congr 1; funext i; exact i.elim0
  have large (xs : Fin 0 → Point B r) : (1/4 : ℝ) < risk p t (A 0 (observe t xs)) := by
    rw [eqc, high]; norm_num
  have f : failure A 0 p t = 1 := by
    unfold failure
    change (∑ xs : Fin 0 → Point B r, if 1/4 < risk p t (A 0 (observe t xs)) then _ else _) = _
    simp only [ite_eq_left (large _)]
    exact sample_mass hp
  have hfail := h 0 le_rfl p hp t
  rw [f] at hfail
  norm_num at hfail

/-- Daniely–Sabato–Ben-David–Shalev-Shwartz's symmetric ERM gap at fixed error and
confidence 1/4. At parameter r the domain has 4^r blocks of r points. The two
proper deterministic ERMs have positive, least PAC sample thresholds g,b. Their
ratio b/g is at least log₂(d)/384, with d the actual Natarajan dimension rounded
by taking the integer logarithm. -/
theorem logarithmicGap (r : ℕ) (hr : 2 ≤ r) :
    let B := 4^r
    let d := dimension B r
    Symmetric B r ∧ B ≤ d ∧ d ≤ B*r ∧
      ∃ G H : Learner B r, ERM G ∧ ERM H ∧ ∃ g b : ℕ,
        ExactThreshold G g ∧ ExactThreshold H b ∧ 0 < g ∧
        g ≤ 64*B ∧ B*r < 2*b ∧ d.log2*g ≤ 384*b := by
  classical
  dsimp only
  let B := 4^r
  have hB : 0 < B := pow_pos (by decide) _
  have hr' : 0 < r := by omega
  obtain ⟨dlo, dhi⟩ := dimension_bounds (B := B) hr'
  let gex := finite_threshold (@good_erm B r)
  let bex := finite_threshold (@bad_erm B r)
  let g := Nat.find gex
  let b := Nat.find bex
  have hg : ExactThreshold (@good B r) g := ⟨Nat.find_spec gex, fun _ => Nat.find_min' gex⟩
  have hb : ExactThreshold (@bad B r) b := ⟨Nat.find_spec bex, fun _ => Nat.find_min' bex⟩
  have hgpos : 0 < g := by
    by_contra! hz
    exact threshold_pos hB hr' good (show Threshold _ 0 from (Nat.eq_zero_of_le_zero hz) ▸ hg.1)
  have hgle : g ≤ 64*B := hg.2 _ (good_upper r)
  have hbgt : B*r < 2*b := by
    by_contra! hm
    obtain ⟨p, hp, t, hf⟩ := bad_lower (Nat.mul_pos hB hr') hm
    have hfail := hb.1 b le_rfl p hp t
    rw [hf] at hfail
    norm_num at hfail
  have dlog : (dimension B r).log2 ≤ 3*r := by
    have hdpos := hB.trans_le dlo
    apply Nat.le_of_lt_succ
    apply (Nat.log2_lt hdpos.ne').mpr
    calc
      _ ≤ B*r := dhi
      _ ≤ B*2^r := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
      _ = 2^(3*r) := by dsimp [B]; rw [← Nat.mul_pow, Nat.pow_mul]
      _ < 2^(3*r+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨symmetry _ _, dlo, dhi, good, bad, good_erm, bad_erm, g, b, hg, hb, hgpos,
    hgle, hbgt, ?_⟩
  calc
    _ ≤ (3*r)*(64*B) := Nat.mul_le_mul dlog hgle
    _ = 192*(B*r) := by ring
    _ ≤ 192*(2*b) := Nat.mul_le_mul_left _ hbgt.le
    _ = 384*b := by ring

end SymmetricERM
