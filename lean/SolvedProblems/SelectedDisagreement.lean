module

public import SolvedProblems.SelectedSelector
public import SolvedProblems.SelectedSampling

public section

namespace SelectedDisagreement

private noncomputable def agree (t g : Hyp) (x : Point) : ℝ :=
  if label t x = label g x then 1 else 0

private theorem agreement_bound {p : Point → ℝ} (hp : Law p) {t g e} (he : bad p t g e) (k) :
    weight p k (agree t g) ≤ 1 - e := by
  obtain ⟨j, hj⟩ := he
  let n := max j k
  have ha := wlength hp.1 (f := agree t g)
    (fun x => by unfold agree; split <;> simp) (Nat.le_max_right j k)
  have hd := wlength hp.1 (f := miss t g)
    (fun x => by unfold miss; split <;> simp) (Nat.le_max_left j k)
  apply le_sub_iff_add_le.mpr
  calc
    _ ≤ weight p n (agree t g) + weight p n (miss t g) := add_le_add ha (le_trans hj.le hd)
    _ = weight p n (fun _ => 1) := by
      rw [← wadd]
      congr 1
      funext x
      by_cases h : label t x = label g x <;> simp [agree,miss,h]
    _ ≤ 1 := hp.2.1 _

private noncomputable def agreementProduct (t g : Hyp) : List Point → ℝ
  | [] => 1
  | x::s => agree t g x * agreementProduct t g s

private theorem agreementProduct_pos (t g s) : 0 ≤ agreementProduct t g s := by
  induction s with
  | nil => exact zero_le_one
  | cons x s ih => exact mul_nonneg (by unfold agree; split <;> simp) ih

private theorem agreementProduct_one {t g s} (h : ∀ x ∈ s, label g x = label t x) : agreementProduct t g s = 1 := by
  induction s with
  | nil => rfl
  | cons x s ih => simp [agreementProduct, agree, (h x (by simp)).symm, ih (fun y hy => h y (by simp [hy]))]

private theorem agreementProduct_iid (p : Point → ℝ) (k t g m) :
    iid p k m (agreementProduct t g) = (weight p k (agree t g)) ^ m := by
  induction m with
  | zero => simp [iid, agreementProduct]
  | succ m ih =>
    change weight p k (fun x => iid p k m (fun s => agree t g x * agreementProduct t g s)) = _
    simp only [iscale, ih, pow_succ]
    rw [← wscale]
    congr 1
    funext x
    exact mul_comm _ _

private noncomputable def badFit (p : Point → ℝ) (t g : Hyp) (e : ℝ) (s : List Point) : ℝ := by
  classical
  exact if bad p t g e then agreementProduct t g s else 0

private theorem badFit_pos (p t g e s) : 0 ≤ badFit p t g e s := by
  unfold badFit
  split
  · exact agreementProduct_pos _ _ _
  · exact le_rfl

private theorem zero_iid (p : Point → ℝ) (k m) : iid p k m (fun _ => 0) = 0 := by
  simpa using iscale p k m 0 (fun _ => 1)

private theorem fixed_bound {p : Point → ℝ} (hp : Law p) (t g e) (ee : e ≤ 1) (k m) :
    iid p k m (badFit p t g e) ≤ (1-e)^m := by
  classical
  by_cases h : bad p t g e
  · have eq : badFit p t g e = agreementProduct t g := by funext s; simp [badFit,h]
    rw [eq, agreementProduct_iid]
    exact pow_le_pow_left₀ (wpos hp.1 k (fun x => by unfold agree; split <;> simp))
      (agreement_bound hp h k) _
  · have eq : badFit p t g e = fun _ => 0 := by funext s; simp [badFit,h]
    rw [eq, zero_iid]
    exact pow_nonneg (sub_nonneg.mpr ee) _

private noncomputable def nominate (p : Point → ℝ) (t : Hyp) (e : ℝ) :
    Point → List Point → ℝ
  | .ordinary _ => fun _ => 0
  | .marker a => badFit p t (.named a) e

private theorem nominate_pos (p t e x s) : 0 ≤ nominate p t e x s := by
  cases x with
  | ordinary _ => exact le_rfl
  | marker a => exact badFit_pos p t (.named a) e s

private theorem bad_ne {p t g e} (h : bad p t g e) (he : 0 < e) : t ≠ g := by
  rintro rfl
  obtain ⟨k,hk⟩ := h
  have same : miss t t = fun _ => 0 := by funext x; simp [miss]
  rw [same,wconst,zero_mul] at hk
  exact (lt_asymm he hk)

private theorem envelope {p : Point → ℝ} (t : Hyp) {e : ℝ} (he : 0 < e) (s : List Point) :
    event p t e s ≤ (badFit p t .central e s + badFit p t .fallback e s) +
      nominations (nominate p t e) s := by
  classical
  have fits0 := (observe_fits _ _ _).mp
    (select_fits (observe t s) t ((observe_fits t t s).mpr (fun _ _ => rfl)))
  have hbase := add_nonneg (badFit_pos p t .central e s) (badFit_pos p t .fallback e s)
  have hn := nominations_nonneg (nominate_pos p t e) s
  unfold event
  split
  next h =>
    cases sel : select (observe t s) with
    | central =>
      rw [sel] at fits0 h
      have hc : badFit p t .central e s = 1 := by simp [badFit,h,agreementProduct_one fits0]
      rw [hc]
      exact le_trans (le_add_of_nonneg_right (badFit_pos ..)) (le_add_of_nonneg_right hn)
    | fallback =>
      rw [sel] at fits0 h
      have hf : badFit p t .fallback e s = 1 := by simp [badFit,h,agreementProduct_one fits0]
      rw [hf]
      exact le_trans (le_add_of_nonneg_left (badFit_pos ..)) (le_add_of_nonneg_right hn)
    | named a =>
      rw [sel] at fits0 h
      apply le_add_of_nonneg_of_le hbase
      apply nomination_mem (nominate_pos p t e) (named_marker sel (bad_ne h he))
      intro u hu
      have eq := agreementProduct_one (fun x hx => fits0 x (hu x hx))
      simp [nominate,badFit,h,eq]
  next _ => exact add_nonneg hbase hn

private theorem pac {p : Point → ℝ} (hp : Law p) (t m e) (hm : 1 ≤ m)
    (e0 : 0 < e) (e1 : e < 1) (k) :
    iid p k m (event p t e) ≤ 2*(1-e)^m + (m:ℝ)*(1-e)^(m-1) := by
  cases m with
  | zero => omega
  | succ m =>
    have qpos : 0 ≤ (1-e)^m := pow_nonneg (sub_nonneg.mpr e1.le) _
    have hb (x : Point) : iid p k m (nominate p t e x) ≤ (1-e)^m := by
      cases x with
      | ordinary _ => simpa [nominate,zero_iid] using qpos
      | marker a => exact fixed_bound hp t _ e e1.le k m
    have hsum : weight p k (fun x => iid p k m (nominate p t e x)) ≤ (1-e)^m := by
      calc
        _ ≤ weight p k (fun _ => (1-e)^m) := wmono hp.1 k hb
        _ = _ := wconst p k _
        _ ≤ _ := (mul_le_mul_of_nonneg_left (hp.2.1 k) qpos).trans (by simp)
    apply le_trans (imono hp.1 k (m+1) (envelope t e0))
    rw [iadd, iadd, iid_nominations, two_mul]
    exact add_le_add (add_le_add (fixed_bound hp t _ e e1.le k _)
      (fixed_bound hp t _ e e1.le k _)) (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))

private theorem two_lt_three_real : (2 : ℝ) < 3 := by
  exact_mod_cast (show (2 : Nat) < 3 by decide)

private theorem pref_bounds (a : Nat) : 0 < pref (.named a) ∧ pref (.named a) < 3 := by
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have ha1 : 0 < (a : ℝ) + 1 := add_pos_of_nonneg_of_pos ha zero_lt_one
  have lo : 0 ≤ (1 : ℝ) / ((a : ℝ)+1) := div_nonneg zero_le_one ha1.le
  have hi : (1 : ℝ) / ((a : ℝ)+1) ≤ 1 :=
    (div_le_iff₀ ha1).mpr (by simp)
  change 0 < 2 - _ ∧ 2 - _ < 3
  exact ⟨sub_pos.mpr (lt_of_le_of_lt hi one_lt_two),
    lt_of_le_of_lt (sub_le_self _ lo) two_lt_three_real⟩

private theorem pref_inj : Function.Injective pref := by
  intro g h eq
  have z3 : (0:ℝ) < 3 := lt_trans zero_lt_one (lt_trans one_lt_two two_lt_three_real)
  cases g <;> cases h
  all_goals try rfl
  case central.fallback => exact False.elim (z3.ne' eq)
  case fallback.central => exact False.elim (z3.ne eq)
  case central.named a => exact False.elim ((pref_bounds a).2.ne' eq)
  case named.central a => exact False.elim ((pref_bounds a).2.ne eq)
  case fallback.named a => exact False.elim ((pref_bounds a).1.ne eq)
  case named.fallback a => exact False.elim ((pref_bounds a).1.ne' eq)
  case named.named a b =>
    change 2 - 1 / ((a:ℝ)+1) = 2 - 1 / ((b:ℝ)+1) at eq
    have invEq := sub_right_injective eq
    simpa using invEq

private theorem minimal (s) (g) (ok : fits g s) :
    pref (select s) ≤ pref g := by
  classical
  unfold select
  split
  next hf =>
    cases g with
    | central => exact (lt_trans zero_lt_one (lt_trans one_lt_two two_lt_three_real)).le
    | fallback => exact le_rfl
    | named a => exact (pref_bounds a).1.le
  next hf =>
    split
    next hn =>
      cases g with
      | central => exact (pref_bounds _).2.le
      | fallback => contradiction
      | named b => rw [named_unique hf hn.choose_spec ok]
    next hn =>
      cases g with
      | central => exact le_rfl
      | fallback => contradiction
      | named b => exact False.elim (hn ⟨b,ok⟩)

/-- This fixed regularizer has a unique consistent minimum on every realizable sample.
Its selected disagreements shatter arbitrarily many ordinary points, and its iid error
probability satisfies the distribution-free bound from the draft. -/
theorem selectedSeparation :
    (∃ enc : Point → Nat, Function.Injective enc) ∧
    (∃ enc : Hyp → Nat, Function.Injective enc) ∧
    Function.Injective label ∧ Function.Injective pref ∧ (∀ g, 0 ≤ pref g) ∧
    (∀ s t, fits t s → fits (select s) s ∧
      ∀ g, fits g s → (g = select s ∨ pref (select s) < pref g)) ∧
    (∀ n : Nat, ∀ v : Nat → Bool, ∃ s : List Point, ∀ i < n,
      (label (select (observe .central s)) (.ordinary i) ≠ label .central (.ordinary i)
        ↔ v i = true)) ∧
    (∀ p : Point → ℝ, Law p → ∀ (t : Hyp) (m : Nat) (e : ℝ),
      1 ≤ m → 0 < e → e < 1 → ∀ k,
      iid p k m (event p t e) ≤ 2 * (1-e)^m + (m:ℝ) * (1-e)^(m-1)) := by
  refine ⟨?_, ?_, distinct_hypotheses, pref_inj, ?_, ?_, shatters, ?_⟩
  · refine ⟨fun | .ordinary i => 2*i | .marker i => 2*i+1, ?_⟩
    intro x y eq
    cases x <;> cases y <;> simp_all <;> omega
  · refine ⟨fun | .central => 0 | .fallback => 1 | .named i => i+2, ?_⟩
    intro x y eq
    cases x <;> cases y <;> simp_all
  · intro g
    cases g with
    | central => exact (lt_trans zero_lt_one (lt_trans one_lt_two two_lt_three_real)).le
    | fallback => exact le_rfl
    | named a => exact (pref_bounds a).1.le
  · intro s t ht
    refine ⟨select_fits s t ht, ?_⟩
    intro g hg
    obtain lt | eq := lt_or_eq_of_le (minimal s g hg)
    · exact Or.inr lt
    · exact Or.inl (pref_inj eq.symm)
  · intro p hp t m e hm e0 e1 k
    exact pac hp t m e hm e0 e1 k

end SelectedDisagreement
