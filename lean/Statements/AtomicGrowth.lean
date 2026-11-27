module

public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Pattern classes and the construction from uniform grid-class inputs. -/

open List

namespace AtomicGrowth

abbrev Word := List ℕ

/-- Rank within a finite word, using zero-based permutation values. -/
def rankIn (w : Word) (x : ℕ) : ℕ := (w.filter (fun y => decide (y<x))).length
def standard (w : Word) : Word := w.map (rankIn w)

def IsPerm (w : Word) : Prop := w.Perm (List.range w.length)
def Contains (u v : Word) : Prop := ∃ z, z.Sublist v ∧ standard z = u

theorem rank_lt {w : Word} {x y : ℕ} (hx : x ∈ w) (hxy : x<y) : rankIn w x < rankIn w y := by
  have h := (List.length_filter_lt_length_iff_exists (l:=w.filter (fun z => decide (z<y))) (p:=fun z => decide (z<x))).mpr
    ⟨x,by simp [hx,hxy],by simp⟩
  rw [List.filter_filter] at h
  have he : w.filter (fun z => decide (z<x) && decide (z<y)) = w.filter (fun z => decide (z<x)) := by
    apply List.filter_congr
    intro z _
    by_cases hh : z<x
    · simp [hh,hh.trans hxy]
    · simp [hh]
  rwa [he] at h

theorem rank_on {w : Word} {x y : ℕ} (hx : x ∈ w) (hy : y ∈ w) :
    rankIn w x < rankIn w y ↔ x<y := by
  constructor
  · intro h
    rcases lt_trichotomy x y with hh|rfl|hh
    · exact hh
    · exact False.elim (h.false)
    · exact False.elim ((rank_lt hy hh).not_gt h)
  · exact rank_lt hx

@[simp] theorem length_standard (w : Word) : (standard w).length = w.length := by simp [standard]

theorem perm_of_bounded {w : Word} (hd : w.Nodup) (hb : ∀ x ∈ w, x<w.length) : IsPerm w := by
  have hs : w.toFinset ⊆ Finset.range w.length := fun x hx => Finset.mem_range.mpr (hb x (List.mem_toFinset.mp hx))
  have he : w.toFinset = Finset.range w.length := Finset.eq_of_subset_of_card_le hs (by simp [List.toFinset_card_of_nodup hd])
  apply (List.perm_ext_iff_of_nodup hd List.nodup_range).mpr
  intro x
  simpa using (Finset.ext_iff.mp he x)

theorem standard_perm {w : Word} (hd : w.Nodup) : IsPerm (standard w) := by
  apply perm_of_bounded
  · apply hd.map_on
    intro x hx y hy e
    rcases lt_trichotomy x y with hl|hl|hl
    · exact False.elim ((rank_lt hx hl).ne e)
    · exact hl
    · exact False.elim ((rank_lt hy hl).ne e.symm)
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    rw [length_standard]
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨x,hx,by simp⟩

theorem standard_of_perm {w : Word} (hp : IsPerm w) : standard w = w := by
  change w.map _ = w
  conv_rhs => rw [←List.map_id w]
  apply List.map_congr_left
  intro x hx
  have hx' : x < w.length := List.mem_range.mp (hp.mem_iff.mp hx)
  have eqr : ((List.range w.length).filter (fun z => decide (z<x))) = List.range x := by
    have ha : (List.range x).filter (fun z => decide (z<x)) = List.range x :=
      List.filter_eq_self.mpr fun z hz => decide_eq_true (List.mem_range.mp hz)
    have hb : ((List.range (w.length-x)).map (x+·)).filter (fun z => decide (z<x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hz
      simp
    conv_lhs => rw [←Nat.add_sub_of_le hx'.le,List.range_add,List.filter_append,ha,hb,List.append_nil]
  exact (hp.filter (fun z => decide (z<x))).length_eq.trans (eqr ▸ List.length_range)

theorem standard_map {w : Word} (f : ℕ → ℕ)
    (hf : ∀ x ∈ w, ∀ y ∈ w, f x < f y ↔ x<y) : standard (w.map f) = standard w := by
  unfold standard
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply,rankIn,List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro y hy
  simp [hf y hy x hx]

theorem standard_shift (w : Word) (a : ℕ) : standard (w.map (a+·)) = standard w :=
  standard_map _ (by simp)

theorem Contains.trans {u v w : Word} (h : Contains u v) (k : Contains v w) : Contains u w := by
  obtain ⟨a,ha,rfl⟩ := k
  obtain ⟨b,hb,rfl⟩ := h
  obtain ⟨c,hc,rfl⟩ := List.sublist_map_iff.mp hb
  exact ⟨c,hc.trans ha,(standard_map _ (fun x hx y hy => rank_on (hc.subset hx) (hc.subset hy))).symm⟩

theorem Contains.refl {w : Word} (hw : IsPerm w) : Contains w w :=
  ⟨w,List.Sublist.refl _,standard_of_perm hw⟩

def direct (u v : Word) : Word := u ++ v.map (u.length+·)

theorem direct_perm {u v : Word} (hu : IsPerm u) (hv : IsPerm v) : IsPerm (direct u v) := by
  change (u ++ v.map (u.length+·)).Perm (List.range (direct u v).length)
  rw [show (direct u v).length = u.length+v.length by simp [direct],List.range_add]
  simpa [Nat.add_comm] using hu.append (hv.map (u.length+·))

/-- The pattern of separated blocks is the direct sum of their individual patterns. -/
theorem standard_append (u v : Word) (h : ∀ x ∈ u, ∀ y ∈ v, x<y) :
    standard (u++v) = direct (standard u) (standard v) := by
  simp only [standard,direct,List.map_append,List.map_map,List.length_map]
  congr 1
  · apply List.map_congr_left
    intro x hx
    simp only [rankIn,List.filter_append,List.length_append]
    have he : v.filter (fun y => decide (y<x)) = [] := List.filter_eq_nil_iff.mpr fun y hy => by simp [(h x hx y hy).not_gt]
    simp [he]
  · apply List.map_congr_left
    intro y hy
    simp only [rankIn,List.filter_append,List.length_append,Function.comp_apply]
    rw [List.filter_eq_self.mpr (fun x hx => by simp [h x hx y hy])]

end AtomicGrowth

open List

namespace AtomicGrowth

abbrev Class := Set Word

noncomputable def level (A : Class) (n : ℕ) : Finset Word := by
  classical
  exact (List.range n).permutations.toFinset.filter (· ∈ A)

theorem mem_level {A : Class} {n : ℕ} {w : Word} :
    w ∈ level A n ↔ IsPerm w ∧ w.length = n ∧ w ∈ A := by
  classical
  rw [level,Finset.mem_filter,List.mem_toFinset,List.mem_permutations]
  constructor
  · rintro ⟨hp,hA⟩
    have hn : w.length=n := by simpa using hp.length_eq
    exact ⟨by simpa [IsPerm,hn] using hp,hn,hA⟩
  · rintro ⟨hp,hn,hA⟩
    exact ⟨by simpa [IsPerm,hn] using hp,hA⟩

def Hereditary (A : Class) : Prop := ∀ v ∈ A, ∀ u, Contains u v → u ∈ A

def Atomic (A : Class) : Prop := ∀ u ∈ A, ∀ v ∈ A, ∃ t ∈ A, Contains u t ∧ Contains v t

def blocks : List Word → Word
  | [] => []
  | w::ws => direct w (blocks ws)

@[simp] theorem direct_length (u v : Word) : (direct u v).length = u.length+v.length := by simp [direct]

@[simp] theorem direct_nil (w : Word) : direct w [] = w := by simp [direct]
@[simp] theorem nil_direct (w : Word) : direct [] w = w := by simp [direct]

theorem direct_assoc (u v w : Word) : direct (direct u v) w = direct u (direct v w) := by
  simp [direct,List.map_map,Function.comp_def,Nat.add_assoc]

theorem blocks_append (xs ys : List Word) : blocks (xs++ys) = direct (blocks xs) (blocks ys) := by
  induction xs with
  | nil => simp [blocks]
  | cons x xs ih => simp [blocks,ih,direct_assoc]

theorem blocks_perm (xs : List Word) (h : ∀ x ∈ xs, IsPerm x) : IsPerm (blocks xs) := by
  induction xs with
  | nil => exact List.Perm.refl []
  | cons x xs ih => exact direct_perm (h x (by simp)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem block_contains {xs : List Word} {x : Word} (h : x ∈ xs) (hp : IsPerm x) : Contains x (blocks xs) := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨x,List.sublist_append_left ..,standard_of_perm hp⟩
    · obtain ⟨y,hy,he⟩ := ih h
      exact ⟨y.map (a.length+·),(hy.map _).trans (List.sublist_append_right ..),(standard_shift _ _).trans he⟩

theorem prefix_contains {xs ys : List Word} {x : Word} (h : Contains x (blocks xs)) : Contains x (blocks (xs++ys)) := by
  obtain ⟨y,hy,he⟩ := h
  rw [blocks_append]
  exact ⟨y,hy.trans (List.sublist_append_left ..),he⟩

def stages (s : ℕ → List Word) (k : ℕ) : List Word := (List.range k).flatMap s

def jointClass (s : ℕ → List Word) : Class := {w | ∃ k, Contains w (blocks (stages s k))}

theorem stages_add (s : ℕ → List Word) (k d : ℕ) :
    stages s (k+d) = stages s k ++ (List.range d).flatMap (fun i => s (k+i)) := by
  simp [stages,List.range_add,List.flatMap_map]

theorem stages_perm {s : ℕ → List Word} (h : ∀ i, ∀ x ∈ s i, IsPerm x) (k) : IsPerm (blocks (stages s k)) := by
  apply blocks_perm
  intro x hx
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hx
  exact h i x hi

theorem joint_atomic {s : ℕ → List Word} (h : ∀ i, ∀ x ∈ s i, IsPerm x) : Atomic (jointClass s) := by
  rintro u ⟨i,hi⟩ v ⟨j,hj⟩
  have hl (w k l) (hkl : k≤l) (hw : Contains w (blocks (stages s k))) : Contains w (blocks (stages s l)) := by
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hkl
    rw [stages_add]
    exact prefix_contains hw
  let l := max i j
  exact ⟨blocks (stages s l),⟨l,Contains.refl (stages_perm h l)⟩,hl _ i l (le_max_left ..) hi,hl _ j l (le_max_right ..) hj⟩

theorem joint_hereditary (s : ℕ → List Word) : Hereditary (jointClass s) := by
  rintro u ⟨k,hk⟩ v hv
  exact ⟨k,hv.trans hk⟩

theorem joint_perms {s : ℕ → List Word} (h : ∀ i, ∀ x ∈ s i, IsPerm x) :
    ∀ x ∈ jointClass s, IsPerm x := by
  rintro x ⟨k,y,hy,rfl⟩
  exact standard_perm (hy.nodup ((stages_perm h k).nodup_iff.mpr List.nodup_range))

theorem stage_mem_class {s : ℕ → List Word} {i : ℕ} {x : Word} (h : x ∈ s i) (hp : IsPerm x) :
    x ∈ jointClass s := ⟨i+1,block_contains (List.mem_flatMap.mpr ⟨i,by simp,h⟩) hp⟩

/-- An explicit finite set containing all direct sums of nonempty Q-blocks
at each size. A repeated representation costs only one element. -/
noncomputable def products (Q : ℕ → Finset Word) : (n : ℕ) → Finset Word
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion (fun k : Fin (n+1) => ((Q (k.val+1)) ×ˢ products Q (n-k.val)).image (fun t => direct t.1 t.2))
termination_by n => n

theorem products_prepend {Q : ℕ → Finset Word} {r k : ℕ} (hr : 0<r) {u v : Word} (hu : u ∈ Q r) (hv : v ∈ products Q k) :
    direct u v ∈ products Q (r+k) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [show r+1+k=(r+k)+1 by omega,products]
  let i : Fin (r+k+1) := ⟨r,by omega⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,?_⟩,rfl⟩⟩
  simpa [i] using hv

theorem products_suffix {Q : ℕ → Finset Word} {m : ℕ} (bs : List Word)
    (hp : ∀ b ∈ bs, IsPerm b)
    (hq : ∀ b ∈ bs, ∀ z, z.Sublist b → z.length ≤ m → z ≠ [] → standard z ∈ Q z.length)
    (z : Word) (hz : z.Sublist (blocks bs)) (hlen : z.length≤m) : standard z ∈ products Q z.length := by
  induction bs generalizing z with
  | nil =>
    have : z=[] := by simpa [blocks] using hz
    simp [this,standard,products]
  | cons b bs ih =>
    obtain ⟨u,v,rfl,hu,hv⟩ := List.sublist_append_iff.mp hz
    obtain ⟨v,hv',rfl⟩ := (List.sublist_map_iff (f:=(b.length+·)) (l₂:=blocks bs)).mp hv
    have hm : u.length+v.length≤m := by simpa using hlen
    have sep : ∀ x ∈ u, ∀ y ∈ v.map (b.length+·), x<y := by
      intro x hx y hy
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hy
      have hlt := List.mem_range.mp ((hp b (by simp)).mem_iff.mp (hu.subset hx))
      omega
    rw [standard_append _ _ sep,standard_shift,List.length_append,List.length_map]
    have hvs := ih (fun t ht => hp t (by simp [ht])) (fun t ht => hq t (by simp [ht])) v hv' (by omega)
    by_cases he : u = []
    · simpa [he,standard] using hvs
    · have h₁ : 0<u.length := List.length_pos_iff.mpr he
      exact products_prepend h₁ (hq b (by simp) u hu (by omega) he) hvs

end AtomicGrowth

open List

namespace AtomicGrowth

theorem products_card {Q : ℕ → Finset Word} {L : ℝ} (hL : 0<L)
    (hw : ∀ n, (∑ i : Fin n, ((Q (i.val+1)).card : ℝ)/L^(i.val+1)) ≤ 1) (n : ℕ) :
    ((products Q n).card : ℝ) ≤ L^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [products]
    | succ n =>
      let t (i : Fin (n+1)) := ((Q (i.val+1)) ×ˢ products Q (n-i.val)).image (fun z => direct z.1 z.2)
      have hsum : (products Q (n+1)).card ≤ ∑ i : Fin (n+1), (Q (i.val+1)).card * (products Q (n-i.val)).card := by
        rw [products]
        exact (Finset.card_biUnion_le (s:=Finset.univ) (t:=t)).trans (Finset.sum_le_sum fun i _ =>
          Finset.card_image_le.trans (Finset.card_product _ _).le)
      apply (show ((products Q (n+1)).card : ℝ) ≤ ∑ i : Fin (n+1), ((Q (i.val+1)).card:ℝ) * (products Q (n-i.val)).card by
        exact_mod_cast hsum).trans
      calc _ ≤ ∑ i : Fin (n+1), ((Q (i.val+1)).card:ℝ)*L^(n-i.val) := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (ih _ (by omega)) (Nat.cast_nonneg _)
           _ = (∑ i : Fin (n+1), ((Q (i.val+1)).card:ℝ)/L^(i.val+1))*L^(n+1) := by
             rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _
             rw [show L^(n+1)=L^(i.val+1)*L^(n-i.val) by rw [←pow_add]; congr 1; omega]
             field_simp
           _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right (hw (n+1)) (pow_nonneg hL.le (n+1))

theorem joint_valley {s : ℕ → List Word} (hp : ∀ i, ∀ w ∈ s i, IsPerm w) (i m : ℕ)
    (Q : ℕ → Finset Word) (hq : ∀ j ≥ i, ∀ b ∈ s j, ∀ z, z.Sublist b → z.length≤m → z ≠ [] → standard z ∈ Q z.length)
    (L : ℝ) (hL : 1≤L) (hw : ∀ n, (∑ k : Fin n, ((Q (k.val+1)).card : ℝ)/L^(k.val+1))≤1) :
    ((level (jointClass s) m).card : ℝ) ≤ 2^(blocks (stages s i)).length * L^m := by
  classical
  let pre := blocks (stages s i)
  let choices := pre.sublists.toFinset
  let after (u : Word) := (products Q (m-u.length)).image fun v => direct (standard u) v
  have incl : level (jointClass s) m ⊆ choices.biUnion after := by
    intro w hwm
    obtain ⟨_,hlen,j,hwj⟩ := mem_level.mp hwm
    have hsub : Contains w (blocks (stages s (i+j))) := by
      rw [Nat.add_comm,stages_add]
      exact prefix_contains hwj
    obtain ⟨z,hz,rfl⟩ := hsub
    rw [stages_add,blocks_append] at hz
    obtain ⟨u,v,rfl,hu,hv⟩ := List.sublist_append_iff.mp hz
    obtain ⟨v,hv',rfl⟩ := (List.sublist_map_iff (f:=(pre.length+·))).mp hv
    change u.Sublist pre at hu
    have hm : u.length+v.length=m := by simpa using hlen
    let bs := (List.range j).flatMap fun k => s (i+k)
    have hper : ∀ t ∈ bs, IsPerm t := by
      rintro t ht
      obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp ht
      exact hp _ _ hk
    have hlocal : ∀ t ∈ bs, ∀ z, z.Sublist t → z.length≤m → z ≠ [] → standard z ∈ Q z.length := by
      intro t ht
      obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp ht
      exact hq (i+k) (by omega) t hk
    have hvs := products_suffix bs hper hlocal v hv' (by omega)
    have sep : ∀ x ∈ u, ∀ y ∈ v.map (pre.length+·), x<y := by
      rintro x hx y hy
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hy
      have hl := List.mem_range.mp ((stages_perm hp i).mem_iff.mp (hu.subset hx))
      change x<pre.length at hl
      omega
    change standard (u ++ v.map (pre.length+·)) ∈ _
    rw [standard_append _ _ sep,standard_shift]
    exact Finset.mem_biUnion.mpr ⟨u,List.mem_toFinset.mpr (List.mem_sublists.mpr hu),
      Finset.mem_image.mpr ⟨standard v,(show m-u.length=v.length by omega) ▸ hvs,rfl⟩⟩
  have hc := (Finset.card_le_card incl).trans (Finset.card_biUnion_le (s:=choices) (t:=after))
  apply (show ((level (jointClass s) m).card : ℝ) ≤ ∑ u ∈ choices, ((after u).card : ℝ) by exact_mod_cast hc).trans
  calc _ ≤ ∑ _u ∈ choices, L^m := by
         apply Finset.sum_le_sum
         intro u _
         have hh : ((after u).card : ℝ) ≤ ((products Q (m-u.length)).card : ℝ) := by exact_mod_cast Finset.card_image_le
         exact hh.trans ((products_card (by linarith) hw _).trans (pow_le_pow_right₀ hL (Nat.sub_le ..)))
       _ = (choices.card : ℝ)*L^m := by simp
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
         exact_mod_cast (List.toFinset_card_le pre.sublists).trans (List.length_sublists pre).le

end AtomicGrowth

open Filter Finset
open scoped Topology

namespace AtomicGrowth

/-- A large integer w absorbs the polynomial prefactor in the Pantone–Vatter
bound. A geometric majorant of ratio 99/100 controls every positive partial
sum, uniformly in the valley length. -/
theorem choose_scale :
    ∃ w : ℕ, 4105 ≤ w ∧
      ∀ q : ℕ → ℕ, (∀ n, 0<n → q n ≤ 512*8^n*n^2*(n+2).choose 2*(w+513)^(n-1)) →
        ∀ m, (∑ i : Fin m, (q (i.val+1) : ℝ) / (17*(w:ℝ)/2)^(i.val+1)) ≤ 1 := by
  let r : ℝ := 99/100
  let t : ℝ := 97/100
  obtain ⟨M,hM⟩ := (tendsto_pow_const_mul_const_pow_of_lt_one 4 (by norm_num [t] : 0≤t)
    (by norm_num [t] : t<1)).bddAbove_range
  obtain ⟨w,hw⟩ := exists_nat_gt (max 30000 (460800*M))
  have hwbig : (30000:ℝ) < w := (le_max_left ..).trans_lt hw
  have hcoef : 460800*M < w := (le_max_right ..).trans_lt hw
  refine ⟨w,by exact_mod_cast (show (4105:ℝ) ≤ w by linarith),?_⟩
  intro q hq m
  let L := 17*(w:ℝ)/2
  have hL : 0<L := by dsimp [L]; positivity
  have hbase : 8*((w:ℝ)+513) ≤ (t*r)*L := by dsimp [t,r,L]; linarith
  have each (k : ℕ) : (q (k+1) : ℝ)/L^(k+1) ≤ (1/100)*r^k := by
    let n := k+1
    have hn : 1 ≤ (n:ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hcast : (q n:ℝ) ≤ 512*(8:ℝ)^n*(n:ℝ)^2*((n+2).choose 2:ℕ)*((w:ℝ)+513)^k := by
      have hh := hq n (by dsimp [n]; omega)
      have hk : n-1=k := by simp [n]
      rw [hk] at hh
      exact_mod_cast hh
    have hbin : (((n+2).choose 2:ℕ):ℝ) ≤ 9*(n:ℝ)^2 := by
      have hc : (((n+2).choose 2:ℕ):ℝ) ≤ ((n:ℝ)+2)^2 := by exact_mod_cast Nat.choose_le_pow (n+2) 2
      nlinarith only [hc,hn,sq_nonneg ((n:ℝ)-1)]
    have hmajor : (q n:ℝ)*((w:ℝ)+513) ≤ 4608*(n:ℝ)^4*(8*((w:ℝ)+513))^n := by
      have hx := mul_le_mul_of_nonneg_right hcast (by positivity : 0≤(w:ℝ)+513)
      have hy := mul_le_mul_of_nonneg_left hbin (by positivity : 0≤512*(8:ℝ)^n*(n:ℝ)^2*((w:ℝ)+513)^n)
      rw [mul_pow]
      rw [show ((w:ℝ)+513)^n = ((w:ℝ)+513)^k*((w:ℝ)+513) from pow_succ ..] at hy ⊢
      nlinarith only [hx,hy]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 8*((w:ℝ)+513)) hbase n
    have hbd : (n:ℝ)^4*t^n ≤ M := hM ⟨n,rfl⟩
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0≤4608*(n:ℝ)^4)
    have hm' := mul_le_mul_of_nonneg_right hbd (by positivity : 0≤4608*r^n*L^n)
    simp only [mul_pow] at hmul hmajor
    have hlarge := mul_le_mul_of_nonneg_right (show 4608*M ≤ ((w:ℝ)+513)/100 by linarith) (by positivity : 0≤r^n*L^n)
    have hqn : (q n:ℝ) ≤ (1/100)*r^n*L^n := by
      apply le_of_mul_le_mul_right (a:=((w:ℝ)+513)) _ (by positivity)
      nlinarith only [hmajor,hmul,hm',hlarge]
    have hr : r^(k+1)≤r^k := by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num [r])
    exact ((div_le_iff₀ (pow_pos hL _)).mpr hqn).trans (mul_le_mul_of_nonneg_left hr (by norm_num))
  change _ ≤ _
  calc (∑ i : Fin m, (q (i.val+1):ℝ)/L^(i.val+1)) ≤ ∑ i : Fin m, (1/100)*r^i.val :=
         Finset.sum_le_sum fun i _ => each i.val
       _ = (1/100)* ∑ k ∈ Finset.range m, r^k := by rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
       _ ≤ 1 := by
         have hsum := (summable_geometric_of_lt_one (by norm_num [r] : 0≤r) (by norm_num [r] : r<1)).sum_le_tsum
           (Finset.range m) (fun i _ => pow_nonneg (by norm_num [r]) i)
         rw [tsum_geometric_of_lt_one (by norm_num [r]) (by norm_num [r])] at hsum
         dsimp [r] at hsum ⊢
         norm_num at hsum
         linarith

end AtomicGrowth

open Filter
open scoped Topology

namespace AtomicGrowth

noncomputable def growth (C : Class) (n : ℕ) : ℝ :=
  ((level C n).card : ℝ)^((n:ℝ)⁻¹)

/-- The grid-class facts from the cited work are explicit hypotheses. -/
structure GridFacts (w : ℕ) (D : ℕ → Class) (Q : Class) : Prop where
  hereditary : ∀ h ≥ 4, Hereditary (D h)
  peak : ∀ h ≥ 4, Tendsto (growth (D h)) atTop (𝓝 (9*(w:ℝ)))
  recurrent : ∀ v, v ∈ Q ↔ ∃ᶠ h in atTop, v ∈ D h
  count : ∀ n, 0<n → (level Q n).card ≤ 512*8^n*n^2*(n+2).choose 2*(w+513)^(n-1)

theorem grid_small {w D Q} (g : GridFacts w D Q) (m : ℕ) :
    ∃ h ≥ 4, ∀ b ∈ D h, IsPerm b → ∀ z, z.Sublist b → z.length ≤ m → standard z ∈ level Q z.length := by
  classical
  let candidates := (Finset.range (m+1)).biUnion (level Set.univ)
  have ev (u : Word) : ∀ᶠ h in atTop, u ∈ D h → u ∈ Q := by
    by_cases hu : u ∈ Q
    · exact Eventually.of_forall fun _ _ => hu
    · have hn := mt (g.recurrent u).mpr hu
      filter_upwards [not_frequently.mp hn] with h hh hmem
      exact (hh hmem).elim
  have he : ∀ᶠ h in atTop, ∀ u ∈ candidates, u ∈ D h → u ∈ Q :=
    (eventually_all_finset candidates).mpr fun u _ => ev u
  obtain ⟨h,hh,huni⟩ := ((eventually_ge_atTop 4).and he).exists
  refine ⟨h,hh,?_⟩
  intro b hb hp z hz hm
  have hzp : IsPerm (standard z) := standard_perm (hz.nodup (hp.nodup_iff.mpr List.nodup_range))
  have hin : standard z ∈ candidates := Finset.mem_biUnion.mpr ⟨z.length,Finset.mem_range.mpr (by omega),
    mem_level.mpr ⟨hzp,length_standard _,Set.mem_univ _⟩⟩
  exact mem_level.mpr ⟨hzp,length_standard _,huni _ hin (g.hereditary h hh b hb _ ⟨z,hz,rfl⟩)⟩

noncomputable def tolerance (i : ℕ) : ℝ := ((i:ℝ)+1)⁻¹
theorem tolerance_pos (i : ℕ) : 0<tolerance i := by unfold tolerance; positivity

structure Stage where
  valley : ℕ
  peak : ℕ
  batch : List Word

structure StageSpec (Q : Class) (L H : ℝ) (i : ℕ) (prior : List Word) (last : ℕ) (s : Stage) : Prop where
  valley_gt : max i last < s.valley
  peak_gt : s.valley < s.peak
  absorb : (2:ℝ)^(blocks prior).length * L^s.valley ≤ (L+tolerance i)^s.valley
  perms : ∀ b ∈ s.batch, IsPerm b
  lengths : ∀ b ∈ s.batch, b.length=s.peak
  small : ∀ b ∈ s.batch, ∀ z, z.Sublist b → z.length≤s.valley → standard z ∈ level Q z.length
  many : H-tolerance i < (s.batch.toFinset.card : ℝ)^((s.peak:ℝ)⁻¹)

theorem grid_stage {w D Q} (g : GridFacts w D Q) {L : ℝ} (hL : 0<L)
    (i : ℕ) (prior : List Word) (last : ℕ) :
    ∃ s, StageSpec Q L (9*(w:ℝ)) i prior last s := by
  classical
  let r := (L+tolerance i)/L
  have hr : 1<r := (one_lt_div hL).mpr (lt_add_of_pos_right _ (tolerance_pos i))
  obtain ⟨a,ha⟩ := pow_unbounded_of_one_lt ((2:ℝ)^(blocks prior).length) hr
  let m := max a (max i last + 1)
  have hm : max i last < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right ..)
  have hab : (2:ℝ)^(blocks prior).length * L^m ≤ (L+tolerance i)^m := by
    have hb := ha.le.trans (pow_le_pow_right₀ hr.le (show a≤m from le_max_left ..))
    unfold r at hb
    rw [div_pow] at hb
    exact (le_div_iff₀ (pow_pos hL _)).mp hb
  obtain ⟨h,hh,hsmall⟩ := grid_small g m
  have he : ∀ᶠ n in atTop, 9*(w:ℝ)-tolerance i < growth (D h) n :=
    (g.peak h hh).eventually (eventually_gt_nhds (by linarith [tolerance_pos i]))
  obtain ⟨n,hn,hg⟩ := ((eventually_gt_atTop m).and he).exists
  let batch := (level (D h) n).toList
  have hmem (b) (hb : b ∈ batch) := mem_level.mp (Finset.mem_toList.mp hb)
  exact ⟨⟨m,n,batch⟩,hm,hn,hab,(fun b hb => (hmem b hb).1),
    (fun b hb => (hmem b hb).2.1),(fun b hb => hsmall b (hmem b hb).2.2 (hmem b hb).1),
    by simpa [batch,growth] using hg⟩

end AtomicGrowth

open Filter
open scoped Topology

namespace AtomicGrowth

/-- A stage is chosen only after its entire finite prefix is known. -/
def history (make : ℕ → List Word → ℕ → Stage) : ℕ → List Word × ℕ
  | 0 => ([],0)
  | i+1 =>
    let old := history make i
    let s := make i old.1 old.2
    (old.1++s.batch,s.peak)

def schedule (make : ℕ → List Word → ℕ → Stage) (i : ℕ) : Stage :=
  make i (history make i).1 (history make i).2

theorem stages_schedule (make : ℕ → List Word → ℕ → Stage) (i : ℕ) :
    stages (fun j => (schedule make j).batch) i = (history make i).1 := by
  induction i with
  | zero => simp [stages,history]
  | succ i ih => rw [stages_add,ih]; simp [history,schedule]

theorem tolerance_tendsto : Tendsto tolerance atTop (𝓝 0) := by
  have h : Tendsto (fun i : ℕ => (i:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

/-- The low and high inequalities here occur at arbitrarily large lengths. -/
def Oscillates (C : Class) (L H : ℝ) : Prop :=
  ∀ e>0, (∃ᶠ n in atTop, growth C n < L+e) ∧ (∃ᶠ n in atTop, H-e < growth C n)

theorem schedule_oscillates {Q : Class} {L H : ℝ} (hL : 1≤L)
    (hw : ∀ n, (∑ k : Fin n, ((level Q (k.val+1)).card : ℝ)/L^(k.val+1))≤1)
    (make : ℕ → List Word → ℕ → Stage)
    (good : ∀ i p l, StageSpec Q L H i p l (make i p l)) :
    let s := fun i => (schedule make i).batch
    (∀ i, ∀ b ∈ s i, IsPerm b) ∧ Oscillates (jointClass s) L H := by
  classical
  let t := schedule make
  let s := fun i => (t i).batch
  let C := jointClass s
  have spec (i) : StageSpec Q L H i (history make i).1 (history make i).2 (t i) := good .. 
  have hp : ∀ i, ∀ b ∈ s i, IsPerm b := fun i => (spec i).perms
  refine ⟨hp,?_⟩
  change Oscillates C L H
  have hindex (i) : i < (t i).valley := (le_max_left ..).trans_lt (spec i).valley_gt
  have hs : StrictMono fun i => (t i).valley := strictMono_nat_of_lt_succ fun i => by
    have hh : (t i).peak < (t (i+1)).valley := (le_max_right ..).trans_lt (spec (i+1)).valley_gt
    exact (spec i).peak_gt.trans hh
  have low (i) : growth C (t i).valley ≤ L+tolerance i := by
    have hv := joint_valley hp i (t i).valley (level Q) (fun j hj b hb z hz hm _ =>
      (spec j).small b hb z hz (hm.trans (hs.monotone hj))) L hL hw
    change ((level C (t i).valley).card:ℝ) ≤ _ at hv
    have hpre : stages s i=(history make i).1 := stages_schedule make i
    rw [hpre] at hv
    have hb := hv.trans (spec i).absorb
    have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by positivity : 0≤((t i).valley:ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (by linarith [tolerance_pos i]) (by have := hindex i; omega)] at h
    exact h
  have high (i) : H-tolerance i < growth C (t i).peak := by
    have incl : (s i).toFinset ⊆ level C (t i).peak := by
      intro b hb
      have hm := List.mem_toFinset.mp hb
      exact mem_level.mpr ⟨hp i b hm,(spec i).lengths b hm,stage_mem_class hm (hp i b hm)⟩
    have hc : ((s i).toFinset.card:ℝ) ≤ (level C (t i).peak).card := by exact_mod_cast Finset.card_le_card incl
    exact (spec i).many.trans_le (Real.rpow_le_rpow (Nat.cast_nonneg _) hc (by positivity))
  intro e he
  have pick (N : ℕ) : ∃ i≥N, tolerance i<e := ((eventually_ge_atTop N).and (tolerance_tendsto.eventually (eventually_lt_nhds he))).exists
  constructor <;> apply frequently_atTop.mpr <;> intro N <;> obtain ⟨i,hi,hsmall⟩ := pick N
  · exact ⟨_,hi.trans (hindex i).le,(low i).trans_lt (by linarith)⟩
  · exact ⟨_,hi.trans ((hindex i).trans (spec i).peak_gt).le,(show H-e < H-tolerance i by linarith).trans (high i)⟩

end AtomicGrowth

open Filter
open scoped Topology

namespace AtomicGrowth

theorem oscillates_no_limit {C L H} (hg : L<H) (ho : Oscillates C L H) :
    ¬ ∃ x : ℝ, Tendsto (growth C) atTop (𝓝 x) := by
  rintro ⟨x,hx⟩
  obtain ⟨lo,hi⟩ := ho ((H-L)/3) (by linarith)
  have h₁ := le_of_tendsto_of_frequently hx (lo.mono fun _ hh => hh.le)
  have h₂ := ge_of_tendsto_of_frequently hx (hi.mono fun _ hh => hh.le)
  linarith

theorem full_level {C : Class} (hc : ∀ w, IsPerm w → w ∈ C) (n : ℕ) :
    (level C n).card = n.factorial := by
  classical
  unfold level
  rw [Finset.filter_eq_self.mpr (fun x hx => hc _ (by
    have h := List.mem_permutations.mp (List.mem_toFinset.mp hx)
    have he : x.length=n := by simpa using h.length_eq
    simpa [IsPerm,he] using h)),List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range),
    List.length_permutations,List.length_range]

theorem oscillates_proper {C L H} (hL : 1≤L) (ho : Oscillates C L H) : ∃ w, IsPerm w ∧ w ∉ C := by
  by_contra hc
  push Not at hc
  have hA : 0≤L+1 := by linarith
  have he : ∀ᶠ n : ℕ in atTop, (L+1)^n < (n.factorial:ℝ) := by
    have ht := (Real.summable_pow_div_factorial (L+1)).tendsto_atTop_zero
    filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn
    simpa using (div_lt_iff₀ (show 0<(n.factorial:ℝ) by exact_mod_cast Nat.factorial_pos n)).mp hn
  obtain ⟨n,hlo,hf,hn⟩ := ((ho 1 (by norm_num)).1.and_eventually (he.and (eventually_gt_atTop 0))).exists
  have hn' : 0<((n:ℝ)⁻¹) := by positivity
  have hh := Real.rpow_lt_rpow (pow_nonneg hA n) hf hn'
  rw [Real.pow_rpow_inv_natCast hA hn.ne'] at hh
  unfold growth at hlo
  rw [full_level hc] at hlo
  exact (hlo.trans hh).false

/-- Assuming precisely the grid-class input cited in the manuscript, there is
a proper atomic permutation class whose exponential growth rate does not exist.
Its members are the patterns of consecutive finite stages in an infinite
direct sum, and the two numerical thresholds are witnessed arbitrarily late. -/
theorem oscillation_from_grid_data
    (grid : ∀ w : ℕ, 4105≤w → ∃ D Q, GridFacts w D Q) :
    ∃ (w : ℕ) (s : ℕ → List Word), 4105≤w ∧
      (∀ i, ∀ b ∈ s i, IsPerm b) ∧
      (∀ u ∈ jointClass s, IsPerm u) ∧ Hereditary (jointClass s) ∧ Atomic (jointClass s) ∧
      (∃ u, IsPerm u ∧ u ∉ jointClass s) ∧
      Oscillates (jointClass s) (17*(w:ℝ)/2) (9*(w:ℝ)) ∧
      ¬ ∃ x : ℝ, Tendsto (growth (jointClass s)) atTop (𝓝 x) := by
  classical
  obtain ⟨w,hw,hscale⟩ := choose_scale
  obtain ⟨D,Q,g⟩ := grid w hw
  let L := 17*(w:ℝ)/2
  have hbig : (4105:ℝ)≤w := by exact_mod_cast hw
  have hL : 1≤L := by dsimp [L]; linarith
  have hgap : L < 9*(w:ℝ) := by dsimp [L]; linarith
  have hwg := hscale (fun n => (level Q n).card) g.count
  choose make good using grid_stage g (by linarith : 0<L)
  obtain ⟨hp,ho⟩ := schedule_oscillates hL hwg make good
  exact ⟨w,_,hw,hp,joint_perms hp,joint_hereditary _,joint_atomic hp,
    oscillates_proper hL ho,ho,oscillates_no_limit hgap ho⟩

end AtomicGrowth
