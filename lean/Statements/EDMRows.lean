module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace EDMRows

/-- A proper ideal containing the finite sets and meeting every infinite set
in an infinite member. All uses are in the ground universe of the model. -/
structure TallIdeal (A : Type*) where
  small : Set A → Prop
  down : ∀ {S T}, S ⊆ T → small T → small S
  union : ∀ {S T}, small S → small T → small (S ∪ T)
  finite : ∀ {S}, S.Finite → small S
  proper : ¬small Set.univ
  tall : ∀ {S}, S.Infinite → ∃ R ⊆ S, R.Infinite ∧ small R

namespace TallIdeal
variable {A : Type*} (I : TallIdeal A)

theorem infinite_complement {S : Set A} (h : I.small S) : Sᶜ.Infinite := by
  intro finite
  have := I.union h (I.finite finite)
  exact I.proper (by simpa using this)

theorem fresh_reserve {S : Set A} (h : I.small S) : ∃ R ⊆ Sᶜ, R.Infinite ∧ I.small R :=
  I.tall (I.infinite_complement h)
end TallIdeal

/-- The number of occupied positions in the initial interval [0,n). -/
noncomputable def initial (S : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (· ∈ S)

theorem mem_initial {S : Set ℕ} {x n : ℕ} : x ∈ initial S n ↔ x < n ∧ x ∈ S := by
  classical
  simp [initial]

noncomputable def count (S : Set ℕ) (n : ℕ) : ℕ := (initial S n).card

/-- The natural-density-zero criterion stated without real division. For each
positive k the frequency is eventually at most 1/k. -/
def DensityZero (S : Set ℕ) : Prop := ∀ k : ℕ, ∃ N, ∀ n ≥ N, k * count S n ≤ n

theorem count_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) : count S n ≤ count T n := by
  apply Finset.card_le_card
  exact fun _ hx => mem_initial.mpr ⟨(mem_initial.mp hx).1,h (mem_initial.mp hx).2⟩

theorem count_union (S T : Set ℕ) (n : ℕ) : count (S ∪ T) n ≤ count S n + count T n := by
  apply (Finset.card_le_card (t := initial S n ∪ initial T n) ?_).trans (Finset.card_union_le ..)
  intro a ha
  obtain ⟨lt,left|right⟩ := mem_initial.mp ha
  · exact Finset.mem_union_left _ (mem_initial.mpr ⟨lt,left⟩)
  · exact Finset.mem_union_right _ (mem_initial.mpr ⟨lt,right⟩)

theorem density_finite {S : Set ℕ} (h : S.Finite) : DensityZero S := by
  classical
  intro k
  refine ⟨k*h.toFinset.card, fun n hn => (Nat.mul_le_mul_left k (Finset.card_le_card ?_)).trans hn⟩
  intro x hx
  exact h.mem_toFinset.mpr (mem_initial.mp hx).2

theorem density_union {S T : Set ℕ} (hs : DensityZero S) (ht : DensityZero T) :
    DensityZero (S ∪ T) := by
  intro k
  obtain ⟨N,l⟩ := hs (k+k)
  obtain ⟨M,r⟩ := ht (k+k)
  refine ⟨max N M,fun n hn => ?_⟩
  have hl := l n ((le_max_left _ _).trans hn)
  have hr := r n ((le_max_right _ _).trans hn)
  rw [Nat.add_mul] at hl hr
  apply (Nat.mul_le_mul_left k (count_union S T n)).trans
  rw [Nat.mul_add]
  apply Nat.le_of_mul_le_mul_left (c := 2) _ (by decide)
  rw [Nat.two_mul,Nat.two_mul]
  exact (show (k*count S n + k*count T n)+(k*count S n + k*count T n) =
    (k*count S n+k*count S n)+(k*count T n+k*count T n) by ac_rfl).le.trans (Nat.add_le_add hl hr)

theorem density_tall {S : Set ℕ} (h : S.Infinite) :
    ∃ R ⊆ S, R.Infinite ∧ DensityZero R := by
  classical
  let next (x : ℕ) := (h.exists_gt x).choose
  have spec (x : ℕ) : next x ∈ S ∧ x < next x := (h.exists_gt x).choose_spec
  let f : ℕ → ℕ := Nat.rec (next 1) (fun n prev => next (max prev ((n+2)^2)))
  have mem (j) : f j ∈ S := by cases j <;> exact (spec _).1
  have grow : StrictMono f := strictMono_nat_of_lt_succ (fun n => (le_max_left _ _).trans_lt (spec _).2)
  have square (j) : (j+1)^2 ≤ f j := by
    cases j with
    | zero => exact (spec 1).2.le
    | succ j => exact (le_max_right _ _).trans (spec _).2.le
  refine ⟨Set.range f,Set.range_subset_iff.mpr mem, Set.infinite_range_of_injective grow.injective,?_⟩
  intro k
  refine ⟨k^2,fun n hn => ?_⟩
  have cover : initial (Set.range f) n ⊆ (Finset.range n.sqrt).image f := by
    intro x hx
    obtain ⟨hx,⟨j,rfl⟩⟩ := mem_initial.mp hx
    have le := Nat.le_sqrt'.mpr ((square j).trans hx.le)
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr le)
  have bound : count (Set.range f) n ≤ n.sqrt := by
    exact (Finset.card_le_card cover).trans (Finset.card_image_le.trans_eq (Finset.card_range _))
  exact (Nat.mul_le_mul (Nat.le_sqrt'.mpr hn) bound).trans (Nat.sqrt_le _)

theorem density_proper : ¬DensityZero Set.univ := by
  intro h
  obtain ⟨N,hN⟩ := h 2
  have t := hN (N+1) (Nat.le_succ _)
  have c : count Set.univ (N+1) = N+1 := by simp [count,initial]
  rw [c,Nat.two_mul] at t
  exact (Nat.lt_add_of_pos_right (Nat.zero_lt_succ N)).not_ge t

/-- Asymptotic density zero gives the concrete tall proper ideal used in the paper. -/
def densityIdeal : TallIdeal ℕ where
  small := DensityZero
  down h ht k := by
    obtain ⟨N,hN⟩ := ht k
    exact ⟨N,fun n hn => (Nat.mul_le_mul_left k (count_mono h n)).trans (hN _ hn)⟩
  union := density_union
  finite := density_finite
  proper := density_proper
  tall := density_tall

end EDMRows

namespace EDMRows
variable (I : TallIdeal ℕ)

abbrev Atom := ℕ × ℕ
abbrev Support := ℕ → Set ℕ

def moved (g : Equiv.Perm ℕ) : Set ℕ := {a | g a ≠ a}

/-- Permutations with small moved set form the group acting on one row. -/
def rowGroup : Subgroup (Equiv.Perm ℕ) where
  carrier := {g | I.small (moved g)}
  one_mem' := by simpa [moved] using I.finite Set.finite_empty
  mul_mem' := by
    intro g h hg hh
    apply I.down _ (I.union hg hh)
    intro a ha
    by_contra! hn
    have h1 : g a = a := Classical.byContradiction (fun h => hn (Or.inl h))
    have h2 : h a = a := Classical.byContradiction (fun h => hn (Or.inr h))
    exact ha (by simp [h1,h2])
  inv_mem' := by
    intro g hg
    apply I.down _ hg
    intro a ha h
    exact ha (g.injective (by simp [h]))

/-- The full direct product, allowing independent permutations in infinitely
many rows, subject only to the small-moved-set condition in each row. -/
abbrev Group := ℕ → rowGroup I

instance : MulAction (Group I) Atom where
  smul := fun g a => (a.1,(g a.1).val a.2)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def Admissible (E : Support) : Prop := {n | ¬I.small (E n)}.Finite

def Fixes (g : Group I) (E : Support) : Prop := ∀ n a, a ∈ E n → (g n).val a = a

def Supports {V : Type*} [MulAction (Group I) V] (E : Support) (v : V) : Prop :=
  ∀ g : Group I, Fixes I g E → g • v = v

def FamilySupported {J V : Type*} [MulAction (Group I) V] (f : J → V) : Prop :=
  ∃ E : Support, Admissible I E ∧ ∀ j, Supports I E (f j)

def InternalInjection (f : Atom → ℕ) : Prop :=
  Function.Injective f ∧ ∃ E : Support, Admissible I E ∧
    ∀ (g : Group I), Fixes I g E → ∀ a, f (g • a) = f a

def row (n : ℕ) : Set Atom := {a | a.1 = n}

theorem small_swap (a b : ℕ) : Equiv.swap a b ∈ rowGroup I := by
  apply I.down (T := {a,b}) _ (I.finite ((Set.finite_singleton b).insert a))
  intro x hx
  by_contra! h
  have xa : x ≠ a := fun e => h (by simp [e])
  have xb : x ≠ b := fun e => h (by simp [e])
  exact hx (Equiv.swap_apply_of_ne_of_ne xa xb)

/-- A single transposition extended by the identity on every other row. -/
def swapAt (n a b : ℕ) (m : ℕ) : rowGroup I :=
  if m = n then ⟨Equiv.swap a b,small_swap I a b⟩ else 1

theorem swapAt_fixes (E : Support) {n a b : ℕ} (ha : a ∉ E n) (hb : b ∉ E n) :
    Fixes I (swapAt I n a b) E := by
  intro m z hz
  by_cases eq : m = n
  · subst m
    have aa : z ≠ a := fun e => ha (e ▸ hz)
    have bb : z ≠ b := fun e => hb (e ▸ hz)
    simpa [swapAt] using Equiv.swap_apply_of_ne_of_ne aa bb
  · simp [swapAt,eq]

theorem separates {f : Atom → ℕ} (h : InternalInjection I f) : False := by
  classical
  obtain ⟨inj,E,finite,fix⟩ := h
  have residual : ∃ n, I.small (E n) := by
    by_contra! all
    exact Set.infinite_univ (α := ℕ) (finite.subset (fun n _ => all n))
  obtain ⟨n,hn⟩ := residual
  obtain ⟨a,ha⟩ := (I.infinite_complement hn).nonempty
  obtain ⟨b,hb,bne⟩ := (I.infinite_complement hn).exists_gt a
  let g := swapAt I n a b
  have hmove : g • (n,a) = (n,b) := by change (n, (swapAt I n a b n).val a) = _; simp [swapAt]
  have eq := inj (fix g (swapAt_fixes I E ha hb) (n,a))
  exact bne.ne' (congrArg Prod.snd (hmove.symm.trans eq))

theorem row_enumerable (n : ℕ) : ∃ f : ℕ → Atom, Function.Injective f ∧
    Set.range f = row n ∧ FamilySupported I f := by
  let f (a : ℕ) := (n,a)
  have ran : Set.range f = row n := by ext ⟨m,a⟩; exact ⟨fun ⟨b,h⟩ => (congrArg Prod.fst h).symm,
    fun h => ⟨a,Prod.ext h.symm rfl⟩⟩
  let E (m : ℕ) : Set ℕ := if m = n then Set.univ else ∅
  have ok : Admissible I E := by
    apply (Set.finite_singleton n).subset
    intro m hm
    change m = n
    by_contra ne
    exact hm (by simpa [E,ne] using I.finite Set.finite_empty)
  refine ⟨f,fun _ _ e => congrArg Prod.snd e,ran,E,ok,fun a g h => ?_⟩
  exact Prod.ext rfl (h n a (by simp [E]))

/-- In the concrete density-zero support model the atom set is the disjoint
union of the invariant, internally denumerable rows. It has no supported
injection into the trivial natural-number sort. -/
theorem density_row_counterexample :
    (∀ (g : Group densityIdeal) n a, g • a ∈ row n ↔ a ∈ row n) ∧
    (Set.univ = ⋃ n, row n) ∧ (∀ n m, n ≠ m → Disjoint (row n) (row m)) ∧
    (∀ n, ∃ f : ℕ → Atom, Function.Injective f ∧ Set.range f = row n ∧ FamilySupported densityIdeal f) ∧
    ¬ ∃ f : Atom → ℕ, InternalInjection densityIdeal f := by
  refine ⟨fun _ _ _ => Iff.rfl, ?_, ?_, row_enumerable densityIdeal,fun ⟨_,h⟩ => separates _ h⟩
  · ext a
    exact ⟨fun _ => Set.mem_iUnion.mpr ⟨a.1,rfl⟩,fun _ => Set.mem_univ _⟩
  · intro n m ne
    exact Set.disjoint_left.mpr (fun a (ha : a.1 = n) (hb : a.1 = m) => ne (ha.symm.trans hb))

end EDMRows

namespace EDMRows
variable {A : Type*}

/-- Swap every point of D with its distinct image outside D, fixing the rest. -/
noncomputable def exchangeFun (D : Set A) (e : D ↪ A) (x : A) : A := by
  classical
  exact if hx : x ∈ D then e ⟨x,hx⟩ else if hr : x ∈ Set.range e then hr.choose.val else x

theorem exchange_left {D : Set A} (e : D ↪ A) (a : D) : exchangeFun D e a.val = e a :=
  dite_eq_left a.property

theorem exchange_right {D : Set A} (e : D ↪ A) (fresh : ∀ a, e a ∉ D) (a : D) :
    exchangeFun D e (e a) = a.val := by
  classical
  have hr : e a ∈ Set.range e := ⟨a,rfl⟩
  unfold exchangeFun
  rw [dite_eq_right (fresh a),dite_eq_left hr]
  exact congrArg Subtype.val (e.injective hr.choose_spec)

theorem exchange_outside {D : Set A} (e : D ↪ A) {x : A} (hd : x ∉ D) (hr : x ∉ Set.range e) :
    exchangeFun D e x = x := by classical exact (dite_eq_right hd).trans (dite_eq_right hr)

theorem exchange_involutive {D : Set A} (e : D ↪ A) (fresh : ∀ a, e a ∉ D) :
    Function.Involutive (exchangeFun D e) := by
  classical
  intro x
  by_cases h : x ∈ D
  · exact (congrArg (exchangeFun D e) (exchange_left e ⟨x,h⟩)).trans (exchange_right e fresh _)
  by_cases hr : x ∈ Set.range e
  · obtain ⟨a,rfl⟩ := hr
    rw [exchange_right e fresh a,exchange_left]
  · rw [exchange_outside e h hr,exchange_outside e h hr]

noncomputable def exchange {D : Set A} (e : D ↪ A) (fresh : ∀ a, e a ∉ D) : Equiv.Perm A :=
  (exchange_involutive e fresh).toPerm _

variable {I : TallIdeal ℕ}

/-- For two small row supports, conjugation by a permutation fixing T moves
the entire part S∖T off the moved set of g. -/
private theorem clear_row {S T : Set ℕ} (hs : I.small S) (ht : I.small T) (g : rowGroup I)
    (overlap : ∀ a ∈ S ∩ T, g.val a = a) :
    ∃ τ : rowGroup I, (∀ a ∈ T, τ.val a = a) ∧ ∀ a ∈ S, g.val (τ.val a) = τ.val a := by
  classical
  let D := S \ T
  let avoid := (S ∪ T) ∪ moved g.val
  have small : I.small avoid := I.union (I.union hs ht) g.property
  obtain ⟨R,empty,inf,hr⟩ := I.fresh_reserve small
  let := inf.to_subtype
  let embed := Infinite.natEmbedding R
  let e : D ↪ ℕ := ⟨fun a => (embed a.val).val,fun a b h => Subtype.ext (embed.injective (Subtype.ext h))⟩
  have inside (a : D) : e a ∈ R := (embed a.val).property
  have fresh (a : D) : e a ∉ D := fun hd => empty (inside a) (Or.inl (Or.inl hd.1))
  let σ := exchange e fresh
  have permitted : σ ∈ rowGroup I := by
    apply I.down (T := S ∪ R) _ (I.union hs hr)
    intro x hx
    by_contra outside
    have hd : x ∉ D := fun hh => outside (Or.inl hh.1)
    have no : x ∉ Set.range e := fun ⟨a,ha⟩ => outside (Or.inr (ha ▸ inside a))
    exact hx (exchange_outside _ hd no)
  refine ⟨⟨σ,permitted⟩,?_,?_⟩
  · intro a ha
    exact exchange_outside e (fun h => h.2 ha)
      (fun ⟨b,eq⟩ => empty (inside b) (Or.inl (Or.inr (eq ▸ ha))))
  · intro a ha
    by_cases inT : a ∈ T
    · have eq : σ a = a := exchange_outside e (fun hd => hd.2 inT)
        (fun ⟨b,eq⟩ => empty (inside b) (Or.inl (Or.inr (eq ▸ inT))))
      rw [eq]
      exact overlap a ⟨ha,inT⟩
    · let b : D := ⟨a,ha,inT⟩
      have eq : σ a = e b := exchange_left e b
      rw [eq]
      exact Classical.byContradiction (fun moved' => empty (inside b) (Or.inr moved'))

/-- Intersect two supports when each pair of row sections is either small or
identical. This includes the paper's common full exceptional rows. The three
factors of a permutation are assembled simultaneously in the full product. -/
theorem supports_intersection {V : Type*} [MulAction (Group I) V] (x : V) (S T : Support)
    (sections : ∀ n, S n = T n ∨ I.small (S n) ∧ I.small (T n))
    (hs : Supports I S x) (ht : Supports I T x) : Supports I (fun n => S n ∩ T n) x := by
  classical
  intro g fix
  have section' (n : ℕ) : ∃ τ : rowGroup I, (∀ a ∈ T n, τ.val a = a) ∧
      ∀ a ∈ S n, (g n).val (τ.val a) = τ.val a := by
    rcases sections n with eq | ⟨s,t⟩
    · exact ⟨1,fun _ _ => rfl,fun a ha => fix n a ⟨ha,eq ▸ ha⟩⟩
    · exact clear_row s t _ (fix n)
  choose τ τT inner using section'
  have fixx := ht τ τT
  have fx : Fixes I (τ⁻¹ * g * τ) S := by
    intro n a ha
    change (τ n).val.symm ((g n).val ((τ n).val a)) = a
    rw [inner n a ha,(τ n).val.symm_apply_apply]
  have eq := congrArg (fun y => τ • y) (hs _ fx)
  simpa only [mul_smul,smul_inv_smul,fixx] using eq

end EDMRows
