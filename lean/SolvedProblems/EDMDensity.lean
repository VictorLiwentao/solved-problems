module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range

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
