module

public import SolvedProblems.ProjectiveZFFormulas
public import Mathlib.Data.Set.Lattice.Image

@[expose] public section

namespace ProjectiveZF

open Set Function

/-- The fragment of pure ZF used below: Extensionality, Pairing, Union,
Power Set, and Separation for actual membership-language formulas with set
parameters. No well-foundedness or standardness of the model is imposed. -/
structure Core (V : Type*) [Membership V V] : Prop where
  ext : ∀ a b : V, (∀ x, x ∈ a ↔ x ∈ b) → a = b
  pairing : ∀ a b : V, ∃ p : V, IsDouble a b p
  union : ∀ a : V, ∃ u : V, ∀ x, x ∈ u ↔ ∃ y, y ∈ a ∧ x ∈ y
  power : ∀ a : V, ∃ p : V, ∀ x, x ∈ p ↔ ∀ y, y ∈ x → y ∈ a
  separation : ∀ (a : V) (P : V → Prop), Unary P → ∃ b : V, ∀ x, x ∈ b ↔ x ∈ a ∧ P x

variable {V : Type*} [Membership V V] (M : Core V)

/-- The external extent of an internal set. -/
def elts (a : V) : Set V := {x | x ∈ a}

noncomputable def double (a b : V) : V := (M.pairing a b).choose
noncomputable def single (a : V) : V := double M a a
noncomputable def ordered (a b : V) : V := double M (single M a) (double M a b)
noncomputable def power (a : V) : V := (M.power a).choose
noncomputable def both (a b : V) : V := (M.union (double M a b)).choose

@[simp] theorem mem_double {a b t : V} : t ∈ double M a b ↔ t = a ∨ t = b := (M.pairing a b).choose_spec t
@[simp] theorem mem_single {a t : V} : t ∈ single M a ↔ t = a := by simp [single]
@[simp] theorem mem_power {a t : V} : t ∈ power M a ↔ ∀ x, x ∈ t → x ∈ a := (M.power a).choose_spec t
@[simp] theorem mem_both {a b t : V} : t ∈ both M a b ↔ t ∈ a ∨ t ∈ b := by
  rw [both,(M.union (double M a b)).choose_spec]; simp [or_and_right,exists_or]

@[simp] theorem single_iff (a z : V) : IsSingle a z ↔ z = single M a := by
  refine ⟨fun h => M.ext _ _ (fun x => (h x).trans (mem_single M).symm),?_⟩
  rintro rfl x
  exact mem_single M

@[simp] theorem double_iff (a b z : V) : IsDouble a b z ↔ z = double M a b := by
  refine ⟨fun h => M.ext _ _ (fun x => (h x).trans (mem_double M).symm),?_⟩
  rintro rfl x
  exact mem_double M

@[simp] theorem pair_iff (a b z : V) : IsPair a b z ↔ z = ordered M a b := by
  refine ⟨fun h => M.ext _ _ (fun x => ?_),?_⟩
  · simpa only [ordered,mem_double,single_iff M,double_iff M] using h x
  · rintro rfl x
    simp [ordered,single_iff M,double_iff M]

@[simp] theorem edge_iff (f a b : V) : Edge f a b ↔ ordered M a b ∈ f := by simp [Edge,pair_iff M]

private theorem ext_double (a b : V) : elts (double M a b) = {a,b} := by ext x; exact mem_double M
private theorem ext_single (a : V) : elts (single M a) = {a} := by ext x; exact mem_single M

/-- Equality of Kuratowski ordered pairs implies equality of both entries in
any extensional membership structure with pairing. -/
theorem ordered_inj {a b c d : V} (eq : ordered M a b = ordered M c d) : a = c ∧ b = d := by
  have family := congrArg (fun z => elts '' elts z) eq
  simp only [ordered,ext_double,Set.image_insert_eq,Set.image_singleton,ext_single] at family
  have common (a b : V) : ∀ W ∈ ({{a},{a,b}} : Set (Set V)), a ∈ W := by simp
  have cIn : {c} ∈ ({{a},{a,b}} : Set (Set V)) := by rw [family]; simp
  have ac : a = c := Set.mem_singleton_iff.mp (common a b {c} cIn)
  subst c
  have union (a b x : V) : (∃ W ∈ ({{a},{a,b}} : Set (Set V)), x ∈ W) ↔ x = a ∨ x = b := by simp
  have same (x : V) : x = a ∨ x = b ↔ x = a ∨ x = d := by rw [← union a b x,family,union]
  have hb := (same b).mp (Or.inr rfl)
  have hd := (same d).mpr (Or.inr rfl)
  exact ⟨rfl,by rcases hb with h|h <;> rcases hd with k|k <;> grind⟩

include M in
theorem pair_coords {p x y a b : V} (h : IsPair x y p) (h' : IsPair a b p) : x = a ∧ y = b :=
  ordered_inj M (((pair_iff M _ _ _).mp h).symm.trans ((pair_iff M _ _ _).mp h'))

/-- A common set bounding every possible internal ordered pair from `X × Y`. -/
noncomputable def pairBound (X Y : V) := power M (power M (both M X Y))

theorem pair_mem_bound {X Y x y : V} (hx : x ∈ X) (hy : y ∈ Y) : ordered M x y ∈ pairBound M X Y := by
  rw [pairBound,mem_power]
  intro z hz
  rcases (mem_double M).mp hz with rfl|rfl
  · rw [mem_power]
    intro t ht
    exact (mem_single M).mp ht ▸ (mem_both M).mpr (Or.inl hx)
  · rw [mem_power]
    intro t ht
    rcases (mem_double M).mp ht with rfl|rfl
    · exact (mem_both M).mpr (Or.inl hx)
    · exact (mem_both M).mpr (Or.inr hy)

end ProjectiveZF
