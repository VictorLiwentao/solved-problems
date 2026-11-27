module

public import SolvedProblems.ChoiceOmegaOneEscape
public import SolvedProblems.ChoiceOmegaOneFilter

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Subgroup
open scoped commutatorElement

variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V]

def blockFix (T : Set I) : Subgroup (I → P) where
  carrier := {g | ∀ i ∈ T, g i=1}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb i hi := by simp [ha i hi,hb i hi]
  inv_mem' {a} ha i hi := by simp [ha i hi]

structure Move (I : Type u) (P : Type v) [Group P] (blocks : ℕ → Set I) where
  tag : ℕ
  a : I → P
  b : I → P
  offA : ∀ i ∉ blocks tag, a i=1
  offB : ∀ i ∉ blocks tag, b i=1

namespace Move

variable {blocks : ℕ → Set I}

def gens (l : List (Move I P blocks)) : Finset (I → P) := by
  classical
  exact (l.map Move.a ++ l.map Move.b).toFinset

def earlier (l : List (Move I P blocks)) : Subgroup (I → P) := Subgroup.closure (gens l : Set _)

theorem generators_mem {l : List (Move I P blocks)} {m : Move I P blocks} (h : m ∈ l) :
    m.a ∈ earlier l ∧ m.b ∈ earlier l := by
  classical
  constructor <;> apply Subgroup.subset_closure
  · exact List.mem_toFinset.2 (List.mem_append_left _ (List.mem_map.2 ⟨m,h,rfl⟩))
  · exact List.mem_toFinset.2 (List.mem_append_right _ (List.mem_map.2 ⟨m,h,rfl⟩))

private theorem later (s : ℕ) (l : List (Move I P blocks)) (higher : ∀ m ∈ l, m.tag < s)
    (apart : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) : earlier l ≤ blockFix (blocks s) := by
  classical
  apply (Subgroup.closure_le _).2
  intro f hf
  have h := List.mem_append.1 (List.mem_toFinset.1 (show f ∈ gens l from hf))
  rcases h with h | h
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.1 h
    exact fun i hi => m.offA i (fun old => Set.disjoint_left.1 (apart (higher m hm).ne) old hi)
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.1 h
    exact fun i hi => m.offB i (fun old => Set.disjoint_left.1 (apart (higher m hm).ne) old hi)

/-- Select a previously unused block and a commutator carrying the point
outside the entire orbit of all the generators picked earlier. -/
theorem next [Finite P] (perfect : commutator P = ⊤)
    (apart : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) (x : V)
    (positive : ∀ n, ¬ PointSupport (P := P) (blocks n)ᶜ x) (l : List (Move I P blocks)) :
    ∃ m : Move I P blocks, (∀ k ∈ l, k.tag < m.tag) ∧ ⁅m.a,m.b⁆ • x ∉ MulAction.orbit (earlier l) x := by
  classical
  let N := l.toFinset.sup Move.tag + 1
  have tag_lt (m : Move I P blocks) (h : m ∈ l) : m.tag < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := Move.tag) (List.mem_toFinset.2 h))
  let s (n : ℕ) := blocks (N+n)
  let φ (n : ℕ) := blockMap (P := P) (s n)
  let L := earlier l
  have finite : Finite L := locally_finite_power (gens l)
  have central (n : ℕ) (a : s n → P) (g : I→P) (hg : g∈L) : Commute (φ n a) g := by
    funext i
    by_cases hi : i∈s n
    · have e : g i=1 := later (N+n) l (fun m hm => (tag_lt m hm).trans_le (Nat.le_add_right ..)) apart hg i hi
      simp [e]
    · simp [φ,blockMap,hi]
  have pos (n : ℕ) : ∃ a : s n → P, φ n a • x ≠ x := by
    by_contra! h
    apply positive (N+n)
    intro g hg
    have eq : φ n (fun i => g i.val) = g := by
      funext i; by_cases hi : i∈s n
      · simp [φ,blockMap,hi]
      · simp [φ,blockMap,hi,hg i hi]
    exact eq ▸ h _
  obtain ⟨n,a,b,esc⟩ := escape φ (fun _ => perfect_power perfect)
    (fun i j ne => block_commute (apart (fun e => ne (Nat.add_left_cancel e)))) L x pos central
  have off (a : s n → P) (i : I) (hi : i∉s n) : φ n a i=1 := by simp [φ,blockMap,hi]
  refine ⟨⟨N+n,φ n a,φ n b,off a,off b⟩,fun m hm => (tag_lt m hm).trans_le (Nat.le_add_right ..),?_⟩
  rwa [map_commutatorElement] at esc

end Move

/-- Pairwise disjoint blocks whose selected commutators are independent at the
point: the greatest index in any nonempty finite product forces motion. -/
structure Witness (I : Type u) (P : Type v) [Group P] (V : Type w) [MulAction (I→P) V] (x : V) where
  blocks : ℕ → Set I
  apart : Pairwise (fun i j => Disjoint (blocks i) (blocks j))
  a : ℕ → I → P
  b : ℕ → I → P
  offA : ∀ n i, i ∉ blocks n → a n i=1
  offB : ∀ n i, i ∉ blocks n → b n i=1
  moves : ∀ (n : ℕ) (l : List ℕ), (∀ j ∈ l, j<n) →
    ((l.map (fun j => ⁅a j,b j⁆)).prod * ⁅a n,b n⁆) • x ≠ x

theorem witness_of_disjoint [Finite P] (perfect : commutator P = ⊤) (s : ℕ → Set I)
    (apart : Pairwise (fun i j => Disjoint (s i) (s j))) (x : V)
    (positive : ∀ n, ¬ PointSupport (P := P) (s n)ᶜ x) : Nonempty (Witness I P V x) := by
  classical
  choose pick high step using Move.next perfect apart x positive
  let hist : ℕ → List (Move I P s) := Nat.rec [] (fun _ l => pick l :: l)
  let m (n : ℕ) := pick (hist n)
  have earlier {i j : ℕ} (h : i < j) : m i ∈ hist j := by
    induction j with
    | zero => omega
    | succ j ih =>
      change m i ∈ m j :: hist j
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
      · exact List.mem_cons_of_mem _ (ih h)
      · exact List.mem_cons_self
  have strict : StrictMono (fun n => (m n).tag) := fun _ _ lt => high _ _ (earlier lt)
  refine ⟨⟨fun n => s (m n).tag,fun i j ne => apart (fun eq => ne (strict.injective eq)),fun n => (m n).a,
     fun n => (m n).b,fun n => (m n).offA,fun n => (m n).offB,?_⟩⟩
  intro n l bound fix
  let L := Move.earlier (hist n)
  let p := (l.map (fun j => ⁅(m j).a,(m j).b⁆)).prod
  have hp : p ∈ L := L.list_prod_mem (by
    intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_map.1 hg
    obtain ⟨ha,hb⟩ := Move.generators_mem (earlier (bound j hj))
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb))
  apply step (hist n)
  refine MulAction.mem_orbit_iff.2 ⟨⟨p⁻¹,L.inv_mem hp⟩,?_⟩
  have h : p • (⁅(m n).a,(m n).b⁆ • x) = x := (mul_smul ..).symm.trans fix
  exact (inv_smul_eq_iff.mpr h.symm)

end ChoiceOmegaOne
