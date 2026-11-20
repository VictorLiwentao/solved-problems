module

public import SolvedProblems.PartitionRamseyModel
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Basic.Denumerable

public section

namespace SolvedProblems.PartitionRamsey

open Set Filter

private theorem le_iff (s t : Set ℕ) : classOf s ≤ classOf t ↔ (s \ t).Finite := by
  change (∀ᶠ x in cofinite, x ∈ s → x ∈ t) ↔ _
  rw [eventually_cofinite]
  simp only [not_imp]
  rfl

private theorem not_le_of_rows (s t : Set ℕ) (e : ℕ → ℕ) (h : Function.Injective e)
    (hs : ∀ i, e i ∈ s) (ht : ∀ i, e i ∉ t) : ¬ classOf s ≤ classOf t := by
  intro hle
  apply Set.infinite_range_of_injective h
  exact ((le_iff _ _).1 hle).subset (by rintro _ ⟨i, rfl⟩; exact ⟨hs i, ht i⟩)

private theorem infinite_quotient : Infinite ModFinite := by
  let col (n : ℕ) : Set ℕ := {a | a.unpair.1 = n}
  apply Infinite.of_injective (fun n => classOf (col n))
  intro m n h
  by_contra hne
  apply not_le_of_rows (col m) (col n) (Nat.pair m) _ _ _ h.le
  · intro i j e
    simpa using congrArg (fun n : ℕ => n.unpair.2) e
  · intro i
    simp [col]
  · intro i
    simpa [col] using hne

private theorem order_invariant (π : Equiv.Perm ℕ) (s t : Set ℕ) :
    classOf (π ⁻¹' s) ≤ classOf (π ⁻¹' t) ↔ classOf s ≤ classOf t := by
  rw [le_iff, le_iff, ← Set.preimage_sdiff]
  exact ⟨fun h => h.of_preimage π.surjective, fun h => h.preimage π.injective.injOn⟩

private theorem points_supported (a : ModFinite) : Supported {a} := by
  classical
  induction a using Germ.inductionOn with
  | _ s =>
    let block (x : ℕ) : Fin 2 := if s x then 1 else 0
    refine ⟨2, block, fun π hp t => ?_⟩
    have fixed : π ⁻¹' (s : Set ℕ) = s := by
      ext x
      change s (π x) ↔ s x
      specialize hp x
      by_cases h : s x <;> by_cases h' : s (π x) <;> simp_all [block]
    change classOf t = classOf s ↔ classOf (π ⁻¹' t) = classOf s
    conv_rhs => rhs; rw [← fixed]
    simp only [le_antisymm_iff]
    exact ((order_invariant π t s).and (order_invariant π s t)).symm

/-- If no block is split into two infinite pieces, the class is a union of blocks. -/
private theorem split_block {k : ℕ} (block : ℕ → Fin k) (Y : Set ModFinite) (hy : Y.Infinite) :
    ∃ (s : Set ℕ) (i : Fin k), classOf s ∈ Y ∧
      {x | block x = i ∧ x ∈ s}.Infinite ∧ {x | block x = i ∧ x ∉ s}.Infinite := by
  classical
  let rounded (w : Fin k → Bool) := classOf {x | w (block x) = true}
  obtain ⟨a, ha, hn⟩ := hy.exists_notMem_finite (Set.finite_range rounded)
  induction a using Germ.inductionOn with
  | _ s =>
    change classOf s ∈ Y at ha
    by_contra! h
    let w (i : Fin k) := decide ({x | block x = i ∧ s x}.Infinite)
    apply hn
    refine ⟨w, Germ.coe_eq.2 ?_⟩
    change ∀ᶠ x in cofinite, (w (block x) = true) = s x
    apply eventually_cofinite.2
    let bad (i : Fin k) : Set ℕ :=
      if {x | block x = i ∧ s x}.Infinite then {x | block x = i ∧ ¬s x}
      else {x | block x = i ∧ s x}
    apply (Set.finite_iUnion (f := bad) (fun i => ?_)).subset
    · intro x hx
      simp only [Set.mem_iUnion]
      refine ⟨block x, ?_⟩
      change ¬((w (block x) = true) = s x) at hx
      by_cases hi : {y | block y = block x ∧ s y}.Infinite <;>
        simp_all [w, bad]
    · by_cases hi : {x | block x = i ∧ s x}.Infinite
      · rw [show bad i = {x | block x = i ∧ ¬s x} from if_pos hi]
        exact h s i ha hi
      · rw [show bad i = {x | block x = i ∧ s x} from if_neg hi]
        exact of_not_not hi

private abbrev Grid := ℕ × ℤ

/-- Embed infinitely many parallel integer lines in the split block, with precisely their
nonnegative halves in the representative. Points beyond this grid will stay fixed. -/
private theorem make_grid {k : ℕ} (block : ℕ → Fin k) (s : Set ℕ) (i : Fin k)
    (hp : {x | block x = i ∧ x ∈ s}.Infinite) (hn : {x | block x = i ∧ x ∉ s}.Infinite) :
    ∃ g : Grid ↪ ℕ, (∀ p, block (g p) = i) ∧ (∀ p, g p ∈ s ↔ 0 ≤ p.2) := by
  classical
  let pos := Set.Infinite.natEmbedding _ hp
  let neg := Set.Infinite.natEmbedding _ hn
  let f (p : Grid) : ℕ := if 0 ≤ p.2 then (pos (Encodable.encode p)).val
    else (neg (Encodable.encode p)).val
  have mem (p : Grid) : f p ∈ s ↔ 0 ≤ p.2 := by
    by_cases he : 0 ≤ p.2
    · simpa [f, he] using (pos (Encodable.encode p)).property.2
    · simpa [f, he] using (neg (Encodable.encode p)).property.2
  have inj : Function.Injective f := by
    intro p q eq
    have side : 0 ≤ p.2 ↔ 0 ≤ q.2 := (mem p).symm.trans (eq ▸ mem q)
    by_cases h : 0 ≤ p.2
    · have hq := side.mp h
      exact Encodable.encode_injective (pos.injective (Subtype.ext (by simpa [f, h, hq] using eq)))
    · have hq := mt side.mpr h
      exact Encodable.encode_injective (neg.injective (Subtype.ext (by simpa [f, h, hq] using eq)))
  refine ⟨⟨f, inj⟩, fun p => ?_, mem⟩
  change block (f p) = i
  by_cases h : 0 ≤ p.2
  · simpa [f, h] using (pos (Encodable.encode p)).property.1
  · simpa [f, h] using (neg (Encodable.encode p)).property.1

private def shift : Equiv.Perm Grid where
  toFun p := (p.1, p.2 - 1)
  invFun p := (p.1, p.2 + 1)
  left_inv p := by simp
  right_inv p := by simp

private def reflect : Equiv.Perm Grid where
  toFun p := (p.1, -p.2 - 1)
  invFun p := (p.1, -p.2 - 1)
  left_inv p := by obtain ⟨a,b⟩ := p; simp
  right_inv p := by obtain ⟨a,b⟩ := p; simp

private theorem both_pairs (Y : Set ModFinite) (hY : Supported Y) (hy : Y.Infinite) :
    (∃ a ∈ Y, ∃ b ∈ Y, a < b) ∧ (∃ a ∈ Y, ∃ b ∈ Y, ¬ a ≤ b ∧ ¬ b ≤ a) := by
  classical
  obtain ⟨k, block, supp⟩ := hY
  obtain ⟨s, i, hs, hpos, hneg⟩ := split_block block Y hy
  obtain ⟨g, hg, hmem⟩ := make_grid block s i hpos hneg
  let moved (e : Equiv.Perm Grid) := (e.viaEmbedding g) ⁻¹' s
  have moved_mem (e : Equiv.Perm Grid) : classOf (moved e) ∈ Y := by
    apply (supp _ _ s).mp hs
    intro x
    by_cases hx : x ∈ Set.range g
    · obtain ⟨p, rfl⟩ := hx
      rw [Equiv.Perm.viaEmbedding_apply, hg, hg]
    · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]
  have on_grid (e : Equiv.Perm Grid) (p : Grid) : g p ∈ moved e ↔ 0 ≤ (e p).2 := by
    change e.viaEmbedding g (g p) ∈ s ↔ _
    rw [Equiv.Perm.viaEmbedding_apply, hmem]
  have row_inj (z : ℤ) : Function.Injective (fun n : ℕ => g (n,z)) :=
    fun _ _ h => congrArg Prod.fst (g.injective h)
  refine ⟨⟨_, moved_mem shift, _, hs, lt_of_le_not_ge ?_ ?_⟩,
    ⟨_, hs, _, moved_mem reflect, ?_, ?_⟩⟩
  · apply Germ.coe_le.2 (Filter.Eventually.of_forall _)
    intro x hx
    by_cases hgx : x ∈ Set.range g
    · obtain ⟨p, rfl⟩ := hgx
      have h := (on_grid shift p).mp hx
      change 0 ≤ p.2 - 1 at h
      exact (hmem p).mpr (by omega)
    · change shift.viaEmbedding g x ∈ s at hx
      rwa [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hgx] at hx
  · exact not_le_of_rows _ _ _ (row_inj 0) (fun n => (hmem _).mpr (by change (0 : ℤ) ≤ 0; decide))
      (fun n h => by have := (on_grid shift _).mp h; exact (by decide : ¬ (0 : ℤ) ≤ 0-1) this)
  · exact not_le_of_rows _ _ _ (row_inj 0) (fun n => (hmem _).mpr (by change (0 : ℤ) ≤ 0; decide))
      (fun n h => by have := (on_grid reflect _).mp h; exact (by decide : ¬ (0 : ℤ) ≤ -0-1) this)
  · exact not_le_of_rows _ _ _ (row_inj (-1)) (fun n => (on_grid reflect _).mpr (by change (0 : ℤ) ≤ -(-1)-1; decide))
      (fun n h => (by decide : ¬ (0 : ℤ) ≤ -1) ((hmem _).mp h))

/-- In Bruce's finite partition model the quotient is an infinite poset, each point has
a finite partition support, and comparability colours both ways on every infinite internal
family. The strict comparison gives two distinct comparable points. -/
theorem finitePartitionRamsey :
    Infinite ModFinite ∧ (∀ a : ModFinite, Supported {a}) ∧
    (∀ (π : Equiv.Perm ℕ) (s t : Set ℕ),
      classOf (π ⁻¹' s) ≤ classOf (π ⁻¹' t) ↔ classOf s ≤ classOf t) ∧
    ∀ Y : Set ModFinite, Supported Y → Y.Infinite →
      (∃ a ∈ Y, ∃ b ∈ Y, a < b) ∧
      (∃ a ∈ Y, ∃ b ∈ Y, ¬ a ≤ b ∧ ¬ b ≤ a) := by
  exact ⟨infinite_quotient, points_supported, order_invariant, both_pairs⟩

end SolvedProblems.PartitionRamsey
