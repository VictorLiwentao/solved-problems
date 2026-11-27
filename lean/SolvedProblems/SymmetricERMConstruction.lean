module

public import SolvedProblems.SymmetricERMModel
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find

@[expose] public section

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
