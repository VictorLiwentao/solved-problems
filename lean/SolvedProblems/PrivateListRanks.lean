module

public import SolvedProblems.PrivateListRectangle

@[expose] public section

namespace PrivateList

open MeasureTheory
open scoped Classical

def AtRank {m L} (a : Fin m → Fin L) (r : Fin (m+1)) (z : Fin L) : Prop :=
  (∀ i, i.val < r.val → a i < z) ∧ (∀ i, r.val ≤ i.val → z < a i)

theorem insert_rank {m L} {a : Fin m → Fin L} (ha : StrictMono a) (r : Fin (m+1)) (z : Fin L)
    (atR : AtRank a r z) : ∃ e : Fin (m+1) ↪o Fin L, e r = z ∧ ∀ i, e (r.succAbove i) = a i := by
  let f : Fin (m+1) → Fin L := Fin.insertNth (α := fun _ => Fin L) r z a
  have increasing (i j : Fin (m+1)) : i < j → f i < f j := by
    revert j
    refine r.succAboveCases ?_ (fun u => ?_) i
    · intro j
      refine r.succAboveCases ?_ (fun v h => ?_) j
      · exact fun h => (lt_irrefl _ h).elim
      · simpa [f] using atR.2 v ((Fin.lt_succAbove_iff_le_castSucc r v).mp h)
    · intro j
      refine r.succAboveCases ?_ (fun v h => ?_) j
      · intro h
        simpa [f] using atR.1 u ((Fin.succAbove_lt_iff_castSucc_lt r u).mp h)
      · simpa [f] using ha (Fin.succAbove_lt_succAbove_iff.mp h)
  exact ⟨OrderEmbedding.ofStrictMono f (fun _ _ h => increasing _ _ h),
    Fin.insertNth_apply_same (α := fun _ => Fin L) r z a,
    fun i => Fin.insertNth_apply_succAbove (α := fun _ => Fin L) r z a i⟩

def HomogeneousOn {k m Ω L} [MeasurableSpace Ω] (A : Rule k m Ω) (T : Template k m)
    (X Y : Fin L ↪o ℕ) (v : Cell m → Label k → ℝ) (τ : ℝ) : Prop :=
  ∀ a b : Fin (m+1) ↪o Fin L, ∀ i y,
    |lookup A T (fun n => X (a n)) (fun n => Y (b n)) i y - v i y| ≤ τ

theorem local_rank {k m Ω L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ} (hom : HomogeneousOn A T X Y v τ)
    {a b : Fin m → Fin L} (ha : StrictMono a) (hb : StrictMono b) (r : Cell m) (x y : Fin L)
    (hx : AtRank a r.1 x) (hy : AtRank b r.2 y) (label : Label k) :
    |omission A (place T (X ∘ a) (Y ∘ b)) (X x,Y y) label - v r label| ≤ τ := by
  obtain ⟨u,ux,us⟩ := insert_rank ha r.1 x hx
  obtain ⟨w,wy,ws⟩ := insert_rank hb r.2 y hy
  simpa [lookup,ux,wy,us,ws,Function.comp_def] using hom u w r label

def spaced {m L} (room : 2*m+1 ≤ L) (i : Fin m) : Fin L := ⟨2*i.val+1, by omega⟩

def shifted {m L} (room : 2*m+1 ≤ L) (j i : Fin m) : Fin L :=
  ⟨if i=j then 2*i.val else 2*i.val+1, by split <;> omega⟩

theorem shifted_mono {m L} (room : 2*m+1 ≤ L) (j : Fin m) : StrictMono (shifted room j) := by
  intro a b hab
  change (if a=j then 2*a.val else 2*a.val+1) < if b=j then 2*b.val else 2*b.val+1
  have : a.val < b.val := hab
  split <;> split <;> omega

theorem shifted_rank {m L} (room : 2*m+1 ≤ L) (j : Fin m) :
    AtRank (shifted room j) j.succ (spaced room j) := by
  constructor
  · intro i hi
    change (if i=j then 2*i.val else 2*i.val+1) < 2*j.val+1
    change i.val < j.val+1 at hi
    split <;> rename_i h
    · subst i; omega
    · have : i.val ≠ j.val := fun e => h (Fin.ext e)
      omega
  · intro i hi
    change 2*j.val+1 < if i=j then 2*i.val else 2*i.val+1
    change j.val+1 ≤ i.val at hi
    split <;> omega

theorem shifted_neighbor {k m L} (T : Template k m) (room : 2*m+1 ≤ L)
    (X Y : Fin L ↪o ℕ) (i : Fin m) :
    Neighbors (place T (X ∘ spaced room) (Y ∘ spaced room))
      (place T (X ∘ shifted room (T.xRank i)) (Y ∘ shifted room (T.yRank i))) := by
  refine ⟨i,fun j h => ?_⟩
  have hx : T.xRank j ≠ T.xRank i := fun e => h (T.xRank.injective e)
  have hy : T.yRank j ≠ T.yRank i := fun e => h (T.yRank.injective e)
  simp [place,spaced,shifted,hx,hy]

theorem Neighbors.symm {X : Type} {m} {s t : Fin m → X} (h : Neighbors s t) : Neighbors t s := by
  obtain ⟨i,eq⟩ := h
  exact ⟨i,fun j h => (eq j h).symm⟩

/-- A single neighbouring replacement makes the old training point a fresh
query while preserving all within-axis sample orders. -/
theorem training_cells {k m Ω L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ δ} (hom : HomogeneousOn A T X Y v τ) (priv : Private A 2 δ)
    (room : 2*m+1 ≤ L) (i : Fin m) (lab : Label k) :
    let s := place T (X ∘ spaced room) (Y ∘ spaced room)
    let r : Cell m := ((T.xRank i).succ,(T.yRank i).succ)
    v r lab ≤ 2*omission A s (s i).1 lab + δ + τ ∧
      omission A s (s i).1 lab ≤ 2*(v r lab+τ)+δ := by
  let r : Cell m := ((T.xRank i).succ,(T.yRank i).succ)
  let s := place T (X ∘ spaced room) (Y ∘ spaced room)
  let s' := place T (X ∘ shifted room (T.xRank i)) (Y ∘ shifted room (T.yRank i))
  let z := (s i).1
  have neigh : Neighbors s s' := shifted_neighbor T room X Y i
  have close : |omission A s' z lab - v r lab| ≤ τ := local_rank hom
    (shifted_mono room _) (shifted_mono room _) r _ _ (shifted_rank ..) (shifted_rank ..) lab
  have one : omission A s' z lab ≤ 2*omission A s z lab + δ := priv s s' neigh _ (A.measurable z lab)
  have two : omission A s z lab ≤ 2*omission A s' z lab + δ := priv s' s neigh.symm _ (A.measurable z lab)
  obtain ⟨l,u⟩ := abs_le.mp close
  change v r lab ≤ 2*omission A s z lab+δ+τ ∧ omission A s z lab ≤ 2*(v r lab+τ)+δ
  constructor <;> linarith

end PrivateList
