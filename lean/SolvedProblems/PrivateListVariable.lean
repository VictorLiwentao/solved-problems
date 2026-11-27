module

public import SolvedProblems.PrivateListRanks

@[expose] public section

namespace PrivateList

open MeasureTheory
open scoped Classical

/-- All data coordinates on an axis stay fixed except rank j, which sweeps a
reserved interval of N values. -/
def varying {m N L} (room : m+N+2 ≤ L) (j : Fin m) (t : Fin N) (i : Fin m) : Fin L :=
  ⟨if i < j then i.val else if i=j then j.val+t.val else i.val+N, by split_ifs <;> omega⟩

def sweep {m N L} (room : m+N+2 ≤ L) (j : Fin m) (t : Fin N) : Fin L :=
  ⟨j.val+t.val,by omega⟩

theorem varying_mono {m N L} (room : m+N+2 ≤ L) (j : Fin m) (t : Fin N) :
    StrictMono (varying room j t) := by
  intro i l hil
  have ord : i.val < l.val := hil
  simp only [varying,Fin.lt_def,Fin.ext_iff]
  split_ifs <;> omega

theorem varying_left {m N L} (room : m+N+2 ≤ L) (j : Fin m) {u t : Fin N} (ut : u<t) :
    AtRank (varying room j t) j.castSucc (sweep room j u) := by
  have : u.val < t.val := ut
  constructor <;> intro i hi <;> 
    simp only [varying,sweep,Fin.lt_def,Fin.ext_iff,Fin.val_castSucc] at * <;>
    split_ifs <;> omega

theorem varying_right {m N L} (room : m+N+2 ≤ L) (j : Fin m) {u t : Fin N} (tu : t<u) :
    AtRank (varying room j t) j.succ (sweep room j u) := by
  have : t.val < u.val := tu
  constructor <;> intro i hi <;>
    simp only [varying,sweep,Fin.lt_def,Fin.ext_iff,Fin.val_succ] at * <;>
    split_ifs <;> omega

def holding {m L} (room : m+1 ≤ L) (h : Fin (m+1)) (i : Fin m) : Fin L :=
  ⟨if i.val < h.val then i.val else i.val+1,by split <;> omega⟩

def spare {m L} (room : m+1 ≤ L) (h : Fin (m+1)) : Fin L := ⟨h.val,by omega⟩

theorem holding_mono {m L} (room : m+1 ≤ L) (h : Fin (m+1)) : StrictMono (holding room h) := by
  intro i j lt
  have : i.val < j.val := lt
  simp only [holding,Fin.lt_def]
  split <;> split <;> omega

theorem holding_rank {m L} (room : m+1 ≤ L) (h : Fin (m+1)) :
    AtRank (holding room h) h (spare room h) := by
  constructor <;> intro i hi <;> simp [holding,spare,Fin.lt_def,hi,Nat.not_lt.mpr]

theorem sweep_neighbor {k m N L} (T : Template k m) (room : m+N+2 ≤ L) (j : Fin m)
    (X : Fin L ↪o ℕ) (b : Fin m → ℕ) (u t : Fin N) :
    Neighbors (place T (X ∘ varying room j u) b) (place T (X ∘ varying room j t) b) := by
  refine ⟨T.xRank.symm j,fun i h => ?_⟩
  have hn : T.xRank i ≠ j := fun he => h (T.xRank.eq_symm_apply.mpr he)
  simp [place,varying,hn]

/-- Reversing the two axes lets exactly the same sweep test vertical rank-cell jumps. -/
def swappedRule {k m Ω} [MeasurableSpace Ω] (A : Rule k m Ω) : Rule k m Ω where
  law s := A.law (fun i => ((s i).1.swap,(s i).2))
  normalized _ := A.normalized _
  predict w x := A.predict w x.swap
  listSize w x := A.listSize w x.swap
  measurable x y := A.measurable x.swap y

def swappedTemplate {k m} (T : Template k m) : Template k m := ⟨T.yRank,T.xRank,T.label⟩

theorem swapped_private {k m Ω} [MeasurableSpace Ω] {A : Rule k m Ω} {scale δ}
    (h : Private A scale δ) : Private (swappedRule A) scale δ := by
  intro s t ⟨i,eq⟩
  exact h _ _ ⟨i,fun j hj => by simp [eq j hj]⟩

theorem swapped_homogeneous {k m Ω L} [MeasurableSpace Ω] {A : Rule k m Ω} {T : Template k m}
    {X Y : Fin L ↪o ℕ} {v τ} (h : HomogeneousOn A T X Y v τ) :
    HomogeneousOn (swappedRule A) (swappedTemplate T) Y X (fun r => v r.swap) τ :=
  fun a b i y => h b a i.swap y

end PrivateList
