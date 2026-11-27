module

public import SolvedProblems.ColourProbe

@[expose] public section

namespace ColourProbe

open SimpleGraph

def UsesAll {U V C : Type*} {H : SimpleGraph U} {G : SimpleGraph V} (e : H ↪g coloringGraph G C) : Prop :=
  ∀ c : C, ∃ u i, (e u).val i = c

def Full {U V : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (C : Type*) :=
  {e : H ↪g coloringGraph G C // UsesAll e}

private theorem adj_coe {V C : Type*} (S : Finset C) (p q : V → S) :
    (hamming V S).Adj p q ↔ (hamming V C).Adj (Subtype.val ∘ p) (Subtype.val ∘ q) := by
  constructor <;> rintro ⟨i,h,rest⟩
  · exact ⟨i,fun he => h (Subtype.ext he),fun j hj => congrArg Subtype.val (rest j hj)⟩
  · exact ⟨i,fun he => h (congrArg Subtype.val he),fun j hj => Subtype.ext (rest j hj)⟩

noncomputable def restrictColors {U V C : Type*} {H : SimpleGraph U} {G : SimpleGraph V} (S : Finset C)
    (e : H ↪g coloringGraph G C) (h : ∀u i, (e u).val i ∈ S) : H ↪g coloringGraph G S where
  toFun u := ⟨fun i => ⟨(e u).val i,h u i⟩,fun i j hj eq => (e u).property hj (congrArg Subtype.val eq)⟩
  inj' u v eq := e.injective (Subtype.ext (funext fun i => congrArg (fun p : Coloring G S => (p.val i).val) eq))
  map_rel_iff' := by
    intro u v
    exact (adj_coe ..).trans e.map_adj_iff

noncomputable def includeColors {U V C : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (S : Finset C) (e : H ↪g coloringGraph G S) : H ↪g coloringGraph G C :=
  (relabel G ⟨Subtype.val,Subtype.val_injective⟩).comp e

theorem membership_used {U V C : Type*} [Fintype U] [Fintype V] {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g coloringGraph G C) (c : C) : c ∈ used e ↔ ∃ u i, (e u).val i = c := by
  classical simp [used]

noncomputable def usedFiber {U V C : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V)
    (S : Finset C) : {e : H ↪g coloringGraph G C // used e = S} ≃ Full H G S where
  toFun e := by
    have mem (u i) : (e.val u).val i ∈ S :=
      (congrArg (fun T : Finset C => (e.val u).val i ∈ T) e.property).mp (used_mem e.val u i)
    refine ⟨restrictColors S e.val mem,?_⟩
    intro c
    have hc : c.val ∈ used e.val := by rw [e.property]; exact c.property
    obtain ⟨u,i,hi⟩ := (membership_used _ _).mp hc
    exact ⟨u,i,Subtype.ext hi⟩
  invFun e := by
    refine ⟨includeColors S e.val,?_⟩
    ext c
    rw [membership_used]
    constructor
    · rintro ⟨u,i,h⟩
      change ((e.val u).val i).val = c at h
      exact h ▸ ((e.val u).val i).property
    · intro h
      obtain ⟨u,i,hi⟩ := e.property ⟨c,h⟩
      exact ⟨u,i,congrArg Subtype.val hi⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def fullEquiv {U V C D : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (π : C ≃ D) :
    Full H G C ≃ Full H G D where
  toFun e := ⟨(relabel G π.toEmbedding).comp e.val,fun d => by
    obtain ⟨u,i,hi⟩ := e.property (π.symm d)
    exact ⟨u,i,(congrArg π hi).trans (π.apply_symm_apply d)⟩⟩
  invFun e := ⟨(relabel G π.symm.toEmbedding).comp e.val,fun c => by
    obtain ⟨u,i,hi⟩ := e.property (π c)
    exact ⟨u,i,(congrArg π.symm hi).trans (π.symm_apply_apply c)⟩⟩
  left_inv e := by
    apply Subtype.ext
    exact DFunLike.ext _ _ fun u => Subtype.ext (funext (fun i => π.symm_apply_apply ((e.val u).val i)))
  right_inv e := by
    apply Subtype.ext
    exact DFunLike.ext _ _ fun u => Subtype.ext (funext (fun i => π.apply_symm_apply ((e.val u).val i)))

end ColourProbe
