module

public import SolvedProblems.ColourProbeRows
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace ColourProbe

open SimpleGraph

noncomputable def relabel {V C D : Type*} (G : SimpleGraph V) (f : C ↪ D) :
    coloringGraph G C ↪g coloringGraph G D where
  toFun p := ⟨f ∘ p.val,fun _ _ h => f.injective.ne (p.property h)⟩
  inj' p q h := Subtype.ext (funext fun i => f.injective (congrFun (congrArg Subtype.val h) i))
  map_rel_iff' := by
    intro p q
    constructor <;> rintro ⟨i,hi,hrest⟩
    · exact ⟨i,fun h => hi (congrArg f h),fun j hj => f.injective (hrest j hj)⟩
    · exact ⟨i,f.injective.ne hi,fun j hj => congrArg f (hrest j hj)⟩

variable {V W C : Type*} {G : SimpleGraph V} {K : SimpleGraph W} (e : probe G ↪g coloringGraph K C)

theorem edge_direction (i : V) (a : Option V) : ∃ j : W, OneAt j (e (rainbow G)).val (e (single G i a)).val :=
  e.map_adj_iff.mpr ⟨i,single_change G i a⟩

noncomputable def direction (i : V) : W := (edge_direction e i none).choose

theorem anchor_direction (i : V) : OneAt (direction e i) (e (rainbow G)).val (e (single G i none)).val :=
  (edge_direction e i none).choose_spec

theorem all_directions (i : V) (a : Option V) :
    OneAt (direction e i) (e (rainbow G)).val (e (single G i a)).val := by
  by_cases h : none = a
  · subst a
    exact anchor_direction e i
  obtain ⟨j,hj⟩ := edge_direction e i a
  have hne := (single_injective G i).ne h
  have hwords := (word_injective G).ne hne
  have hadj : (probe G).Adj (single G i none) (single G i a) :=
    (neighbor_directions (single_change G i none) (single_change G i a) hwords).mpr rfl
  have outNe : (e (single G i none)).val ≠ (e (single G i a)).val := fun h => hne (e.injective (Subtype.ext h))
  have hj' := (neighbor_directions (anchor_direction e i) hj outNe).mp (e.map_adj_iff.mpr hadj)
  rwa [hj']

theorem direction_injective : Function.Injective (direction e) := by
  intro i j h
  by_contra hne
  have hrs := single_distinct G hne none none
  have outNe : (e (single G i none)).val ≠ (e (single G j none)).val := fun h => hrs (e.injective (Subtype.ext h))
  have hadj := (neighbor_directions (anchor_direction e i) (anchor_direction e j) outNe).mpr h
  exact hne ((neighbor_directions (single_change G i none) (single_change G j none) ((word_injective G).ne hrs)).mp
    (e.map_adj_iff.mp hadj))

noncomputable def changedColor (i : V) (a : Option V) : C := (e (single G i a)).val (direction e i)

theorem changed_injective (i : V) : Function.Injective (changedColor e i) := by
  intro a b h
  apply single_injective G i
  apply e.injective
  apply Subtype.ext
  funext j
  by_cases hji : j = direction e i
  · subst j
    exact h
  · exact ((all_directions e i a).2 j hji).symm.trans ((all_directions e i b).2 j hji)

theorem shared_color [Fintype V] [Fintype C] (hc : Fintype.card C < 2 * Fintype.card (Option V)) (i j : V) :
    ∃ a b, changedColor e i a = changedColor e j b := by
  classical
  by_contra! no
  let f : Option V ⊕ Option V → C := Sum.elim (changedColor e i) (changedColor e j)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (changed_injective e i h)
    · exact False.elim (no a b h)
    · exact False.elim (no b a h.symm)
    · exact congrArg Sum.inr (changed_injective e j h)
  have h := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_sum] at h
  omega

/-- Every nonedge of the target remains a nonedge on the recovered host
coordinates, because the two rows can be made to share a fresh output color. -/
theorem reflect_edges [Fintype V] [Fintype C] (hc : Fintype.card C < 2 * Fintype.card (Option V))
    {i j : V} (hK : K.Adj (direction e i) (direction e j)) : G.Adj i j := by
  classical
  have hij : i ≠ j := fun h => hK.ne (congrArg _ h)
  by_contra hG
  obtain ⟨a,b,hab⟩ := shared_color e hc i j
  let d := double G i j hij hG a b
  have dbase : (e d).val ≠ (e (rainbow G)).val := fun h => double_ne_rainbow G i j hij hG a b (e.injective (Subtype.ext h))
  have hdq : (coloringGraph K C).Adj (e (single G i a)) (e d) := e.map_adj_iff.mpr ⟨j,double_left ..⟩
  have hdr : (coloringGraph K C).Adj (e (single G j b)) (e d) := e.map_adj_iff.mpr ⟨i,double_right ..⟩
  obtain ⟨hi,hj⟩ := opposite_corner ((direction_injective e).ne hij) (all_directions e i a)
    (all_directions e j b) hdq hdr dbase
  exact (e d).property hK (hi.trans (hab.trans hj.symm))

end ColourProbe
