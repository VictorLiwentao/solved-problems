module

public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Filter.Ultrafilter.Defs

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Cardinal Ordinal Order Filter

/-- Indices are the actual ground-model first uncountable ordinal. -/
abbrev Row := (ω₁ : Ordinal.{0}).ToType

theorem row_cof : Order.cof Row = ℵ₁ := (Ordinal.cof_toType _).trans Cardinal.cof_omega_one

theorem row_cof_ne : Order.cof Row ≠ ℵ₀ := row_cof ▸ Cardinal.aleph0_lt_aleph_one.ne'

instance row_regular : IsRegularCardinalOrder Row := ⟨by rw [row_cof,Ordinal.type_toType,Cardinal.ord_aleph]⟩

instance row_nonempty : Nonempty Row := Ordinal.nonempty_toType_iff.mpr ((Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one).ne')
noncomputable instance row_bot : OrderBot Row := WellFoundedLT.toOrderBot _
instance row_noMax : NoMaxOrder Row :=
  (noTopOrder_iff_noMaxOrder _).1 (Order.one_lt_cof_iff.1 (one_lt_aleph0.trans_le (row_cof ▸ aleph0_lt_aleph_one.le)))

/-- The allowed supports are exactly those disjoint from a club. -/
def Small (D : Set Row) : Prop := ∃ C, IsClub C ∧ Disjoint D C

theorem above (a : Row) : IsClub (Ioi a) := by
  refine ⟨?_,fun x => ?_⟩
  · intro t ht ne _ y lub
    obtain ⟨z,hz⟩ := ne
    exact lt_of_lt_of_le (ht hz) (lub.1 hz)
  · obtain ⟨y,hy⟩ := exists_gt (max a x)
    exact ⟨y,(le_max_left ..).trans_lt hy,((le_max_right ..).trans_lt hy).le⟩

theorem small_subset {D E : Set Row} (h : Small E) (sub : D ⊆ E) : Small D := by
  obtain ⟨C,hC,e⟩ := h
  exact ⟨C,hC,e.mono_left sub⟩

theorem small_union {D E : Set Row} (h : Small D) (j : Small E) : Small (D ∪ E) := by
  obtain ⟨C,hC,e⟩ := h; obtain ⟨K,hK,f⟩ := j
  refine ⟨C∩K,hC.inter row_cof_ne hK,Set.disjoint_left.2 ?_⟩
  intro x hx h
  exact hx.elim (fun d => Set.disjoint_left.1 e d h.1) (fun t => Set.disjoint_left.1 f t h.2)

theorem small_countable_union {I : Type v} [Countable I] (D : I → Set Row) (h : ∀ i, Small (D i)) :
    Small (⋃ i, D i) := by
  choose C club dis using h
  refine ⟨⋂ i,C i,IsClub.iInter_of_countable row_cof_ne club,Set.disjoint_left.2 ?_⟩
  intro x hx hxC
  obtain ⟨i,hi⟩ := Set.mem_iUnion.1 hx
  exact Set.disjoint_left.1 (dis i) hi (Set.mem_iInter.1 hxC i)

theorem cofinal_uncountable {J : Set Row} (h : IsCofinal J) : ¬ J.Countable := by
  intro c
  have le := (Order.cof_le h).trans (Cardinal.le_aleph0_iff_set_countable.mpr c)
  exact Cardinal.aleph0_lt_aleph_one.not_ge (row_cof ▸ le)

/-- A cofinal sequence of finite row sets admits an uncountable subfamily with
one nonstationary support. Pressing down the maximum below the index replaces
the manuscript's delta-system extraction. -/
theorem thin_finite (F : Row → Finset Row) : ∃ (J C : Set Row), IsCofinal J ∧ IsClub C ∧
    ∀ i ∈ J, ∀ x ∈ F i, x ∉ C := by
  classical
  let low (i : Row) := ((F i).filter (· < i)).sup id
  have reg (i : Row) (hi : i ∈ Ioi (⊥ : Row)) : low i < i := by
    exact (Finset.sup_lt_iff hi).2 (fun _ hx => (Finset.mem_filter.1 hx).2)
  obtain ⟨b,stat⟩ := exists_isStationary_preimage_singleton row_cof_ne ((above ⊥).isStationary row_cof_ne) reg
  have next (a : Row) : ∃ i, a < i ∧ low i = b := by
    obtain ⟨i,hi,high⟩ := stat (above a)
    exact ⟨i,high,hi.2⟩
  choose g gt level using next
  let lim := {δ : Row | ∀ i < δ, (F (g i)).sup id < δ}
  have club : IsClub lim := IsClub.diag row_cof_ne (fun i => above ((F (g i)).sup id))
  let C := lim ∩ Ioi b
  have hC : IsClub C := club.inter row_cof_ne (above b)
  refine ⟨g '' C,C,?_,hC,?_⟩
  · intro x
    obtain ⟨a,ha,xa⟩ := hC.isCofinal x
    exact ⟨g a,⟨a,ha,rfl⟩,xa.trans (gt a).le⟩
  · rintro _ ⟨a,ha,rfl⟩ x hx hCₓ
    by_cases lt : x < g a
    · have le : x ≤ low (g a) := Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hx,lt⟩)
      exact (level a ▸ le).not_gt hCₓ.2
    · have lt' : a < x := (gt a).trans_le (le_of_not_gt lt)
      exact (Finset.le_sup (f := id) hx).not_gt (hCₓ.1 a lt')

end ChoiceOmegaOne
