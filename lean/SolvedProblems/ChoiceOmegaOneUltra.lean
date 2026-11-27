module

public import SolvedProblems.ChoiceOmegaOneClub

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Filter Order

variable {I : Type u} (rank : I → Row)

/-- Initial segments seen as subsets of the actual residual rows. -/
def seen (U : Ultrafilter I) : Set Row := {b | rank ⁻¹' Iic b ∈ U}

noncomputable def endpoint (U : Ultrafilter I) : Row := by
  classical
  exact if h : (seen rank U).Nonempty then wellFounded_lt.min (seen rank U) h else ⊥

private theorem bounded_complement (U : Ultrafilter I) (hb : (seen rank U).Nonempty) {C : Set Row}
    (club : IsClub C) (outside : endpoint rank U ∉ C) : (rank ⁻¹' C)ᶜ ∈ U := by
  classical
  apply Ultrafilter.compl_mem_iff_notMem.mpr
  intro inside
  let γ := endpoint rank U
  have he (U : Ultrafilter I) (hb : (seen rank U).Nonempty) :
      endpoint rank U = wellFounded_lt.min (seen rank U) hb := by simp [endpoint,hb]
  have bounded : rank ⁻¹' Iic γ ∈ U := by
    change γ ∈ seen rank U
    dsimp [γ]; rw [he U hb]; exact wellFounded_lt.min_mem _ _
  let t := C ∩ Iic γ
  have both : rank ⁻¹' t ∈ U := inter_mem inside bounded
  obtain ⟨x,hx⟩ := Filter.nonempty_of_mem both
  have nonempty : t.Nonempty := ⟨rank x,hx⟩
  have bound : BddAbove t := ⟨γ,fun _ h => h.2⟩
  let _ := WellFoundedLT.conditionallyCompleteLinearOrderBot (α := Row)
  let b := sSup t
  have cb : b ∈ C := club.csSup_mem inter_subset_left nonempty bound
  have bg : b < γ := lt_of_le_of_ne (csSup_le nonempty (fun _ h => h.2))
    (fun eq => outside (show γ ∈ C from eq ▸ cb))
  have mem : b ∈ seen rank U := mem_of_superset both (fun i hi => le_csSup bound hi)
  exact (wellFounded_lt.not_lt_min _ mem) (he U hb ▸ bg)

/-- For uncountably many indices there is one nonstationary member of all
their ultrafilters, whenever each finite family initially has such a member.
The map to ω₁ accommodates an arbitrary residual set of rows. -/
theorem thin_ultrafilters (F : Row → Finset (Ultrafilter I))
    (individual : ∀ α, ∃ D : Set Row, Small D ∧ ∀ U ∈ F α, rank ⁻¹' D ∈ U) :
    ∃ J D : Set Row, IsCofinal J ∧ Small D ∧ ∀ α ∈ J, ∀ U ∈ F α, rank ⁻¹' D ∈ U := by
  classical
  choose D small member using individual
  choose K club dis using small
  let d := {x : Row | ∃ α < x, x ∈ D α}
  let k := {x : Row | ∀ α < x, x ∈ K α}
  have hd : Small d := ⟨k,IsClub.diag row_cof_ne club,Set.disjoint_left.2 (by
    rintro x ⟨α,hα,hx⟩ hk; exact Set.disjoint_left.1 (dis α) hx (hk α hα))⟩
  let bounds (α : Row) := ((F α).filter (fun U => (seen rank U).Nonempty)).image (endpoint rank)
  obtain ⟨J,C,cof,hC,miss⟩ := thin_finite bounds
  refine ⟨J,d ∪ Cᶜ,cof,small_union hd ⟨C,hC,disjoint_compl_left⟩,?_⟩
  intro α hα U hU
  by_cases hb : (seen rank U).Nonempty
  · have m := bounded_complement rank U hb hC (miss α hα _ (Finset.mem_image.2
        ⟨U,Finset.mem_filter.2 ⟨hU,hb⟩,rfl⟩))
    exact mem_of_superset m (fun _ h => Or.inr h)
  · have outside : rank ⁻¹' Iic α ∉ U := fun mem => hb ⟨α,mem⟩
    have both := inter_mem (member α U hU) (Ultrafilter.compl_mem_iff_notMem.mpr outside)
    exact mem_of_superset both (fun i h => Or.inl ⟨α,lt_of_not_ge h.2,h.1⟩)

end ChoiceOmegaOne
