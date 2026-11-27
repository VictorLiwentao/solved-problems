module

public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Bases

@[expose] public section

namespace UniversalWadge

open Set
open scoped Classical

/-- The additive Borel classes: at positive rank α, start with open sets and close
under countable unions and complements of classes at strictly smaller ranks. -/
inductive AdditiveClass (X : Type) [TopologicalSpace X] : Ordinal.{0} → Set X → Prop
  | basic {α U} (positive : 0 < α) (h : IsOpen U) : AdditiveClass X α U
  | unions {α} (positive : 0 < α) {I : Type} [Countable I] (s : I → Set X)
      (hs : ∀ i,AdditiveClass X α (s i)) : AdditiveClass X α (⋃ i,s i)
  | lowerCompl {α β s} (low : β<α) (h : AdditiveClass X β s) : AdditiveClass X α sᶜ

def MultiplicativeClass (X : Type) [TopologicalSpace X] (α : Ordinal.{0}) (s : Set X) : Prop :=
  AdditiveClass X α sᶜ

theorem additive_positive {X} [TopologicalSpace X] {α s} (h : AdditiveClass X α s) : 0 < α := by
  induction h with | basic pos _ => exact pos | unions pos _ _ _ => exact pos | lowerCompl low _ ih => exact ih.trans low

theorem additive_baire {X} [TopologicalSpace X] {α s} (h : AdditiveClass X α s) : BaireMeasurableSet s := by
  induction h with | basic _ h => exact h.baireMeasurableSet | unions _ _ _ ih => exact .iUnion ih | lowerCompl _ _ ih => exact ih.compl

theorem additive_preimage {X Y} [TopologicalSpace X] [TopologicalSpace Y] {α s} {f : X → Y}
    (cf : Continuous f) (h : AdditiveClass Y α s) : AdditiveClass X α (f ⁻¹' s) := by
  induction h with
  | basic pos ho => exact .basic pos (ho.preimage cf)
  | unions pos u _ ih => rw [preimage_iUnion];exact .unions pos _ ih
  | lowerCompl low _ ih => exact .lowerCompl low ih

theorem relative_extension {X} [TopologicalSpace X] (G : Set X) {α s} (h : AdditiveClass G α s) :
    ∃ E : Set X, AdditiveClass X α E ∧ Subtype.val ⁻¹' E = s := by
  induction h with
  | basic pos ho =>
    obtain ⟨U,hU,eq⟩ := isOpen_induced_iff.mp ho
    exact ⟨U,.basic pos hU,eq⟩
  | unions pos u _ ih =>
    choose E hE eq using ih
    exact ⟨⋃ i,E i,.unions pos E hE,by simp only [preimage_iUnion,eq]⟩
  | lowerCompl low _ ih =>
    obtain ⟨E,hE,eq⟩ := ih
    exact ⟨Eᶜ,.lowerCompl low hE,by rw [preimage_compl,eq]⟩

end UniversalWadge
