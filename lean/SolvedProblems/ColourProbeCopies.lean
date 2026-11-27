module

public import SolvedProblems.ColourProbeHamming
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace ColourProbe

open SimpleGraph

/-- Copies are the actual vertex subsets inducing a graph isomorphic to the
probe, without an ordering of their vertices. -/
def Copies {U W : Type*} (H : SimpleGraph U) (G : SimpleGraph W) :=
  {S : Set W // Nonempty (H ≃g G.induce S)}

noncomputable def inducedCount {U W : Type*} (H : SimpleGraph U) (G : SimpleGraph W) := Nat.card (Copies H G)

noncomputable def copyRange {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W} (e : H ↪g G) : Copies H G :=
  ⟨Set.range e,⟨e.isoInduceRange⟩⟩

private noncomputable def intoSubset {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W} (S : Copies H G)
    (e : {e : H ↪g G // copyRange e = S}) : H ≃g G.induce S.val := by
  have range_eq : Set.range e.val = S.val := congrArg Subtype.val e.2
  let f (x : U) : S.val := ⟨e.val x,range_eq ▸ Set.mem_range_self x⟩
  have inj : Function.Injective f := fun _ _ h => e.val.injective (congrArg Subtype.val h)
  have sur : Function.Surjective f := by
    intro y
    have hy : y.val ∈ Set.range e.val := by rw [range_eq]; exact y.property
    obtain ⟨x,hx⟩ := hy
    exact ⟨x,Subtype.ext hx⟩
  exact ⟨Equiv.ofBijective f ⟨inj,sur⟩,e.val.map_rel_iff⟩

private noncomputable def fiberEquiv {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W} (S : Copies H G) :
    {e : H ↪g G // copyRange e = S} ≃ (H ≃g G.induce S.val) where
  toFun := intoSubset S
  invFun e := ⟨(SimpleGraph.Embedding.induce S.val).comp e.toEmbedding,by
    apply Subtype.ext
    ext y
    change (∃ x, (e x).val=y) ↔ y ∈ S.val
    constructor
    · rintro ⟨x,rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩⟩
  left_inv _ := by apply Subtype.ext; ext; rfl
  right_inv _ := by ext; rfl

private noncomputable def autEquiv {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W}
    (S : Copies H G) : (H ≃g G.induce S.val) ≃ (H ≃g H) where
  toFun f := f.trans S.property.some.symm
  invFun f := f.trans S.property.some
  left_inv f := by ext; simp
  right_inv f := by ext; simp

theorem embeddings_count {U W : Type*} [Fintype U] [Fintype W] (H : SimpleGraph U) (G : SimpleGraph W) :
    Nat.card (H ↪g G) = inducedCount H G * Nat.card (H ≃g H) := by
  classical
  let _ : Fintype (Copies H G) := by unfold Copies; infer_instance
  let _ := Fintype.ofFinite (H ↪g G)
  have _ : Finite (H ≃g H) := Finite.of_injective (fun e : H ≃g H => (e : U → U)) DFunLike.coe_injective
  let _ := Fintype.ofFinite (H ≃g H)
  let _ (s : Copies H G) := Fintype.ofFinite {e : H ↪g G // copyRange e = s}
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (@copyRange _ _ H G)),Nat.card_eq_fintype_card,Fintype.card_sigma]
  have h (s : Copies H G) : Fintype.card {e : H ↪g G // copyRange e = s} = Nat.card (H ≃g H) :=
    (Fintype.card_congr ((fiberEquiv s).trans (autEquiv s))).trans Nat.card_eq_fintype_card.symm
  simp [h,inducedCount,Nat.card_eq_fintype_card]

theorem nonempty_of_count_pos {U W : Type*} [Fintype U] [Fintype W] {H : SimpleGraph U} {G : SimpleGraph W}
    (h : 0 < inducedCount H G) : Nonempty (H ↪g G) := by
  classical
  let _ : Fintype (Copies H G) := by unfold Copies; infer_instance
  obtain ⟨S⟩ := Nat.card_pos_iff.mp h |>.1
  exact ⟨(SimpleGraph.Embedding.induce S.val).comp S.property.some.toEmbedding⟩

theorem count_pos_of_embedding {U W : Type*} [Fintype W] {H : SimpleGraph U} {G : SimpleGraph W}
    (e : H ↪g G) : 0 < inducedCount H G := by
  classical
  let _ : Fintype (Copies H G) := by unfold Copies; infer_instance
  exact Nat.card_pos_iff.mpr ⟨⟨copyRange e⟩,inferInstance⟩

end ColourProbe
