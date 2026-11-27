module

public import SolvedProblems.DominationMarkers

@[expose] public section

namespace DominationVC.WitnessArray

variable {V : Type*} [PartialOrder V] {a b m : ℕ}
    {P : Fin a → Fin b → Prop} {code : Index b ↪ (Fin m → Bool)} (d : WitnessArray V P code)

/-- Combine one data block with an injective set of same-orientation witnesses.
The embedding reflects every nonedge as well as preserving every edge. -/
theorem assemble (hm : 0 < m) (block : Fin a → Slots a m) (hb : Function.Injective block)
    (pick : Fin b → Index b) (hp : Function.Injective pick)
    (orient : ∀ i j, d.positive (pick i) ↔ d.positive (pick j))
    (data : ∀ x i, trace P code (pick i) (block x) ↔ P x i) :
    Nonempty (twoCliques P ↪g incomparability V) := by
  let left := fun x => d.A (block x)
  let right := fun i => d.w (pick i)
  have hl : Function.Injective left := d.A.injective.comp hb
  have hr : Function.Injective right := d.w_injective.comp hp
  have hsep (x i) : left x ≠ right i := (d.outside hm _ _).symm
  have cross (x i) : (incomparability V).Adj (left x) (right i) ↔ P x i := by
    constructor
    · exact fun h => (data x i).1 ((d.sees _ _).1 ⟨h.2.2,h.2.1⟩)
    · intro h
      have hv := (d.sees _ _).2 ((data x i).2 h)
      exact ⟨hsep x i, hv.2, hv.1⟩
  refine ⟨{ toFun := Sum.elim left right, inj' := hl.sumElim hr hsep, map_rel_iff' := ?_ }⟩
  intro x y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      change (left x ≠ left y ∧ Visible (left x) (left y)) ↔ x ≠ y
      exact ⟨fun h => fun e => h.1 (congrArg _ e),
        fun h => ⟨hl.ne h, d.antichain _ _, d.antichain _ _⟩⟩
    | inr y => exact cross x y
  | inr x =>
    cases y with
    | inl y => exact ((incomparability V).adj_comm _ _).trans (cross y x)
    | inr y =>
      change (right x ≠ right y ∧ Visible (right x) (right y)) ↔ x ≠ y
      exact ⟨fun h => fun e => h.1 (congrArg _ e), fun h => ⟨hr.ne h,
        d.same_orientation (hp.ne h) (orient _ _), d.same_orientation (hp.ne h.symm) (orient _ _)⟩⟩

include d in
/-- Either every row supplies a positive witness, or a single row supplies all
negative witnesses. The two separate data blocks handle these two choices. -/
theorem induced_copy (hm : 0 < m) : Nonempty (twoCliques P ↪g incomparability V) := by
  classical
  by_cases hrows : ∀ i : Fin b, ∃ j : Fin b, d.positive (i,j)
  · let j (i : Fin b) := (hrows i).choose
    have hpos (i) : d.positive (i,j i) := (hrows i).choose_spec
    apply d.assemble hm Sum.inl Sum.inl_injective (fun i => (i,j i))
    · exact fun _ _ h => congrArg Prod.fst h
    · exact fun i k => ⟨fun _ => hpos k, fun _ => hpos i⟩
    · exact fun _ _ => Iff.rfl
  · push Not at hrows
    obtain ⟨i, hi⟩ := hrows
    apply d.assemble hm (fun x => Sum.inr (Sum.inl x))
      (Sum.inr_injective.comp Sum.inl_injective) (fun j => (i,j))
    · exact fun _ _ h => congrArg Prod.snd h
    · exact fun j k => ⟨fun h => False.elim (hi j h), fun h => False.elim (hi k h)⟩
    · exact fun _ _ => Iff.rfl

end DominationVC.WitnessArray
