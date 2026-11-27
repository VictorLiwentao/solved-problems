module

public import SolvedProblems.RadoBoolean
public import Mathlib.Order.Filter.Germ.Basic

@[expose] public section

namespace RadoSelection
open Filter

universe u v

attribute [-instance] BooleanAlgebra.toBiheytingAlgebra BooleanAlgebra.toGeneralizedBooleanAlgebra

/-- The Boolean prime ideal theorem in its two-valued homomorphism formulation. -/
def BooleanPrime : Prop :=
  ∀ (B : Type u) [BooleanAlgebra B] [Nontrivial B], BooleanPoint B

/-- A predicate is large in the cone filter when all samples containing one
finite list of requirements satisfy it. The list is only a witness in Prop. -/
def cones (T : Type u) : Filter (Sample T) where
  sets p := ∃ l : List T, ∀ s : Sample T, (∀ x ∈ l, x ∈ s) → p s
  univ_sets := ⟨[],fun _ _ => trivial⟩
  sets_of_superset := fun ⟨l,h⟩ h' => ⟨l,fun s hs => h' (h s hs)⟩
  inter_sets := fun ⟨l,hl⟩ ⟨w,hw⟩ => ⟨l ++ w, fun s hs =>
    ⟨hl s (fun x hx => hs x (List.mem_append_left _ hx)),
      hw s (fun x hx => hs x (List.mem_append_right _ hx))⟩⟩

/-- Boolean operations on functions modulo eventual equality in the cone filter. -/
abbrev germAlgebra {X : Type u} (f : Filter X) : BooleanAlgebra (f.Germ Bool) where
  __ := (inferInstance : DistribLattice (f.Germ Bool))
  __ := (inferInstance : BoundedOrder (f.Germ Bool))
  compl := Germ.map Bool.not
  inf_compl_le_bot g := by
    induction g using Germ.inductionOn with | h g =>
      apply Germ.coe_le.mpr
      exact Filter.Eventually.of_forall (fun s => show (g s && !(g s)) ≤ false by cases g s <;> decide)
  top_le_sup_compl g := by
    induction g using Germ.inductionOn with | h g =>
      apply Germ.coe_le.mpr
      exact Filter.Eventually.of_forall (fun s => show true ≤ (g s || !(g s)) by cases g s <;> decide)
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

theorem nontrivial_quotient (T : Type u) : Nontrivial ((cones T).Germ Bool) := by
  refine ⟨⟨Germ.const (l := cones T) false, Germ.const (l := cones T) true, ?_⟩⟩
  intro e
  have eventual : (fun _ : Sample T => false) =ᶠ[cones T] (fun _ => true) := Germ.coe_eq.mp e
  obtain ⟨l, h⟩ := eventual
  exact Bool.noConfusion (h (Sample.ofList l) (fun _ hx => hx))

private def germOf {T : Type u} [∀ p : Prop, Decidable p] (p : Sample T → Prop) :
    (cones T).Germ Bool := Germ.ofFun (fun s => decide (p s))

theorem quotient_fine (T : Type u) [∀ p : Prop, Decidable p]
    (bpi : @BooleanPoint ((cones T).Germ Bool) (germAlgebra _)) :
    ∃ U : (Sample T → Prop) → Prop, Fine U := by
  let _ := germAlgebra (cones T)
  obtain ⟨f,fb,ft,fi,fc⟩ := bpi
  have botEq : germOf (fun _ : Sample T => False) = ⊥ := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => by simp)
  have negEq (p : Sample T → Prop) : germOf (fun s => ¬ p s) = (germOf p)ᶜ := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun s => show decide (¬ p s) = !(decide (p s)) by simp)
  have meetEq (p q : Sample T → Prop) :
      germOf (fun s => p s ∧ q s) = germOf p ⊓ germOf q := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun s => show decide (p s ∧ q s) = (decide (p s) && decide (q s)) by
      by_cases hp : p s <;> by_cases hq : q s <;> simp [hp, hq])
  refine ⟨fun p => f (germOf p) = true, ?_⟩
  constructor
  · rw [botEq, fb]
    exact Bool.noConfusion
  · intro p q h hfp
    have ee : (fun s => p s ∧ q s) = p := funext (fun s => propext ⟨And.left,fun hs => ⟨hs,h s hs⟩⟩)
    have hv := fi (germOf p) (germOf q)
    rw [← meetEq, ee, hfp, Bool.true_and] at hv
    exact hv.symm
  · intro p q hp hq
    rw [meetEq, fi, hp, hq]
    rfl
  · intro p
    by_cases hp : f (germOf p) = true
    · exact Or.inl hp
    · exact Or.inr (by rw [negEq, fc, Bool.eq_false_iff.mpr hp]; rfl)
  · intro x
    have coneEq : germOf (fun s : Sample T => x ∈ s) = ⊤ := by
      apply Germ.coe_eq.mpr
      refine ⟨[x], fun s h => ?_⟩
      change decide (x ∈ s) = true
      exact decide_eq_true (h x List.mem_cons_self)
    rw [coneEq, ft]

/-- BPI yields Rado selection over arbitrary sets, without a membership-hierarchy
assumption. The quotient Boolean algebra identifies predicates which agree on
some cone; its nontriviality is witnessed by that finite cone itself. -/
theorem selection_of_boolean [∀ p : Prop, Decidable p] (bpi : BooleanPrime.{u}) :
    Selection.{u,v} := selection_iff_fine.mpr (fun T =>
      quotient_fine T (@bpi _ (germAlgebra _) (nontrivial_quotient T)))

end RadoSelection
