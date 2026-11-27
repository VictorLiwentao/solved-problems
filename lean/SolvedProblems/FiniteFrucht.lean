module

public import SolvedProblems.FiniteFruchtCore
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Equiv.Defs

@[expose] public section

namespace FiniteFrucht

/-- The full automorphism group of a simple graph, as a subgroup of all
permutations of its vertex set. -/
def automorphisms {V : Type u} (A : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {f | Preserves A f}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {f g} hf hg := fun x y => (hf (g x) (g y)).trans (hg x y)
  inv_mem' {f} hf x y := by simpa using (hf (f.symm x) (f.symm y)).symm

variable {G : Type u} [Group G] (s : Family (Set G) → Set G)

/-- The uncolored simple graph built from the chosen selector. -/
def representingGraph : SimpleGraph (Vertex (@color G)) := graph (coreGraph s) color

/-- Extend a left translation of the group points to every vertex of the graph. -/
def leftAction (a : G) : Equiv.Perm (Vertex (@color G)) := extend color (corePerm a) (corePerm_color a)

private theorem left_mul (a b : G) (v : Vertex (@color G)) :
    leftAction (a*b) v = leftAction a (leftAction b v) := by
  have comp (q : Core G) : corePerm (a*b) q = corePerm a (corePerm b q) := by
    rcases q with ⟨i,x⟩; cases i <;> simp [corePerm,translation,mul_assoc]
  cases v <;> simp [leftAction,extend,mapVertex,comp]

private def marked (a : G) : Vertex (@color G) := .base ⟨.pt,a⟩

private def read : Vertex (@color G) → G := fun v => match root color v with
  | ⟨.pt,a⟩ => a
  | _ => 1

private theorem read_left (a : G) : read (leftAction a (marked (1:G))) = a := by
  change a*1 = a
  exact mul_one a

private theorem all_actions (em : ∀ p : Prop, p ∨ ¬p) (member : ∀ F, s F ∈ F.val)
    (f : Equiv.Perm (Vertex (@color G))) (hf : Preserves (representingGraph s) f) :
    ∀ v, f v = leftAction (read (f (marked (1:G)))) v := by
  let p := oldPerm (coreGraph s) color f hf
  have hc := old_color (coreGraph s) color f hf
  obtain ⟨a,ha⟩ := core_is_translation s em member p hc (old_adj _ _ _ hf)
  have eq (v : Vertex (@color G)) : f v = leftAction a v := by
    rw [recovered (coreGraph s) color f hf v]
    change extend color p hc v = extend color (corePerm a) _ v
    have congr {p q : Equiv.Perm (Core G)} (e : p = q) (hp : ∀ z, color (p z) = color z)
        (hq : ∀ z, color (q z) = color z) : extend color p hp v = extend color q hq v := by cases e; rfl
    exact congr (Equiv.ext ha) hc _
  have recovers : read (f (marked (1:G))) = a := by rw [eq,read_left]
  simpa only [recovers] using eq

/-- A faithful action with an explicit inverse on *all* graph automorphisms.
This formulation uses pointwise composition and the simple graph itself. -/
structure FullAction (H : Type u) [Group H] {V : Type v} (A : SimpleGraph V) where
  act : H → Equiv.Perm V
  readBack : Equiv.Perm V → H
  identity : ∀ v, act 1 v = v
  multiply : ∀ a b v, act (a*b) v = act a (act b v)
  preserves : ∀ a, Preserves A (act a)
  read_act : ∀ a, readBack (act a) = a
  recover : ∀ f : Equiv.Perm V, Preserves A f → ∀ v, f v = act (readBack f) v

/-- The automorphism representation with only propositional excluded middle and
the one supplied local selector. -/
theorem action_of_selector (em : ∀ p : Prop, p ∨ ¬p) (member : ∀ F, s F ∈ F.val) :
    Nonempty (FullAction G (representingGraph s)) := by
  refine ⟨{ act := leftAction, readBack := fun f => read (f (marked 1)), identity := ?_,
            multiply := left_mul, preserves := fun a => extend_preserves (coreGraph s) color
              (corePerm a) (corePerm_color a) (corePerm_adj s a),
            read_act := read_left, recover := all_actions s em member }⟩
  intro v
  have e := left_mul (1 : G) 1 v
  rw [one_mul] at e
  exact ((leftAction (1:G)).injective e).symm

/-- Finite choice realizes every group on an uncolored simple graph, with the
full representation certified independently of any ambient choice axiom. -/
theorem finite_choice_action (em : ∀ p : Prop, p ∨ ¬p) (finiteChoice : ∀ Y : Type u, ChoiceFin Y)
    (G : Type u) [Group G] : ∃ (V : Type u) (A : SimpleGraph V), Nonempty (FullAction G A) := by
  obtain ⟨s,member⟩ := finiteChoice (Set G)
  exact ⟨Vertex (@color G), representingGraph s, action_of_selector s em member⟩

/-- A single choice function on the nonempty finite families of subsets of G
suffices. The inverse isomorphism reads the image of the identity vertex. -/
theorem representation_of_selector (em : ∀ p : Prop, p ∨ ¬p) (member : ∀ F, s F ∈ F.val) :
    Nonempty (G ≃* automorphisms (representingGraph s)) := by
  let act (a : G) : automorphisms (representingGraph s) :=
    ⟨leftAction a, extend_preserves (coreGraph s) color (corePerm a) (corePerm_color a) (corePerm_adj s a)⟩
  refine ⟨{ toFun := act, invFun := fun f => read (f.val (marked 1)), left_inv := read_left, right_inv := ?_, map_mul' := ?_ }⟩
  · intro f
    apply Subtype.ext
    exact Equiv.ext (fun v => (all_actions s em member f.val f.property v).symm)
  · intro a b
    apply Subtype.ext
    exact Equiv.ext (left_mul a b)

/-- Pinsky's finite-choice implication for all groups, undirected simple graphs,
and their full automorphism groups. The one required selector is instantiated
at the powerset of this group. -/
theorem finite_choice_frucht (finiteChoice : ∀ Y : Type u, ChoiceFin Y) (G : Type u) [Group G] :
    ∃ (V : Type u) (A : SimpleGraph V), Nonempty (G ≃* automorphisms A) := by
  obtain ⟨s,member⟩ := finiteChoice (Set G)
  exact ⟨Vertex (@color G), representingGraph s, representation_of_selector s Classical.em member⟩

end FiniteFrucht
