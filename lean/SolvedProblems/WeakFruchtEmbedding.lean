module

public import SolvedProblems.WeakFruchtEvaluation
public import SolvedProblems.WeakFruchtShift

@[expose] public section

namespace WeakFrucht

universe u

/-- Every group in the universe has a faithful action realizing precisely all
automorphisms of some simple undirected graph, with a supplied inverse. -/
def ActionFrucht : Prop := ∀ (G : Type u) [Group G], ∃ (V : Type u) (A : SimpleGraph V),
  Nonempty (FiniteFrucht.FullAction G A)

/-- The usual Frucht principle with a group isomorphism to the whole
automorphism group. -/
def Frucht : Prop := ∀ (G : Type u) [Group G], ∃ (V : Type u) (A : SimpleGraph V),
  Nonempty (G ≃* FiniteFrucht.automorphisms A)

theorem actions_of_frucht [dec : ∀ p : Prop, Decidable p] (frucht : Frucht.{u}) : ActionFrucht.{u} := by
  intro G group
  obtain ⟨V,A,⟨iso⟩⟩ := frucht G
  let read (f : Equiv.Perm V) : G := if hf : FiniteFrucht.Preserves A f then iso.symm ⟨f,hf⟩ else 1
  refine ⟨V,A,⟨{
    act := fun g => (iso g).val, readBack := read,
    identity := ?_, multiply := ?_, preserves := fun g => (iso g).property,
    read_act := ?_, recover := ?_}⟩⟩
  · intro v
    exact congrArg (fun f : FiniteFrucht.automorphisms A => f.val v) iso.map_one
  · intro g h v
    exact congrArg (fun f : FiniteFrucht.automorphisms A => f.val v) (iso.map_mul g h)
  · intro g
    have p : FiniteFrucht.Preserves A (iso g).val := (iso g).property
    simp only [read,dite_eq_left p,iso.symm_apply_apply]
  · intro f hf v
    simp only [read,dite_eq_left hf]
    exact (congrArg (fun h : FiniteFrucht.automorphisms A => h.val v) (iso.apply_symm_apply ⟨f,hf⟩)).symm

/-- The converse verifies that the pointwise formulation specifies exactly
the ordinary automorphism-group principle. -/
theorem frucht_of_actions (actions : ActionFrucht.{u}) : Frucht.{u} := by
  intro G group
  obtain ⟨V,A,⟨F⟩⟩ := actions G
  refine ⟨V,A,⟨{
    toFun := fun g => ⟨F.act g,F.preserves g⟩, invFun := fun f => F.readBack f.val,
    left_inv := F.read_act, right_inv := ?_, map_mul' := ?_}⟩⟩
  · intro f
    exact Subtype.ext (Equiv.ext (fun v => (F.recover f.val f.property v).symm))
  · intro g h
    exact Subtype.ext (Equiv.ext (F.multiply g h))

/-- One application of Frucht supplies a pointed rigid graph containing any
given type. The realizing group has a pair with trivial joint centralizer.
Evaluation and two pins turn this fact into rigidity of an uncolored graph. -/
theorem embedding_of_actions [dec : ∀ p : Prop, Decidable p] (actions : ActionFrucht.{u}) (X : Type u) :
    ∃ (S : Type u) (B : SimpleGraph S) (p : S) (i : X → S), PointRigid B p ∧ Function.Injective i := by
  obtain ⟨V,A,⟨F⟩⟩ := actions (Shift X)
  let point (c : Shift X) : Evaluation.Maps A := ⟨F.act c,F.preserves c⟩
  have faithful {e g : Shift X} (eq : F.act e = F.act g) : e = g :=
    (F.read_act e).symm.trans ((congrArg F.readBack eq).trans (F.read_act g))
  have commutes (h : Evaluation.Maps A) (q : Shift X) (hc : ∀ v, h.val ((point q).val v) = (point q).val (h.val v)) :
      F.readBack h.val * q = q * F.readBack h.val := by
    apply faithful
    apply Equiv.ext
    intro v
    rw [F.multiply,F.multiply,← F.recover h.val h.property,← F.recover h.val h.property]
    exact hc v
  have fixed (h : Evaluation.Maps A)
      (ht : ∀ x, h.val ((point Shift.up).val x) = (point Shift.up).val (h.val x))
      (hs : ∀ x, h.val ((point Shift.pin).val x) = (point Shift.pin).val (h.val x)) (x : V) : h.val x = x := by
    have trivializer := Shift.centralizer (F.readBack h.val) (commutes h _ ht) (commutes h _ hs)
    rw [F.recover h.val h.property,trivializer,F.identity]
  let i (x : X) : Evaluation.Carrier A := .base ⟨.map,point (Shift.encode x)⟩
  refine ⟨Evaluation.Carrier A,Evaluation.plainGraph A (point Shift.up) (point Shift.pin),Evaluation.origin A,i,
    Evaluation.pointed_rigid A _ _ fixed,?_⟩
  intro x y e
  have h : point (Shift.encode x) = point (Shift.encode y) := eq_of_heq (Sigma.mk.inj (FiniteFrucht.Vertex.base.inj e)).2
  exact Shift.encode_injective (faithful (congrArg Subtype.val h))

theorem embedding_of_frucht [∀ p : Prop, Decidable p] (frucht : Frucht.{u}) (X : Type u) :
    ∃ (S : Type u) (B : SimpleGraph S) (p : S) (i : X → S), PointRigid B p ∧ Function.Injective i :=
  embedding_of_actions (actions_of_frucht frucht) X

end WeakFrucht
