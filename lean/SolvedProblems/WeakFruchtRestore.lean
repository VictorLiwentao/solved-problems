module

public import SolvedProblems.WeakFruchtExpansion
public import SolvedProblems.WeakFruchtWellFounded

@[expose] public section

namespace WeakFrucht

/-- An accessible, extensional and isomorphism-extensional source decorating
the given pointed target. -/
structure Representation {V : Type u} (D : V → V → Prop) (o : V) where
  Carrier : Type v
  E : Carrier → Carrier → Prop
  root : Carrier
  proj : Carrier → V
  accessible : AccessibleFrom E root
  ext : Extensional E
  isoExt : IsoExtensional E
  decorates : Decorates E D root o proj

abbrev Bad {V : Type u} (D : V → V → Prop) := {x // ¬ Well D x}
abbrev Good {V : Type u} (D : V → V → Prop) := {x // Well D x}

def badRel {V : Type u} {D : V → V → Prop} (x y : Bad D) := D x.val y.val

/-- The leafless expansion applies when its reusable labels are supplied. -/
theorem leafless_representation {V : Type u} {Q : Type v} (o : V) (D : V → V → Prop)
    (leafless : ∀ x, ∃ y, D x y) (C : Labels V Q) : Nonempty (Representation.{u,max u v} D o) :=
  ⟨⟨K o D C, arc, start o D C, fun x => project o x.val, expansion_accessible,
    expansion_extensional leafless, expansion_iso_extensional leafless, projection_decorates⟩⟩

variable {V : Type u} {D : V → V → Prop} {o : Bad D} (K : Representation.{u,v} (@badRel _ D) o)

abbrev Union := K.Carrier ⊕ Good D

def joined : Union K → Union K → Prop
  | .inl a, .inl b => K.E a b
  | .inl a, .inr w => D (K.proj a).val w.val
  | .inr w, .inr z => D w.val z.val
  | .inr _, .inl _ => False

def projection : Union K → V
  | .inl a => (K.proj a).val
  | .inr w => w.val

private theorem union_dec (em : ∀ p : Prop, p ∨ ¬p) :
    Decorates (joined K) D (.inl K.root) o.val (projection K) := by
  refine ⟨congrArg Subtype.val K.decorates.1,?_,?_⟩
  · rintro (a|w) (b|z) e
    · exact K.decorates.2.1 e
    · exact e
    · exact False.elim e
    · exact e
  · rintro (a|w) z e
    · rcases em (Well D z) with well | bad
      · exact ⟨.inr ⟨z,well⟩,e,rfl⟩
      · obtain ⟨b,ab,hb⟩ := K.decorates.2.2 a ⟨z,bad⟩ e
        exact ⟨.inl b,ab,congrArg Subtype.val hb⟩
    · exact ⟨.inr ⟨z,well_successor w.property e⟩,e,rfl⟩

private theorem union_accessible (em : ∀ p : Prop, p ∨ ¬p) (accessible : AccessibleFrom D o.val) :
    AccessibleFrom (joined K) (.inl K.root) := by
  rintro (a|w)
  · exact reach_map Sum.inl (fun h => h) (K.accessible a)
  · obtain ⟨b,path,eq⟩ := reach_lift (projection K) (union_dec K em) (accessible w.val)
    cases b with
    | inl a =>
      change (K.proj a).val = w.val at eq
      exact False.elim ((K.proj a).property (eq ▸ w.property))
    | inr z => exact (show z = w from Subtype.ext eq) ▸ path

private theorem union_ext (em : ∀ p : Prop, p ∨ ¬p) (extD : Extensional D) : Extensional (joined K) := by
  have privateChild (k : K.Carrier) : ∃ z, K.E k z := by
    obtain ⟨z,hz,bad⟩ := bad_successor em (K.proj k).property
    obtain ⟨a,ha,_⟩ := K.decorates.2.2 k ⟨z,bad⟩ hz
    exact ⟨a,ha⟩
  rintro (a|a) (b|b) h
  · exact congrArg Sum.inl (K.ext a b (fun z => h (.inl z)))
  · obtain ⟨z,hz⟩ := privateChild a
    exact False.elim ((h (.inl z)).mp hz)
  · obtain ⟨z,hz⟩ := privateChild b
    exact False.elim ((h (.inl z)).mpr hz)
  · apply congrArg Sum.inr
    apply Subtype.ext
    apply extD
    intro z
    constructor
    · exact fun az => (h (.inr ⟨z,well_successor a.property az⟩)).mp az
    · exact fun bz => (h (.inr ⟨z,well_successor b.property bz⟩)).mpr bz

private def IsLeft : Union K → Prop
  | .inl _ => True
  | .inr _ => False

private theorem left_iff_bad (em : ∀ p : Prop, p ∨ ¬p) (z : Union K) :
    IsLeft K z ↔ ¬ Well (joined K) z := by
  rw [well_iff_image (projection K) (union_dec K em).2.1 (union_dec K em).2.2 z]
  cases z with
  | inl k => exact ⟨fun _ => (K.proj k).property,fun _ => trivial⟩
  | inr w => exact ⟨False.elim,fun h => h w.property⟩

private theorem restrict_path {a b : K.Carrier} (h : Reach (joined K) (.inl a) (.inl b)) : Reach K.E a b := by
  have aux {z : Union K} (p : Reach (joined K) (.inl a) z) : ∀ c, z = .inl c → Reach K.E a c := by
    induction p with
    | refl => rintro c eq; cases eq; exact .refl
    | @tail z t _ e ih =>
      rintro c rfl
      cases z with
      | inl k => exact (ih k rfl).tail e
      | inr w => exact False.elim e
  exact aux h b rfl

private def liftBelow (a : K.Carrier) (v : Below K.E a) : Below (joined K) (.inl a) :=
  ⟨.inl v.val,reach_map Sum.inl (fun h => h) v.property⟩

private def leftBelow (a : K.Carrier) : Below K.E a ≃ {u : Below (joined K) (.inl a) // IsLeft K u.val} where
  toFun v := ⟨liftBelow K a v,trivial⟩
  invFun
    | ⟨⟨.inl c,hc⟩,_⟩ => ⟨c,restrict_path K hc⟩
    | ⟨⟨.inr _,_⟩,bad⟩ => False.elim bad
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨(_|_),_⟩,h⟩; rfl; exact False.elim h

private theorem back_to_leafless (em : ∀ p : Prop, p ∨ ¬p) {a b : K.Carrier}
    (f : RootIso (joined K) (joined K) (.inl a) (.inl b)) : Nonempty (RootIso K.E K.E a b) := by
  have keeps (u : Below (joined K) (.inl a)) : IsLeft K u.val ↔ IsLeft K (f.iso.toEquiv u).val :=
    (left_iff_bad K em _).trans ((not_congr (f.well_iff u)).trans (left_iff_bad K em _).symm)
  let restrict := f.iso.toEquiv.subtypeEquiv (p := fun u => IsLeft K u.val) (q := fun u => IsLeft K u.val) keeps
  let e := ((leftBelow K a).trans restrict).trans (leftBelow K b).symm
  have im (v : Below K.E a) : (f.iso.toEquiv (liftBelow K a v)).val = .inl (e v).val := by
    have q := (leftBelow K b).apply_symm_apply (restrict (leftBelow K a v))
    exact (congrArg (fun z => z.val.val) q).symm
  refine ⟨⟨⟨e,?_⟩,?_⟩⟩
  · intro u v
    have edges := f.iso.edges (liftBelow K a u) (liftBelow K a v)
    change joined K (f.iso.toEquiv _).val (f.iso.toEquiv _).val ↔ _ at edges
    rw [im,im] at edges
    exact edges
  · apply Subtype.ext
    apply Sum.inl.inj
    exact (im (rootOf K.E a)).symm.trans (congrArg Subtype.val f.point)

include K in
/-- Restoring precisely the well-founded vertices preserves extensionality,
rooted-isomorphism-extensionality, accessibility, and the decoration. -/
theorem restore (em : ∀ p : Prop, p ∨ ¬p) (acc : AccessibleFrom D o.val) (extD : Extensional D) :
    Nonempty (Representation.{u,max u v} D o.val) := by
  refine ⟨⟨Union K,joined K,.inl K.root,projection K,union_accessible K em acc,union_ext K em extD,?_,union_dec K em⟩⟩
  intro a b f
  have wt : Well (joined K) a ↔ Well (joined K) b := by
    have h := f.well_iff (rootOf (joined K) a)
    rw [f.point] at h
    exact h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨g⟩ := back_to_leafless K em f
      exact congrArg Sum.inl (K.isoExt a b g)
    | inr w => exact False.elim ((left_iff_bad K em (.inr w)).mpr (fun hw =>
        (left_iff_bad K em (.inl a)).mp trivial (wt.mpr hw)))
  | inr w =>
    have well : Well (joined K) (.inr w) :=
      (well_iff_image (projection K) (union_dec K em).2.1 (union_dec K em).2.2 _).mpr w.property
    exact well_roots_equal (union_ext K em extD) f well

/-- It suffices to cover all leafless accessible digraphs (whose vertices may
have equal successor sets) to cover every extensional accessible target. -/
theorem from_leafless (em : ∀ p : Prop, p ∨ ¬p)
    (cover : ∀ (I : Type u) (E : I → I → Prop) (i : I), AccessibleFrom E i →
      (∀ x, ∃ y, E x y) → Nonempty (Representation.{u,u} E i))
    {V : Type u} (D : V → V → Prop) (o : V) (acc : AccessibleFrom D o) (extD : Extensional D) :
    Nonempty (Representation.{u,u} D o) := by
  rcases em (Well D o) with well | bad
  · exact ⟨⟨V,D,o,id,acc,extD,fun x _ f => well_roots_equal extD f (well_reachable well (acc x)),
      rfl,fun h => h,fun _ z e => ⟨z,e,rfl⟩⟩⟩
  · let i : Bad D := ⟨o,bad⟩
    have inner_acc : AccessibleFrom (@badRel _ D) i := fun a =>
      reach_restrict (fun e hb ha => hb (well_successor ha e)) (acc a.val) bad a.property
    have no_leaf (a : Bad D) : ∃ b, badRel a b := by
      obtain ⟨b,ab,bad'⟩ := bad_successor em a.property
      exact ⟨⟨b,bad'⟩,ab⟩
    obtain ⟨k⟩ := cover (Bad D) badRel i inner_acc no_leaf
    exact restore k em acc extD

end WeakFrucht
