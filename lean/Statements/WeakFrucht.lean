module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace WeakFrucht

abbrev Reach {V : Type u} (D : V → V → Prop) := Relation.ReflTransGen D

def Extensional {V : Type u} (D : V → V → Prop) : Prop :=
  ∀ x y, (∀ z, D x z ↔ D y z) → x = y

def AccessibleFrom {V : Type u} (D : V → V → Prop) (root : V) : Prop := ∀ y, Reach D root y

/-- A decoration preserves the root, preserves edges, and maps the successor
set of each source vertex onto that of its image. -/
def Decorates {V : Type u} {W : Type v} (D : V → V → Prop) (E : W → W → Prop)
    (root : V) (point : W) (p : V → W) : Prop :=
  p root = point ∧ (∀ {x y}, D x y → E (p x) (p y)) ∧ ∀ x z, E (p x) z → ∃ y, D x y ∧ p y = z

structure Iso {V : Type u} {W : Type v} (D : V → V → Prop) (E : W → W → Prop) where
  toEquiv : V ≃ W
  edges : ∀ x y, E (toEquiv x) (toEquiv y) ↔ D x y

def Iso.symm {V W} {D : V → V → Prop} {E : W → W → Prop} (f : Iso D E) : Iso E D where
  toEquiv := f.toEquiv.symm
  edges x y := by simpa using (f.edges (f.toEquiv.symm x) (f.toEquiv.symm y)).symm

theorem reach_map {V W} {D : V → V → Prop} {E : W → W → Prop} (f : V → W)
    (h : ∀ {x y}, D x y → E (f x) (f y)) {x y} (r : Reach D x y) : Reach E (f x) (f y) := by
  induction r with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (h e)

abbrev Below {V : Type u} (D : V → V → Prop) (x : V) := {y // Reach D x y}

def rootOf {V : Type u} (D : V → V → Prop) (x : V) : Below D x := ⟨x,.refl⟩

def inner {V : Type u} {D : V → V → Prop} {x : V} (a b : Below D x) : Prop := D a.val b.val

/-- The isomorphism is between the full induced rooted descendant graphs. -/
structure RootIso {V : Type u} {W : Type v} (D : V → V → Prop) (E : W → W → Prop) (x : V) (y : W) where
  iso : Iso (@inner _ D x) (@inner _ E y)
  point : iso.toEquiv (rootOf D x) = rootOf E y

def RootIso.symm {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) : RootIso E D y x where
  iso := f.iso.symm
  point := by change f.iso.toEquiv.symm _ = _; rw [← f.point,Equiv.symm_apply_apply]

def IsoExtensional {V : Type u} (D : V → V → Prop) : Prop := ∀ x y, RootIso D D x y → x = y

abbrev Child {V : Type u} (D : V → V → Prop) (x : V) := {y // D x y}

/-- Distinct children are joined when they have a common successor. -/
def Share {V : Type u} {D : V → V → Prop} {x : V} (a b : Child D x) : Prop :=
  a ≠ b ∧ ∃ z, D a.val z ∧ D b.val z

def childBelow {V} {D : V → V → Prop} {x : V} (a : Child D x) : Below D x := ⟨a.val,.single a.property⟩

def RootIso.mapChild {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (a : Child D x) : Child E y :=
  ⟨(f.iso.toEquiv (childBelow a)).val, by
    have h := (f.iso.edges (rootOf D x) (childBelow a)).mpr a.property
    rw [f.point] at h
    exact h⟩

private theorem child_below_image {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (a : Child D x) : childBelow (f.mapChild a) = f.iso.toEquiv (childBelow a) :=
  Subtype.ext rfl

@[simp] theorem RootIso.backChild {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (a : Child D x) : f.symm.mapChild (f.mapChild a) = a := by
  apply Subtype.ext
  change (f.iso.toEquiv.symm (childBelow (f.mapChild a))).val = a.val
  rw [child_below_image,Equiv.symm_apply_apply]; rfl

@[simp] theorem RootIso.forthChild {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) (b : Child E y) : f.mapChild (f.symm.mapChild b) = b := by
  apply Subtype.ext
  change (f.iso.toEquiv (childBelow (f.symm.mapChild b))).val = b.val
  rw [child_below_image]; change (f.iso.toEquiv (f.iso.toEquiv.symm _)).val = _
  rw [Equiv.apply_symm_apply]; rfl

theorem share_maps {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) {a b : Child D x} (h : Share a b) : Share (f.mapChild a) (f.mapChild b) := by
  obtain ⟨ne,z,az,bz⟩ := h
  let z' : Below D x := ⟨z,(childBelow a).property.tail az⟩
  refine ⟨fun e => ne (by simpa only [RootIso.backChild] using congrArg f.symm.mapChild e),
    (f.iso.toEquiv z').val, (f.iso.edges (childBelow a) z').mpr az, (f.iso.edges (childBelow b) z').mpr bz⟩

/-- Sharing a successor is intrinsic even when the ambient graphs have other
parents outside the two rooted descendant graphs. -/
def RootIso.onChildren {V W} {D : V → V → Prop} {E : W → W → Prop} {x y}
    (f : RootIso D E x y) : Iso (@Share _ D x) (@Share _ E y) where
  toEquiv := ⟨f.mapChild,f.symm.mapChild,f.backChild,f.forthChild⟩
  edges a b := by
    change Share (f.mapChild a) (f.mapChild b) ↔ Share a b
    exact ⟨fun h => by simpa only [RootIso.backChild] using share_maps f.symm h, share_maps f⟩

end WeakFrucht

namespace WeakFrucht

/-- Finite constructor records for the leafless expansion. Oriented edges give
separate common children for each orientation; their unordered adjacency on a
parent's children recovers the original marker graph. -/
inductive Node (V : Type u) (Q : Type v) where
  | origin
  | fresh (x : Node V Q) (next : V)
  | marker (x : Node V Q) (next : V) (q : Q)
  | joint (x : Node V Q) (next : V) (a b : Q) (last : V)

variable {V : Type u} {Q : Type v}

def project (o : V) : Node V Q → V
  | .origin => o
  | .fresh _ c | .marker _ c _ => c
  | .joint _ _ _ _ z => z

/-- Source labels are connected, have no isolated points, and their unpointed
isomorphism types distinguish the node records. -/
structure Labels (V : Type u) (Q : Type v) where
  graph : Node V Q → SimpleGraph Q
  populated : Nonempty Q
  joined : ∀ x a b, Reach (graph x).Adj a b
  neighbors : ∀ x a, ∃ b, (graph x).Adj a b
  distinguishes : ∀ x y, Iso (graph x).Adj (graph y).Adj → x = y

def Valid (o : V) (D : V → V → Prop) (C : Labels V Q) : Node V Q → Prop
  | .origin => True
  | .fresh x c | .marker x c _ => Valid o D C x ∧ D (project o x) c
  | .joint x c a b z => Valid o D C x ∧ D (project o x) c ∧ (C.graph x).Adj a b ∧ D c z

def parent (x : Node V Q) : Node V Q → Prop
  | .origin => False
  | .fresh t _ | .marker t _ _ => x = t
  | .joint t c a b _ => x = .marker t c a ∨ x = .marker t c b

abbrev K (o : V) (D : V → V → Prop) (C : Labels V Q) := Subtype (Valid o D C)

variable {o : V} {D : V → V → Prop} {C : Labels V Q}

def arc (x y : K o D C) : Prop := parent x.val y.val

def start (o : V) (D : V → V → Prop) (C : Labels V Q) : K o D C := ⟨.origin,trivial⟩

private def basic (x : K o D C) (c : V) (hc : D (project o x.val) c) : K o D C :=
  ⟨.fresh x.val c,x.property,hc⟩

def childD (x : K o D C) (c : V) (hc : D (project o x.val) c) (q : Q) : Child arc x :=
  ⟨⟨.marker x.val c q,x.property,hc⟩,rfl⟩

private theorem d_injective (x : K o D C) (c : V) (hc : D (project o x.val) c) :
    Function.Injective (childD x c hc) := by
  intro a b h
  exact (Node.marker.inj (congrArg (fun v : Child arc x => v.val.val) h)).2.2

private theorem preserves_projection {x y : K o D C} (xy : arc x y) : D (project o x.val) (project o y.val) := by
  obtain ⟨z,hz⟩ := y
  cases z with
  | origin => exact False.elim xy
  | fresh t c | marker t c _ => exact (show x.val = t from xy) ▸ hz.2
  | joint t c a b u =>
    rcases xy with h|h <;> change D (project o x.val) u <;> rw [h] <;> exact hz.2.2.2

theorem projection_decorates : Decorates (@arc _ _ o D C) D (start o D C) o (fun x => project o x.val) :=
  ⟨rfl,fun h => preserves_projection h,fun x z hz => ⟨basic x z hz,rfl,rfl⟩⟩

theorem expansion_accessible : AccessibleFrom (@arc _ _ o D C) (start o D C) := by
  rintro ⟨x,hx⟩
  induction x with
  | origin => exact .refl
  | fresh t c ih => exact (ih hx.1).tail rfl
  | marker t c q ih => exact (ih hx.1).tail rfl
  | joint t c a b z ih =>
    let d := childD (⟨t,hx.1⟩ : K o D C) c hx.2.1 a
    exact ((ih hx.1).tail d.property).tail (Or.inl rfl)

theorem expansion_extensional (leafless : ∀ x, ∃ y, D x y) : Extensional (@arc _ _ o D C) := by
  intro x y h
  obtain ⟨c,hc⟩ := leafless (project o x.val)
  exact Subtype.ext ((h (basic x c hc)).mp rfl).symm

theorem expansion_leafless (leafless : ∀ x, ∃ y, D x y) (x : K o D C) : ∃ y, arc x y := by
  obtain ⟨c,hc⟩ := leafless (project o x.val)
  exact ⟨basic x c hc,rfl⟩

private theorem both_markers {x : K o D C} {a b : Child arc x} {t : Node V Q} {c : V} {p q : Q}
    (ha : a.val.val = .marker t c p) (hb : b.val.val = .marker t c q)
    (hc : D (project o t) c) (edge : (C.graph t).Adj p q) :
    ∃ c, ∃ h : D (project o x.val) c, ∃ p q,
      a = childD x c h p ∧ b = childD x c h q ∧ (C.graph x.val).Adj p q := by
  have par := a.property
  change parent x.val a.val.val at par
  rw [ha] at par
  have eq : x.val = t := par
  subst t
  exact ⟨c,hc,p,q,Subtype.ext (Subtype.ext ha),Subtype.ext (Subtype.ext hb),edge⟩

/-- All and only the two endpoints of one label edge can share a successor. -/
theorem shared_iff {x : K o D C} {a b : Child arc x} (leafless : ∀ u, ∃ v, D u v) :
    Share a b ↔ ∃ c, ∃ h : D (project o x.val) c, ∃ p q,
      a = childD x c h p ∧ b = childD x c h q ∧ (C.graph x.val).Adj p q := by
  constructor
  · rintro ⟨ne,⟨z,hz⟩,az,bz⟩
    cases z with
    | origin => exact False.elim az
    | fresh t c | marker t c q =>
      exact False.elim (ne (Subtype.ext (Subtype.ext ((show a.val.val = t from az).trans bz.symm))))
    | joint t c p q u =>
      rcases az with ap | aq <;> rcases bz with bp | bq
      · exact False.elim (ne (Subtype.ext (Subtype.ext (ap.trans bp.symm))))
      · exact both_markers ap bq hz.2.1 hz.2.2.1
      · exact both_markers aq bp hz.2.1 hz.2.2.1.symm
      · exact False.elim (ne (Subtype.ext (Subtype.ext (aq.trans bq.symm))))
  · rintro ⟨c,h,p,q,rfl,rfl,edge⟩
    obtain ⟨z,hz⟩ := leafless c
    refine ⟨fun eq => ?_,⟨.joint x.val c p q z,x.property,h,edge,hz⟩,Or.inl rfl,Or.inr rfl⟩
    exact edge.ne (d_injective _ _ _ eq)

private theorem child_iff (leafless : ∀ u, ∃ v, D u v) (x : K o D C) {c} (hc : D (project o x.val) c) (p q : Q) :
    Share (childD x c hc p) (childD x c hc q) ↔ (C.graph x.val).Adj p q := by
  constructor
  · intro h
    obtain ⟨_,_,a,b,ha,hb,edge⟩ := (shared_iff leafless).mp h
    have ea := (Node.marker.inj (congrArg (fun v : Child arc x => v.val.val) ha)).2.2
    have eb := (Node.marker.inj (congrArg (fun v : Child arc x => v.val.val) hb)).2.2
    exact ea ▸ eb ▸ edge
  · exact fun h => (shared_iff leafless).mpr ⟨c,hc,p,q,rfl,rfl,h⟩

private theorem same_component (leafless : ∀ u, ∃ v, D u v) (x : K o D C) {c} (hc : D (project o x.val) c)
    (q : Q) {v : Child arc x} (h : Reach Share (childD x c hc q) v) : ∃ p, v = childD x c hc p := by
  induction h with
  | refl => exact ⟨q,rfl⟩
  | tail before edge ih =>
    obtain ⟨p,rfl⟩ := ih
    obtain ⟨d,hd,a,b,ha,hb,_⟩ := (shared_iff leafless).mp edge
    have eq := (Node.marker.inj (congrArg (fun v : Child arc x => v.val.val) ha)).2.1
    subst d
    exact ⟨b,hb⟩

private def extract (fallback : Q) : Node V Q → Q
  | .marker _ _ q => q
  | _ => fallback

/-- An isomorphism of rooted descendant graphs identifies a whole connected
copy of the label, by shared successors at the root. -/
theorem expansion_iso_extensional (leafless : ∀ u, ∃ v, D u v) : IsoExtensional (@arc _ _ o D C) := by
  intro x y f
  let iso := f.onChildren
  obtain ⟨q₀⟩ := C.populated
  obtain ⟨c,hc⟩ := leafless (project o x.val)
  let fromX := childD x c hc
  obtain ⟨q₁,edge⟩ := C.neighbors x.val q₀
  have cross := (iso.edges (fromX q₀) (fromX q₁)).mpr ((child_iff leafless x hc q₀ q₁).mpr edge)
  obtain ⟨d,hd,r,_,startY,_,_⟩ := (shared_iff leafless).mp cross
  let fromY := childD y d hd
  change iso.toEquiv (fromX q₀) = fromY r at startY
  let fw (p : Q) := extract q₀ (iso.toEquiv (fromX p)).val.val
  let bw (p : Q) := extract q₀ (iso.toEquiv.symm (fromY p)).val.val
  have image_fw (p : Q) : iso.toEquiv (fromX p) = fromY (fw p) := by
    have path := reach_map fromX (fun {a b} h => (child_iff leafless x hc a b).mpr h) (C.joined x.val q₀ p)
    have path' := reach_map iso.toEquiv (fun {a b} h => (iso.edges a b).mpr h) path
    rw [startY] at path'
    obtain ⟨w,hw⟩ := same_component leafless y hd r path'
    have ew : fw p = w := congrArg (fun z : Child arc y => extract q₀ z.val.val) hw
    exact hw.trans (congrArg fromY ew.symm)
  have image_bw (p : Q) : iso.toEquiv.symm (fromY p) = fromX (bw p) := by
    have path := reach_map fromY (fun {a b} h => (child_iff leafless y hd a b).mpr h) (C.joined y.val r p)
    have path' := reach_map iso.symm.toEquiv (fun {a b} h => (iso.symm.edges a b).mpr h) path
    change Reach Share (iso.toEquiv.symm (fromY r)) (iso.toEquiv.symm (fromY p)) at path'
    have e : iso.toEquiv.symm (fromY r) = fromX q₀ := by rw [← startY,Equiv.symm_apply_apply]
    rw [e] at path'
    obtain ⟨w,hw⟩ := same_component leafless x hc q₀ path'
    have ew : bw p = w := congrArg (fun z : Child arc x => extract q₀ z.val.val) hw
    exact hw.trans (congrArg fromX ew.symm)
  apply Subtype.ext
  apply C.distinguishes
  refine ⟨⟨fw,bw,?_,?_⟩,?_⟩
  · intro p; apply d_injective x c hc
    change fromX (bw (fw p)) = fromX p
    rw [← image_bw,← image_fw,Equiv.symm_apply_apply]
  · intro p; apply d_injective y d hd
    change fromY (fw (bw p)) = fromY p
    rw [← image_fw,← image_bw,Equiv.apply_symm_apply]
  · intro a b
    change (C.graph y.val).Adj (fw a) (fw b) ↔ (C.graph x.val).Adj a b
    rw [← child_iff leafless y hd,← child_iff leafless x hc]
    change Share (fromY (fw a)) (fromY (fw b)) ↔ Share (fromX a) (fromX b)
    rw [← image_fw,← image_fw]; exact iso.edges _ _

end WeakFrucht

namespace WeakFrucht

/-- Well-foundedness down the successor relation. This is the inductive
well-foundedness used in ZF and does not assume dependent choice. -/
def Well {V : Type u} (D : V → V → Prop) (x : V) := Acc (fun a b => D b a) x

/-- A successor-surjective map that preserves edges preserves and reflects the
well-founded part. No infinite branches are selected. -/
theorem well_iff_image {V W} {D : V → V → Prop} {E : W → W → Prop} (p : V → W)
    (forward : ∀ {x y}, D x y → E (p x) (p y)) (back : ∀ x z, E (p x) z → ∃ y, D x y ∧ p y = z)
    (x : V) : Well D x ↔ Well E (p x) := by
  constructor
  · intro h
    induction h with
    | intro a _ ih =>
      constructor
      intro z hz
      obtain ⟨y,hy,rfl⟩ := back a z hz
      exact ih y hy
  · intro h
    have lift (y : W) (w : Well E y) : ∀ a, p a = y → Well D a := by
      induction w with
      | intro t _ ih =>
        rintro a rfl
        exact Acc.intro a (fun z hz => ih (p z) (forward hz) z rfl)
    exact lift _ h x rfl

private theorem well_below {V} {D : V → V → Prop} {x : V} (u : Below D x) :
    Well (@inner _ D x) u ↔ Well D u.val := well_iff_image Subtype.val (fun h => h)
      (fun a z e => ⟨⟨z,a.property.tail e⟩,e,rfl⟩) u

theorem RootIso.well_iff {V W} {D : V → V → Prop} {E : W → W → Prop} {x y} (f : RootIso D E x y)
    (u : Below D x) : Well D u.val ↔ Well E (f.iso.toEquiv u).val := by
  apply (well_below u).symm.trans
  apply Iff.trans _ (well_below (f.iso.toEquiv u))
  apply well_iff_image f.iso.toEquiv (fun {a b} h => (f.iso.edges a b).mpr h)
  intro a z h
  refine ⟨f.iso.toEquiv.symm z,(f.iso.edges _ _).mp ?_,f.iso.toEquiv.apply_symm_apply z⟩
  simpa using h

/-- An isomorphism between two rooted descendant graphs of one extensional
relation fixes a well-founded root. -/
theorem well_roots_equal {V} {D : V → V → Prop} (extD : Extensional D) {x y : V}
    (f : RootIso D D x y) (w : Well D x) : x = y := by
  let related (a b : V) := ∃ h : Reach D x a, (f.iso.toEquiv ⟨a,h⟩).val = b
  have compare (a : V) (h : Well D a) : ∀ b, related a b → a = b := by
    induction h with
    | intro a _ ih =>
      rintro b ⟨ha,rfl⟩
      let u : Below D x := ⟨a,ha⟩
      apply extD
      intro z
      constructor
      · intro az
        let v : Below D x := ⟨z,ha.tail az⟩
        have e := ih z az (f.iso.toEquiv v).val ⟨v.property,rfl⟩
        exact e ▸ (f.iso.edges u v).mpr az
      · intro bz
        let t : Below D y := ⟨z,(f.iso.toEquiv u).property.tail bz⟩
        let v := f.iso.toEquiv.symm t
        have eq : f.iso.toEquiv v = t := f.iso.toEquiv.apply_symm_apply t
        have av : D a v.val := (f.iso.edges u v).mp (by rw [eq]; exact bz)
        have same := ih v.val av z ⟨v.property,congrArg Subtype.val eq⟩
        exact same ▸ av
  exact compare x w y ⟨.refl,congrArg Subtype.val f.point⟩

theorem well_successor {V} {D : V → V → Prop} {x y : V} (h : Well D x) (edge : D x y) : Well D y :=
  h.inv edge

theorem well_reachable {V} {D : V → V → Prop} {x y : V} (hw : Well D x) (h : Reach D x y) : Well D y := by
  induction h with
  | refl => exact hw
  | tail _ e ih => exact well_successor ih e

/-- Each non-well-founded vertex has a non-well-founded successor, using only
propositional classical logic. -/
theorem bad_successor {V} {D : V → V → Prop} (em : ∀ p : Prop, p ∨ ¬p) {x} (h : ¬ Well D x) :
    ∃ y, D x y ∧ ¬ Well D y := by
  rcases em (∃ y, D x y ∧ ¬ Well D y) with out | no
  · exact out
  · apply False.elim <| h (Acc.intro x ?_)
    intro y hy
    exact (em (Well D y)).resolve_right (fun bad => no ⟨y,hy,bad⟩)

theorem reach_restrict {V} {D : V → V → Prop} {P : V → Prop}
    (back : ∀ {a b}, D a b → P b → P a) {x y} (h : Reach D x y) (hx : P x) (hy : P y) :
    Reach (fun a b : Subtype P => D a.val b.val) ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact (ih (back e hy)).tail e

/-- Edges lift from each currently reached preimage, so finite reachable paths
lift without a simultaneous choice of lifts. -/
theorem reach_lift {V W} {D : V → V → Prop} {E : W → W → Prop} {o p} (f : V → W)
    (h : Decorates D E o p f) {z : W} (r : Reach E p z) : ∃ u, Reach D o u ∧ f u = z := by
  induction r with
  | refl => exact ⟨o,.refl,h.1⟩
  | tail _ edge ih =>
    obtain ⟨v,rv,eq⟩ := ih
    obtain ⟨u,vu,fu⟩ := h.2.2 v _ (eq ▸ edge)
    exact ⟨u,rv.tail vu,fu⟩

end WeakFrucht

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

namespace WeakFrucht

/-- From a single uniform supply of distinct connected graph labels on finite
records, the expansion and restoration give the required decoration of every
extensional accessible pointed digraph. -/
theorem reusable_labels_suffice (em : ∀ p : Prop, p ∨ ¬p)
    (supply : ∀ I : Type u, ∃ Q : Type u, Nonempty (Labels I Q))
    {V : Type u} (D : V → V → Prop) (o : V) (acc : AccessibleFrom D o) (extD : Extensional D) :
    Nonempty (Representation.{u,u} D o) := by
  apply from_leafless em _ D o acc extD
  intro I E i _ leafless
  obtain ⟨Q,⟨labels⟩⟩ := supply I
  exact leafless_representation i E leafless labels

end WeakFrucht
