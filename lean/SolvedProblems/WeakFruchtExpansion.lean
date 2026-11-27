module

public import SolvedProblems.WeakFruchtGraph

@[expose] public section

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
