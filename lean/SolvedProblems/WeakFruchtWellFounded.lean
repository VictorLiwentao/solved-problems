module

public import SolvedProblems.WeakFruchtGraph

@[expose] public section

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
