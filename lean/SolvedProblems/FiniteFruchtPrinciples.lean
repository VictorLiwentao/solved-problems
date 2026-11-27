module

public import SolvedProblems.FiniteFrucht
public import SolvedProblems.RadoOrderability

@[expose] public section

namespace FiniteFrucht

universe u

/-- Every set admits a strict linear order. -/
def Ordering : Prop := ∀ Y : Type u, ∃ r : Y → Y → Prop, RadoSelection.StrictOn (fun _ => True) r

/-- Every strict partial order extends to a strict linear order on its carrier. -/
def OrderExtension : Prop := ∀ (Y : Type u) (p : Y → Y → Prop),
  (∀ x, ¬ p x x) → (∀ x y z, p x y → p y z → p x z) →
  ∃ r : Y → Y → Prop, RadoSelection.StrictOn (fun _ => True) r ∧ ∀ x y, p x y → r x y

/-- The members of the family are individually well-orderable. The input does
not choose a well-order simultaneously for each member. -/
def WellOrderableChoice : Prop := ∀ (Y : Type u) (D : Set (Set Y)),
  (∀ S ∈ D, S.Nonempty ∧ ∃ r : S → S → Prop, RadoSelection.StrictOn (fun _ => True) r ∧ WellFounded r) →
  ∃ s : D → Y, ∀ F, s F ∈ F.val

private theorem list_least {Y : Type u} (em : ∀ p : Prop, p ∨ ¬p) {r : Y → Y → Prop}
    (o : RadoSelection.StrictOn (fun _ => True) r) (l : List Y) (inh : ∃ x, x ∈ l) :
    ∃ a ∈ l, ∀ z ∈ l, ¬ r z a := by
  induction l with
  | nil => obtain ⟨x,h⟩ := inh; exact False.elim (List.not_mem_nil h)
  | cons y l ih =>
    rcases em (∃ x, x ∈ l) with nonempty | empty
    · obtain ⟨a,ha,least⟩ := ih nonempty
      rcases em (r y a) with lt | nlt
      · refine ⟨y,List.mem_cons_self,?_⟩
        intro z hz h
        rcases List.mem_cons.mp hz with rfl | hz
        · exact o.irrefl _ trivial h
        · exact least _ hz (o.trans trivial trivial trivial h lt)
      · refine ⟨a,List.mem_cons_of_mem _ ha,?_⟩
        intro z hz h
        exact (List.mem_cons.mp hz).elim (fun e => nlt (e ▸ h)) (fun hl => least _ hl h)
    · refine ⟨y,List.mem_cons_self,?_⟩
      intro z hz h
      exact (List.mem_cons.mp hz).elim (fun e => o.irrefl _ trivial (e ▸ h)) (fun hl => empty ⟨z,hl⟩)

private def minMember {Y : Type u} (r : Set Y → Set Y → Prop) (F : Family (Set Y)) : Set Y :=
  {y | ∃ S ∈ F.val, (∀ T ∈ F.val, ¬ r T S) ∧ y ∈ S}

/-- The unique least subset is defined by separation. No choice function is
used to collect the minima across different finite families. -/
theorem selector_of_order {Y : Type u} (em : ∀ p : Prop, p ∨ ¬p) (r : Set Y → Set Y → Prop)
    (o : RadoSelection.StrictOn (fun _ => True) r) : ChoiceFin (Set Y) := by
  refine ⟨minMember r,?_⟩
  intro F
  obtain ⟨S,hS⟩ := F.property.1
  obtain ⟨l,hl⟩ := F.property.2
  obtain ⟨A,ha,least⟩ := list_least em o l ⟨S,(hl S).mp hS⟩
  have eq : minMember r F = A := by
    ext x
    constructor
    · rintro ⟨T,hT,hmin,hx⟩
      rcases em (T = A) with e | ne
      · exact e ▸ hx
      · rcases o.compare trivial trivial ne with h | h
        · exact (least T ((hl T).mp hT) h).elim
        · exact (hmin A ((hl A).mpr ha) h).elim
    · exact fun hx => ⟨A,(hl A).mpr ha,fun T hT => least T ((hl T).mp hT),hx⟩
  exact eq ▸ (hl A).mpr ha

private theorem selector_of_wellorders {Y : Type u} (test : ∀ p : Prop, Decidable p)
    (w : WellOrderableChoice.{u}) : ChoiceFin Y := by
  let D : Set (Set Y) := {S | (∃ y, y ∈ S) ∧ ∃ l : List Y, ∀ y, y ∈ S ↔ y ∈ l}
  apply w Y D
  rintro S ⟨inh,l,hl⟩
  refine ⟨inh,?_⟩
  let _ : DecidableEq Y := fun x y => test (x = y)
  let idx (y : S) := l.idxOf y.val
  have inj : Function.Injective idx := by
    intro x y eq
    let i : Fin l.length := ⟨idx x,List.idxOf_lt_length_of_mem ((hl x.val).mp x.property)⟩
    let j : Fin l.length := ⟨idx y,List.idxOf_lt_length_of_mem ((hl y.val).mp y.property)⟩
    apply Subtype.ext
    exact (List.getElem_idxOf i.isLt).symm.trans
      ((congrArg l.get (show i = j from Fin.ext eq)).trans (List.getElem_idxOf j.isLt))
  refine ⟨fun a b => idx a < idx b, ⟨fun _ _ => Nat.lt_irrefl _,fun _ _ _ => Nat.lt_trans,?_⟩,
    InvImage.wf idx Nat.lt_wfRel.wf⟩
  intro x y _ _ hn
  exact lt_or_gt_of_ne (fun e => hn (inj e))

/-- The four alternatives in Pinsky's list besides joint finite choice each
supply the required selector on the finite families of subsets of this group. -/
theorem four_principles_action (test : ∀ p : Prop, Decidable p)
    (principle : Ordering.{u} ∨ OrderExtension.{u} ∨ RadoSelection.BooleanPrime.{u} ∨ WellOrderableChoice.{u})
    (G : Type u) [Group G] : ∃ (V : Type u) (A : SimpleGraph V), Nonempty (FullAction G A) := by
  let em (p : Prop) := @Decidable.em p (test p)
  have choiceOn : ChoiceFin (Set G) := by
    rcases principle with o | e | b | w
    · obtain ⟨r,hr⟩ := o (Set G)
      exact selector_of_order em r hr
    · obtain ⟨r,hr,_⟩ := e (Set G) (fun _ _ => False) (fun _ h => h) (fun _ _ _ h _ => h)
      exact selector_of_order em r hr
    · obtain ⟨r,hr⟩ := @RadoSelection.order_of_boolean (Set G) test b
      exact selector_of_order em r hr
    · exact selector_of_wellorders test w
  obtain ⟨s,member⟩ := choiceOn
  exact ⟨_,representingGraph s,action_of_selector s em member⟩

end FiniteFrucht
