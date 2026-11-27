module

public import SolvedProblems.WeakFruchtMark

@[expose] public section

namespace WeakFrucht

/-- Finite well-founded records over the possibly non-well-founded set of leaves.
Binary constructors and natural-number tags code all later nodes. -/
inductive Record (S : Type u) where
  | atom (s : S)
  | num (n : ℕ)
  | pair (a b : Record S)

def shape {S} : Record S → ℕ
  | .atom _ => 0 | .pair _ _ => 1 | .num n => n+2

inductive Role | hub | term | wire₁ | wire₂ | left | right | edge | point

def Role.code : Role → ℕ
  | .hub => 0 | .term => 1 | .wire₁ => 2 | .wire₂ => 3
  | .left => 4 | .right => 5 | .edge => 6 | .point => 7

theorem role_inj : Function.Injective Role.code := by intro a b h; cases a <;> cases b <;> simp_all [Role.code]

abbrev Payload (S : Type u) : Role → Type u
  | .hub => PUnit
  | _ => Record S
abbrev Skeleton (S : Type u) := Sigma (Payload S)

def paint {S : Type u} : Skeleton S → ℕ
  | ⟨.term,u⟩ => 8*shape u + 1
  | ⟨t,_⟩ => t.code

private theorem role_from_paint {S} (x : Skeleton S) : paint x % 8 = x.1.code := by
  obtain ⟨t,u⟩ := x; cases t <;> simp [paint,Role.code]

variable {S : Type u} (B : SimpleGraph S) (p : S)

def groundEdge : Record S → Record S → Prop
  | .atom a,.atom b => B.Adj a b
  | _,_ => False

def wires : (i j : Role) → Payload S i → Payload S j → Prop
  | .hub,.term,_,_ | .hub,.wire₂,_,_ => True
  | .term,.wire₁,x,y | .wire₁,.wire₂,x,y => x=y
  | .wire₂,.left,x,y | .wire₂,.right,x,y | .wire₂,.edge,x,y | .wire₂,.point,x,y => x=y
  | .term,.left,x,y => ∃ b, x = .pair y b
  | .term,.right,x,y => ∃ a, x = .pair a y
  | .term,.edge,x,y => groundEdge B x y
  | .term,.point,x,y => x = .atom p ∧ y = .atom p
  | _,_,_,_ => False

/-- The hub connects the whole record structure. Three-edge identification
paths and separately typed final vertices record the four binary predicates. -/
def skeleton : SimpleGraph (Skeleton S) where
  Adj x y := wires B p x.1 y.1 x.2 y.2 ∨ wires B p y.1 x.1 y.2 x.2
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by rintro ⟨i,x⟩; cases i <;> simp [wires]⟩

private def hub : Skeleton S := ⟨.hub,⟨⟩⟩

theorem skeleton_connected (a b : Skeleton S) : Reach (skeleton B p).Adj a b := by
  have reach (v : Skeleton S) : Reach (skeleton B p).Adj hub v := by
    obtain ⟨t,u⟩ := v
    cases t with
    | hub => exact .refl
    | term | wire₂ => exact .single (Or.inl trivial)
    | wire₁ =>
      have h : Reach (skeleton B p).Adj hub ⟨.term,u⟩ := .single (Or.inl trivial)
      exact h.tail (Or.inl rfl)
    | left | right | edge | point =>
      have h : Reach (skeleton B p).Adj hub ⟨.wire₂,u⟩ := .single (Or.inl trivial)
      exact h.tail (Or.inl rfl)
  exact (reach_reverse (reach a)).trans (reach b)

def side {S : Type u} : Skeleton S → Bool
  | ⟨.term,_⟩ | ⟨.wire₂,_⟩ => false
  | _ => true

theorem skeleton_bipartite {a b} (e : (skeleton B p).Adj a b) : side a ≠ side b := by
  obtain ⟨i,x⟩ := a; obtain ⟨j,y⟩ := b
  cases i <;> cases j <;> simp [skeleton,wires,side] at e ⊢

private def fiber {J : Type v} (T : J → Type u) (k : J) : T k ≃ {q : Sigma T // q.1 = k} where
  toFun x := ⟨⟨k,x⟩,rfl⟩
  invFun | ⟨⟨_,x⟩,rfl⟩ => x
  left_inv _ := rfl
  right_inv | ⟨⟨_,_⟩,rfl⟩ => rfl

private def atomFiber : S ≃ {u : Record S // shape u = 0} where
  toFun s := ⟨.atom s,rfl⟩
  invFun
    | ⟨.atom s,_⟩ => s
    | ⟨.num _,eq⟩ => False.elim (Nat.noConfusion eq)
    | ⟨.pair _ _,eq⟩ => False.elim (Nat.noConfusion eq)
  left_inv _ := rfl
  right_inv := by rintro ⟨(_|_|_),h⟩; rfl; exact False.elim (Nat.noConfusion h); exact False.elim (Nat.noConfusion h)

/-- Rigidity of a simple graph pointed at p. -/
def PointRigid : Prop := ∀ f : Equiv.Perm S, FiniteFrucht.Preserves B f → f p = p → ∀ x, f x = x

/-- Every automorphism of the colored record structure fixes all record nodes. -/
theorem skeleton_terms_fixed (rigid : PointRigid B p) (f : Equiv.Perm (Skeleton S))
    (hf : FiniteFrucht.Preserves (skeleton B p) f) (hc : ∀ x, paint (f x) = paint x) (u : Record S) :
    f ⟨.term,u⟩ = ⟨.term,u⟩ := by
  have typed (x : Skeleton S) : (f x).1 = x.1 := role_inj (by rw [← role_from_paint, hc, role_from_paint])
  let cut (k : Role) := f.subtypeEquiv (p := fun x => x.1 = k) (q := fun x => x.1 = k) (fun x => by rw [typed])
  let act (k : Role) := ((fiber (Payload S) k).trans (cut k)).trans (fiber (Payload S) k).symm
  have eq (k : Role) (x : Payload S k) : f ⟨k,x⟩ = ⟨k,act k x⟩ := by
    have e := (fiber (Payload S) k).apply_symm_apply (cut k (fiber (Payload S) k x))
    exact (congrArg Subtype.val e).symm
  have adj (i j : Role) (x : Payload S i) (y : Payload S j) :
      (skeleton B p).Adj ⟨i,act i x⟩ ⟨j,act j y⟩ ↔ (skeleton B p).Adj ⟨i,x⟩ ⟨j,y⟩ := by
    rw [← eq,← eq]; exact hf _ _
  let t := act .term
  have w₁ (x : Record S) : act .wire₁ x = t x := by
    symm; simpa [skeleton,wires,t] using (adj .term .wire₁ x x).mpr (Or.inl rfl)
  have w₂ (x : Record S) : act .wire₂ x = t x := by
    symm; simpa [skeleton,wires,w₁] using (adj .wire₁ .wire₂ x x).mpr (Or.inl rfl)
  have left' (x : Record S) : act .left x = t x := by
    symm; simpa [skeleton,wires,w₂] using (adj .wire₂ .left x x).mpr (Or.inl rfl)
  have right' (x : Record S) : act .right x = t x := by
    symm; simpa [skeleton,wires,w₂] using (adj .wire₂ .right x x).mpr (Or.inl rfl)
  have edge' (x : Record S) : act .edge x = t x := by
    symm; simpa [skeleton,wires,w₂] using (adj .wire₂ .edge x x).mpr (Or.inl rfl)
  have point' (x : Record S) : act .point x = t x := by
    symm; simpa [skeleton,wires,w₂] using (adj .wire₂ .point x x).mpr (Or.inl rfl)
  have shape_eq (x : Record S) : shape (t x) = shape x := by
    have e := hc ⟨.term,x⟩
    rw [eq] at e; change 8 * shape (t x) + 1 = 8 * shape x + 1 at e
    exact Nat.mul_left_cancel (by decide : 0 < 8) (Nat.succ.inj e)
  let cutAtoms := t.subtypeEquiv (p := fun x => shape x = 0) (q := fun x => shape x = 0) (fun x => by rw [shape_eq])
  let g : Equiv.Perm S := (atomFiber.trans cutAtoms).trans atomFiber.symm
  have atomEq (s : S) : t (.atom s) = .atom (g s) := by
    exact (congrArg Subtype.val (atomFiber.apply_symm_apply (cutAtoms (atomFiber s)))).symm
  have ground (a b : S) : B.Adj (g a) (g b) ↔ B.Adj a b := by
    have e := adj .term .edge (.atom a) (.atom b)
    simpa only [skeleton,wires,or_false,edge',show act .term = t from rfl,atomEq,groundEdge] using e
  have pinned : g p = p := by
    have e := (adj .term .point (.atom p) (.atom p)).mpr (Or.inl ⟨rfl,rfl⟩)
    simpa only [skeleton,wires,or_false,point',show act .term = t from rfl,atomEq,Record.atom.injEq,and_self] using e
  have all (z : Record S) : t z = z := by
    induction z with
    | atom a => rw [atomEq,rigid g ground pinned]
    | num n =>
      have h := shape_eq (.num n)
      cases ht : t (.num n) with
      | atom a => rw [ht] at h; exact False.elim (Nat.noConfusion h)
      | pair x y => rw [ht] at h; exact False.elim (Nat.noConfusion (Nat.succ.inj h))
      | num m => rw [ht] at h; exact congrArg Record.num (Nat.add_right_cancel h)
    | pair a b ha hb =>
      have l := (adj .term .left (.pair a b) a).mpr (Or.inl ⟨b,rfl⟩)
      have r := (adj .term .right (.pair a b) b).mpr (Or.inl ⟨a,rfl⟩)
      simp only [skeleton,wires,or_false,left',right',show act .term = t from rfl,ha,hb] at l r
      obtain ⟨c,ec⟩ := l
      obtain ⟨d,ed⟩ := r
      exact ec.trans (congrArg (Record.pair a) (Record.pair.inj (ec.symm.trans ed)).2)
  exact (eq .term u).trans (congrArg (@Sigma.mk Role (Payload S) Role.term) (all u))

end WeakFrucht
