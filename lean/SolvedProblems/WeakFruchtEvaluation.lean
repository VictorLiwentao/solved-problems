module

public import SolvedProblems.FiniteFrucht
public import SolvedProblems.WeakFruchtRecords

@[expose] public section

namespace WeakFrucht.Evaluation

/-- All automorphisms and their evaluation relation, with two designated
automorphisms. This structure's symmetries form their joint centralizer. -/
inductive Kind | vertex | map | tuple | input | output | first | second

def Kind.color : Kind → ℕ
  | .vertex => 0 | .map => 1 | .tuple => 2 | .input => 3
  | .output => 4 | .first => 5 | .second => 6

private theorem color_inj : Function.Injective Kind.color := by
  intro a b e; cases a <;> cases b <;> simp_all [Kind.color]

variable {V : Type v} (A : SimpleGraph V)

abbrev Maps := {f : Equiv.Perm V // FiniteFrucht.Preserves A f}

abbrev Part : Kind → Type v
  | .vertex => V
  | .map => Maps A
  | .tuple | .input | .output => Maps A × V
  | .first | .second => PUnit

abbrev Core := Sigma (Part A)

def color (x : Core A) := x.1.color

variable (a b : Maps A)

def incidence : (i j : Kind) → Part A i → Part A j → Prop
  | .vertex,.vertex,v,w => A.Adj v w
  | .map,.tuple,f,q => f=q.1
  | .tuple,.input,q,r | .tuple,.output,q,r => q=r
  | .vertex,.input,v,q => v=q.2
  | .vertex,.output,v,q => v=q.1.val q.2
  | .first,.map,_,f => f=a
  | .second,.map,_,f => f=b
  | _,_,_,_ => False

def coreGraph : SimpleGraph (Core A) where
  Adj x y := incidence A a b x.1 y.1 x.2 y.2 ∨ incidence A a b y.1 x.1 y.2 x.2
  symm := ⟨fun _ _ e => e.symm⟩
  loopless := ⟨by rintro ⟨i,x⟩; cases i <;> simp [incidence]⟩

private def slice (k : Kind) : Part A k ≃ {x : Core A // x.1 = k} where
  toFun x := ⟨⟨k,x⟩,rfl⟩
  invFun | ⟨⟨_,x⟩,rfl⟩ => x
  left_inv _ := rfl
  right_inv | ⟨⟨_,_⟩,rfl⟩ => rfl

theorem core_rigid (central : ∀ h : Maps A,
    (∀ x, h.val (a.val x) = a.val (h.val x)) →
    (∀ x, h.val (b.val x) = b.val (h.val x)) → ∀ x, h.val x = x)
    (f : Equiv.Perm (Core A)) (hf : FiniteFrucht.Preserves (coreGraph A a b) f)
    (hc : ∀ x, color A (f x) = color A x) (x : Core A) : f x = x := by
  have typed (q : Core A) : (f q).1 = q.1 := color_inj (hc q)
  let cut (k : Kind) := f.subtypeEquiv (p := fun q => q.1=k) (q := fun q => q.1=k) (fun x => by rw [typed])
  let act (k : Kind) := ((slice A k).trans (cut k)).trans (slice A k).symm
  have move (k : Kind) (x : Part A k) : f ⟨k,x⟩ = ⟨k,act k x⟩ := by
    exact (congrArg Subtype.val ((slice A k).apply_symm_apply (cut k (slice A k x)))).symm
  have adj (i j : Kind) (x : Part A i) (y : Part A j) :
      (coreGraph A a b).Adj ⟨i,act i x⟩ ⟨j,act j y⟩ ↔ (coreGraph A a b).Adj ⟨i,x⟩ ⟨j,y⟩ := by
    rw [← move,← move]; exact hf _ _
  have ga (u v : V) : A.Adj (act .vertex u) (act .vertex v) ↔ A.Adj u v := by
    have e := adj .vertex .vertex u v
    constructor
    · intro huv
      exact ((e.mp (Or.inl huv)).elim id (fun e => e.symm))
    · intro huv
      exact ((e.mpr (Or.inl huv)).elim id (fun e => e.symm))
  have inp (q : Maps A × V) : act .input q = act .tuple q := by
    symm
    simpa only [coreGraph,incidence,or_false] using (adj .tuple .input q q).mpr (Or.inl rfl)
  have out (q : Maps A × V) : act .output q = act .tuple q := by
    symm
    simpa only [coreGraph,incidence,or_false] using (adj .tuple .output q q).mpr (Or.inl rfl)
  have pair (h : Maps A) (v : V) : act .tuple (h,v) = (act .map h,act .vertex v) := by
    apply Prod.ext
    · symm
      simpa only [coreGraph,incidence,or_false] using (adj .map .tuple h (h,v)).mpr (Or.inl rfl)
    · symm
      simpa only [coreGraph,incidence,or_false,inp] using (adj .vertex .input v (h,v)).mpr (Or.inl rfl)
  have eval (h : Maps A) (v : V) : act .vertex (h.val v) = (act .map h).val (act .vertex v) := by
    simpa only [coreGraph,incidence,or_false,out,pair] using (adj .vertex .output (h.val v) (h,v)).mpr (Or.inl rfl)
  have one : act .map a = a := by
    simpa only [coreGraph,incidence,or_false] using (adj .first .map ⟨⟩ a).mpr (Or.inl rfl)
  have two : act .map b = b := by
    simpa only [coreGraph,incidence,or_false] using (adj .second .map ⟨⟩ b).mpr (Or.inl rfl)
  have fixed (v : V) : act .vertex v = v := central ⟨act .vertex,ga⟩
    (fun y => (eval a y).trans (congrArg (fun h : Maps A => h.val _) one))
    (fun y => (eval b y).trans (congrArg (fun h : Maps A => h.val _) two)) v
  have maps (h : Maps A) : act .map h = h := by
    apply Subtype.ext
    apply Equiv.ext
    intro v
    simpa only [fixed] using (eval h v).symm
  have pairs (q : Maps A × V) : act .tuple q = q := by
    obtain ⟨h,v⟩ := q; rw [pair,maps,fixed]
  obtain ⟨k,x⟩ := x
  rw [move]
  apply congrArg (Sigma.mk k)
  cases k with
  | vertex => exact fixed x
  | map => exact maps x
  | tuple => exact pairs x
  | input => exact (inp x).trans (pairs x)
  | output => exact (out x).trans (pairs x)
  | first | second => exact Subsingleton.elim .. 

abbrev Carrier := FiniteFrucht.Vertex (color A)

def plainGraph : SimpleGraph (Carrier A) := FiniteFrucht.graph (coreGraph A a b) (color A)

def origin : Carrier A := .base ⟨.first,⟨⟩⟩

/-- Every automorphism of the uncolored graph restricts to an automorphism
commuting with the two pins, and the attached paths are fixed by their bases. -/
theorem pointed_rigid (central : ∀ h : Maps A,
    (∀ x, h.val (a.val x) = a.val (h.val x)) →
    (∀ x, h.val (b.val x) = b.val (h.val x)) → ∀ x, h.val x = x) :
    PointRigid (plainGraph A a b) (origin A) := by
  intro f hf _ v
  let P := coreGraph A a b
  let col := color A
  let g := FiniteFrucht.oldPerm P col f hf
  let hc := FiniteFrucht.old_color P col f hf
  have hg (x : Core A) : g x = x := core_rigid A a b central g (FiniteFrucht.old_adj P col f hf) hc x
  rw [FiniteFrucht.recovered P col f hf v]
  have identity (p : Equiv.Perm (Core A)) (colorEq : ∀ x, col (p x) = col x)
      (fixed : p = Equiv.refl _) (x : FiniteFrucht.Vertex col) :
      FiniteFrucht.extend col p colorEq x = x := by
    subst p
    cases x <;> rfl
  exact identity g hc (Equiv.ext hg) v

end WeakFrucht.Evaluation
