module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Relation
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

namespace FiniteFrucht

/-- Three pendant paths of distinct lengths encode the old vertex's type. -/
def span (t : ℕ) (b : Fin 3) : ℕ := if b = 0 then 1 else if b = 1 then 2 else 3+t

private theorem span_pos (t : ℕ) (b : Fin 3) : 0 < span t b := by
  unfold span; split <;> first | omega | split <;> omega

inductive Vertex {R : Type u} (color : R → ℕ) where
  | base (r : R)
  | tip (r : R) (branch : Fin 3) (j : ℕ) (hj : j < span (color r) branch)

variable {R : Type u} (A : SimpleGraph R) (color : R → ℕ)

def link : Vertex color → Vertex color → Prop
  | .base r, .base s => A.Adj r s
  | .base r, .tip s _ j _ => r = s ∧ j = 0
  | .tip r _ i _, .base s => s = r ∧ i = 0
  | .tip r b i _, .tip s c j _ => r = s ∧ b = c ∧ (i+1 = j ∨ j+1 = i)

def graph : SimpleGraph (Vertex color) where
  Adj := link A color
  symm := ⟨by
    intro u v
    cases u <;> cases v <;> simp only [link]
    · exact A.symm.symm _ _
    · exact id
    · exact id
    · rintro ⟨h,k,e⟩
      exact ⟨h.symm,k.symm,e.symm⟩⟩
  loopless := ⟨by
    intro u
    cases u <;> simp only [link]
    · exact A.loopless.irrefl _
    · omega⟩

/-- A permutation preserving and reflecting adjacency, with no finite-degree assumption. -/
def Preserves {V : Type w} (B : SimpleGraph V) (f : Equiv.Perm V) : Prop :=
  ∀ u v, B.Adj (f u) (f v) ↔ B.Adj u v

private theorem preserves_symm {V : Type w} {B : SimpleGraph V} {f : Equiv.Perm V}
    (hf : Preserves B f) : Preserves B f.symm := fun u v => by simpa using (hf (f.symm u) (f.symm v)).symm

private def Three {V : Type w} (B : SimpleGraph V) (u : V) : Prop :=
  ∃ a b c, B.Adj u a ∧ B.Adj u b ∧ B.Adj u c ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c

private theorem three_maps {V : Type w} {B : SimpleGraph V} {f : Equiv.Perm V} (hf : Preserves B f)
    {u : V} (h : Three B u) : Three B (f u) := by
  obtain ⟨a,b,c,ha,hb,hc,ab,bc,ac⟩ := h
  exact ⟨f a,f b,f c,(hf _ _).mpr ha,(hf _ _).mpr hb,(hf _ _).mpr hc,
    fun e => ab (f.injective e),fun e => bc (f.injective e),fun e => ac (f.injective e)⟩

private theorem base_three (r : R) : Three (graph A color) (.base r) := by
  let leaf (b : Fin 3) : Vertex color := .tip r b 0 (span_pos _ _)
  refine ⟨leaf 0,leaf 1,leaf 2,⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩,?_,?_,?_⟩ <;>
    intro h <;> simp [leaf,Vertex.tip.injEq] at h

private def prev (r : R) (b : Fin 3) (j : ℕ) (hj : j < span (color r) b) : Vertex color :=
  if j = 0 then .base r else .tip r b (j-1) (by omega)

private def next (r : R) (b : Fin 3) (j : ℕ) : Vertex color :=
  if h : j+1 < span (color r) b then .tip r b (j+1) h else .base r

private theorem two_neighbors (r : R) (b : Fin 3) (j : ℕ) (hj : j < span (color r) b)
    (v : Vertex color) (adj : (graph A color).Adj (.tip r b j hj) v) :
    v = prev color r b j hj ∨ v = next color r b j := by
  cases v with
  | base s =>
    obtain ⟨rfl,rfl⟩ := adj
    exact Or.inl (by simp [prev])
  | tip t c k hk =>
    obtain ⟨rfl,rfl,h⟩ := adj
    rcases h with rfl | rfl
    · exact Or.inr (by simp [next,hk])
    · exact Or.inl (by simp [prev])

private theorem not_three_tip (r : R) (b : Fin 3) (j : ℕ) (hj : j < span (color r) b) :
    ¬ Three (graph A color) (.tip r b j hj) := by
  rintro ⟨a,c,e,ha,hc,he,ac,ce,ae⟩
  rcases two_neighbors A color _ _ _ _ a ha with h|h <;>
    rcases two_neighbors A color _ _ _ _ c hc with h'|h' <;>
    rcases two_neighbors A color _ _ _ _ e he with h''|h'' <;>
    first | exact ac (h.trans h'.symm) | exact ce (h'.trans h''.symm) | exact ae (h.trans h''.symm)

private def depth : Vertex color → ℕ
  | .base _ => 0
  | .tip _ _ j _ => j+1

/-- Being at distance at most n from the vertices with at least three neighbors
is intrinsic to the uncolored graph. -/
private def Near {V : Type w} (B : SimpleGraph V) : ℕ → V → Prop
  | 0, u => Three B u
  | n+1, u => Near B n u ∨ ∃ v, B.Adj u v ∧ Near B n v

private theorem near_maps {V : Type w} {B : SimpleGraph V} {f : Equiv.Perm V} (hf : Preserves B f)
    (n : ℕ) {u : V} (h : Near B n u) : Near B n (f u) := by
  induction n generalizing u with
  | zero => exact three_maps hf h
  | succ n ih =>
    rcases h with h | ⟨v,adj,hr⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨f v,(hf _ _).mpr adj,ih hr⟩

private theorem depth_step {u v : Vertex color} (h : (graph A color).Adj u v) :
    depth color u ≤ depth color v + 1 := by
  cases u with
  | base r => exact Nat.zero_le _
  | tip r b j hj =>
    cases v with
    | base s => obtain ⟨_,rfl⟩ := h; rfl
    | tip t c k hk => obtain ⟨_,_,e⟩ := h; simp only [depth]; omega

private theorem near_iff (n : ℕ) (u : Vertex color) : Near (graph A color) n u ↔ depth color u ≤ n := by
  induction n generalizing u with
  | zero =>
    cases u with
    | base r => exact ⟨fun _ => Nat.le_refl _, fun _ => base_three A color _⟩
    | tip r b j hj => exact ⟨fun h => False.elim (not_three_tip A color _ _ _ _ h), fun h => by simp [depth] at h⟩
  | succ n ih =>
    constructor
    · rintro (h|⟨v,adj,h⟩)
      · exact Nat.le_succ_of_le ((ih u).mp h)
      · have := depth_step A color adj
        have := (ih v).mp h
        omega
    · intro h
      cases u with
      | base r => exact Or.inl ((ih _).mpr (Nat.zero_le _))
      | tip r b j hj =>
        cases j with
        | zero => exact Or.inr ⟨.base r,⟨rfl,rfl⟩,(ih _).mpr (Nat.zero_le _)⟩
        | succ k =>
          refine Or.inr ⟨.tip r b k (by omega),⟨rfl,rfl,Or.inr rfl⟩,(ih _).mpr ?_⟩
          simp only [depth] at h ⊢
          omega

private theorem depth_fixed (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f)
    (u : Vertex color) : depth color (f u) = depth color u := by
  have le {p : Equiv.Perm (Vertex color)} (hp : Preserves (graph A color) p) (v : Vertex color) :
      depth color (p v) ≤ depth color v := (near_iff A color _ _).mp
    (near_maps hp _ ((near_iff A color _ _).mpr (Nat.le_refl _)))
  exact Nat.le_antisymm (le hf u) (by simpa using le (preserves_symm hf) (f u))

def root : Vertex color → R
  | .base r | .tip r _ _ _ => r

private theorem maps_base (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f) (r : R) :
    f (.base r) = .base (root color (f (.base r))) := by
  have h := depth_fixed A color f hf (.base r)
  cases he : f (.base r) with
  | base s => rfl
  | tip s k j hj => rw [he] at h; simp [depth] at h

/-- The permutation of the old vertices recovered from any automorphism. -/
def oldPerm (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f) : Equiv.Perm R where
  toFun r := root color (f (.base r))
  invFun r := root color (f.symm (.base r))
  left_inv r := by dsimp only; rw [← maps_base A color f hf, f.symm_apply_apply]; rfl
  right_inv r := by dsimp only; rw [← maps_base A color f.symm (preserves_symm hf), f.apply_symm_apply]; rfl

theorem old_base (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f) (r : R) :
    f (.base r) = .base (oldPerm A color f hf r) := maps_base A color f hf r

theorem old_adj (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f) :
    Preserves A (oldPerm A color f hf) := by
  intro r s
  have h := hf (.base r) (.base s)
  rw [old_base A color f hf,old_base A color f hf] at h
  exact h

private theorem start_image (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f)
    (r : R) (b : Fin 3) : ∃ c : Fin 3, f (.tip r b 0 (span_pos _ _)) =
      .tip (oldPerm A color f hf r) c 0 (span_pos _ _) := by
  let v : Vertex color := .tip r b 0 (span_pos _ _)
  have h : (graph A color).Adj (f (.base r)) (f v) := (hf _ _).mpr ⟨rfl,rfl⟩
  rw [old_base A color f hf] at h
  have dep := depth_fixed A color f hf v
  cases he : f v with
  | base s => rw [he] at dep; simp [v,depth] at dep
  | tip s c j hj =>
    rw [he] at h
    obtain ⟨e,rfl⟩ := h
    subst s
    exact ⟨c,rfl⟩

private theorem follows (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f)
    {r s : R} {b c : Fin 3} (start : f (.tip r b 0 (span_pos _ _)) = .tip s c 0 (span_pos _ _))
    (j : ℕ) (hj : j < span (color r) b) : ∃ hj' : j < span (color s) c,
      f (.tip r b j hj) = .tip s c j hj' := by
  induction j with
  | zero => exact ⟨_,start⟩
  | succ j ih =>
    obtain ⟨hk,eq⟩ := ih (Nat.lt_of_succ_lt hj)
    let v : Vertex color := .tip r b (j+1) hj
    have a : (graph A color).Adj (f (.tip r b j (Nat.lt_of_succ_lt hj))) (f v) := (hf _ _).mpr ⟨rfl,rfl,Or.inl rfl⟩
    rw [eq] at a
    have dep := depth_fixed A color f hf v
    cases he : f v with
    | base t => rw [he] at dep; exact False.elim (Nat.noConfusion dep)
    | tip t d l hl =>
      rw [he] at a dep
      obtain ⟨rfl,rfl,_⟩ := a
      change l+1 = (j+1)+1 at dep
      have e : l = j+1 := Nat.succ.inj dep
      subst l
      exact ⟨hl,rfl⟩

private theorem same_span (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f)
    {r s : R} {b c : Fin 3} (start : f (.tip r b 0 (span_pos _ _)) = .tip s c 0 (span_pos _ _)) :
    span (color r) b = span (color s) c := by
  have le {q : Equiv.Perm (Vertex color)} (hq : Preserves (graph A color) q) {a d : R} {i k : Fin 3}
      (h : q (.tip a i 0 (span_pos _ _)) = .tip d k 0 (span_pos _ _)) : span (color a) i ≤ span (color d) k := by
    have pos := span_pos (color a) i
    obtain ⟨bound,_⟩ := follows A color q hq h (span (color a) i - 1) (by omega)
    omega
  have rev := congrArg f.symm start.symm
  exact Nat.le_antisymm (le hf start) (le (preserves_symm hf) (by simpa using rev))

private theorem branch_cases (b : Fin 3) : b = 0 ∨ b = 1 ∨ b = 2 := by
  rcases b with ⟨i,hi⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem old_color (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f) (r : R) :
    color (oldPerm A color f hf r) = color r := by
  obtain ⟨c,h⟩ := start_image A color f hf r 2
  have len := same_span A color f hf h
  rcases branch_cases c with rfl | rfl | rfl <;> simp [span] at len <;> omega

/-- Extend a color-preserving permutation to the attached paths by preserving its
branch and distance from the root. -/
def mapVertex (p : R → R) (hc : ∀ r, color (p r) = color r) : Vertex color → Vertex color
  | .base r => .base (p r)
  | .tip r b j hj => .tip (p r) b j (by rw [hc]; exact hj)

def extend (p : Equiv.Perm R) (hc : ∀ r, color (p r) = color r) : Equiv.Perm (Vertex color) where
  toFun := mapVertex color p hc
  invFun := mapVertex color p.symm (fun r => by simpa using (hc (p.symm r)).symm)
  left_inv v := by cases v <;> simp [mapVertex]
  right_inv v := by cases v <;> simp [mapVertex]

theorem extend_preserves (p : Equiv.Perm R) (hc : ∀ r, color (p r) = color r) (hp : Preserves A p) :
    Preserves (graph A color) (extend color p hc) := by
  intro u v
  cases u <;> cases v <;> simp [extend,mapVertex,graph,link]
  apply hp

/-- Every automorphism is the unique extension of its restriction to the old vertices. -/
theorem recovered (f : Equiv.Perm (Vertex color)) (hf : Preserves (graph A color) f) (v : Vertex color) :
    f v = extend color (oldPerm A color f hf) (old_color A color f hf) v := by
  cases v with
  | base r => exact old_base A color f hf r
  | tip r b j hj =>
    obtain ⟨c,h⟩ := start_image A color f hf r b
    have len := same_span A color f hf h
    rw [old_color A color f hf] at len
    have eq : c = b := by
      rcases branch_cases c with rfl | rfl | rfl <;> rcases branch_cases b with rfl | rfl | rfl <;>
        simp [span] at len <;> first | rfl | omega
    subst c
    obtain ⟨_,e⟩ := follows A color f hf h j hj
    exact e

end FiniteFrucht

namespace FiniteFrucht

/-- The full automorphism group of a simple graph, as a subgroup of all
permutations of its vertex set. -/
def automorphisms {V : Type u} (A : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {f | Preserves A f}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {f g} hf hg := fun x y => (hf (g x) (g y)).trans (hg x y)
  inv_mem' {f} hf x y := by simpa using (hf (f.symm x) (f.symm y)).symm

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

end FiniteFrucht

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

namespace WeakFrucht

variable {R : Type u} (A : SimpleGraph R)

/-- Connect two new points to one old point and to each other. When the original
graph is triangle-free the old marked point can be recovered intrinsically. -/
def addTriangle (m : R) : SimpleGraph (R ⊕ Bool) where
  Adj
    | .inl a,.inl b => A.Adj a b
    | .inl a,.inr _ => a = m
    | .inr _,.inl a => a = m
    | .inr a,.inr b => a ≠ b
  symm := ⟨by rintro (a|a) (b|b) h; exact h.symm; exact h; exact h; exact h.symm⟩
  loopless := ⟨by rintro (a|a); exact A.loopless.irrefl _; exact fun h => h rfl⟩

def Triangle {Y : Type u} (B : SimpleGraph Y) (v : Y) : Prop :=
  ∃ a b, B.Adj v a ∧ B.Adj a b ∧ B.Adj b v
private def Low {Y : Type u} (B : SimpleGraph Y) (v : Y) : Prop :=
  ∃ a b, ∀ c, B.Adj v c → c = a ∨ c = b

private theorem triangle_maps {Y Z} {B : SimpleGraph Y} {C : SimpleGraph Z} (f : Iso B.Adj C.Adj)
    {v} (h : Triangle B v) : Triangle C (f.toEquiv v) := by
  obtain ⟨a,b,va,ab,bv⟩ := h
  exact ⟨_,_,(f.edges _ _).mpr va,(f.edges _ _).mpr ab,(f.edges _ _).mpr bv⟩

private theorem low_maps {Y Z} {B : SimpleGraph Y} {C : SimpleGraph Z} (f : Iso B.Adj C.Adj)
    {v} (h : Low B v) : Low C (f.toEquiv v) := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨f.toEquiv a,f.toEquiv b,?_⟩
  intro c hc
  obtain ⟨t,rfl⟩ := f.toEquiv.surjective c
  exact (h t ((f.edges _ _).mp hc)).imp (congrArg _) (congrArg _)

private theorem old_triangle {m r : R} (free : ∀ x, ¬ Triangle A x) :
    Triangle (addTriangle A m) (.inl r) → r = m := by
  rintro ⟨(a|a),(b|b),ra,ab,br⟩
  · exact (free r ⟨a,b,ra,ab,br⟩).elim
  · exact br
  · exact ra
  · exact ra

private theorem extra_characterization {m : R} (free : ∀ x, ¬ Triangle A x) (neigh : ∃ r, A.Adj m r)
    (v : R ⊕ Bool) : Triangle (addTriangle A m) v ∧ Low (addTriangle A m) v ↔ v.isRight = true := by
  cases v with
  | inl r =>
    constructor
    · rintro ⟨h,a,b,low⟩
      obtain rfl := old_triangle A free h
      obtain ⟨s,ms⟩ := neigh
      have p := low (.inl s) ms
      have t := low (.inr true) rfl
      have f := low (.inr false) rfl
      rcases p with rfl|rfl <;> rcases t with t|t <;> rcases f with f|f <;> simp_all <;> exact Bool.noConfusion (Sum.inr.inj (t.trans f.symm))
    · intro h; cases h
  | inr v =>
    constructor
    · intro _; rfl
    · intro _
      have opposite : v ≠ !v := by cases v <;> decide
      refine ⟨⟨.inl m,.inr (!v),rfl,rfl,opposite.symm⟩,.inl m,.inr (!v),?_⟩
      rintro (r|b) h
      · exact Or.inl (congrArg Sum.inl h)
      · right; apply congrArg Sum.inr
        change v ≠ b at h
        cases v <;> cases b <;> simp_all

private def unmark (m : R) : R ⊕ Bool → R
  | .inl x => x
  | .inr _ => m

/-- An unpointed isomorphism between two marked graphs induces an automorphism
of the original triangle-free graph carrying the first mark to the second. -/
theorem recover_mark {m n : R} (free : ∀ x, ¬ Triangle A x) (hm : ∃ r, A.Adj m r) (hn : ∃ r, A.Adj n r)
    (iso : Iso (addTriangle A m).Adj (addTriangle A n).Adj) :
    ∃ f : Equiv.Perm R, FiniteFrucht.Preserves A f ∧ f m = n := by
  have old {m n : R} (hm : ∃ r, A.Adj m r) (hn : ∃ r, A.Adj n r)
      (g : Iso (addTriangle A m).Adj (addTriangle A n).Adj) (r : R) :
      g.toEquiv (.inl r) = .inl (unmark n (g.toEquiv (.inl r))) := by
    cases he : g.toEquiv (.inl r) with
    | inl s => rfl
    | inr b =>
      have p := (extra_characterization A free hn (.inr b)).mpr rfl
      have t := triangle_maps g.symm p.1
      have l := low_maps g.symm p.2
      have e : g.symm.toEquiv (.inr b) = .inl r := by rw [← he]; exact g.toEquiv.symm_apply_apply _
      rw [e] at t l
      exact False.elim (Bool.noConfusion ((extra_characterization A free hm (.inl r)).mp ⟨t,l⟩))
  let f : Equiv.Perm R := {
    toFun := fun a => unmark n (iso.toEquiv (.inl a))
    invFun := fun b => unmark m (iso.toEquiv.symm (.inl b))
    left_inv := fun r => by dsimp only; rw [← old hm hn iso r,Equiv.symm_apply_apply]; rfl
    right_inv := fun r => by
      change unmark n (iso.toEquiv (.inl (unmark m (iso.symm.toEquiv (.inl r))))) = r
      rw [← old hn hm iso.symm]; change unmark n (iso.toEquiv (iso.toEquiv.symm _)) = _
      rw [Equiv.apply_symm_apply]; rfl }
  have im (r : R) : iso.toEquiv (.inl r) = .inl (f r) := old hm hn iso r
  refine ⟨f,?_,?_⟩
  · intro x y
    have h := iso.edges (.inl x) (.inl y)
    rw [im,im] at h
    exact h
  · have h : Triangle (addTriangle A m) (.inl m) := ⟨.inr false,.inr true,rfl,Bool.false_ne_true,rfl⟩
    have t := triangle_maps iso h
    rw [im] at t
    exact old_triangle A free t

theorem reach_reverse {Y} {B : SimpleGraph Y} {a b} (h : Reach B.Adj a b) : Reach B.Adj b a := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.head e.symm

/-- Marking a vertex preserves connectedness. -/
theorem mark_connected (conn : ∀ x y, Reach A.Adj x y) (m : R) (a b : R ⊕ Bool) :
    Reach (addTriangle A m).Adj a b := by
  have fromRoot (v : R ⊕ Bool) : Reach (addTriangle A m).Adj (.inl m) v := by
    cases v with
    | inl x => exact reach_map Sum.inl (fun h => h) (conn m x)
    | inr b => exact .single rfl
  exact (reach_reverse (fromRoot a)).trans (fromRoot b)

/-- Substituting the three identifying paths preserves connectedness. -/
theorem paths_connected (col : R → ℕ) (conn : ∀ x y, Reach A.Adj x y)
    (x y : FiniteFrucht.Vertex col) : Reach (FiniteFrucht.graph A col).Adj x y := by
  have fromRoot (v : FiniteFrucht.Vertex col) : Reach (FiniteFrucht.graph A col).Adj (.base (FiniteFrucht.root col v)) v := by
    cases v with
    | base r => exact .refl
    | tip r b j hj =>
      change Reach (FiniteFrucht.graph A col).Adj (.base r) (.tip r b j hj)
      induction j with
      | zero => exact .single ⟨rfl,rfl⟩
      | succ j ih => exact (ih (Nat.lt_of_succ_lt hj)).tail ⟨rfl,rfl,Or.inl rfl⟩
  exact (reach_reverse (fromRoot x)).trans ((reach_map FiniteFrucht.Vertex.base (fun h => h) (conn _ _)).trans (fromRoot y))

/-- Extending a bipartition along each pendant path keeps the graph triangle-free. -/
theorem paths_no_triangle (col : R → ℕ) (side : R → Bool) (different : ∀ {x y}, A.Adj x y → side x ≠ side y)
    (v : FiniteFrucht.Vertex col) : ¬ Triangle (FiniteFrucht.graph A col) v := by
  let paint : FiniteFrucht.Vertex col → Bool
    | .base r => side r
    | .tip r _ j _ => if j%2 = 0 then !(side r) else side r
  have mismatch {a b} (e : (FiniteFrucht.graph A col).Adj a b) : paint a ≠ paint b := by
    cases a with
    | base r =>
      cases b with
      | base s => exact different e
      | tip s c j hj => obtain ⟨rfl,rfl⟩ := e; simp [paint]
    | tip r k j hj =>
      cases b with
      | base s => obtain ⟨rfl,rfl⟩ := e; simp [paint]
      | tip s c l hl =>
        obtain ⟨rfl,rfl,adj⟩ := e
        rcases adj with rfl | rfl <;> simp only [paint] <;> split <;> split <;> first | omega | simp
  rintro ⟨a,b,va,ab,bv⟩
  have p := mismatch va
  have q := mismatch ab
  have t := mismatch bv
  cases h₁ : paint v <;> cases h₂ : paint a <;> cases h₃ : paint b <;> simp_all

end WeakFrucht

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

namespace WeakFrucht

variable {S : Type u}

/-- A single type for all marked graphs, including their two triangle vertices. -/
abbrev Marked (S : Type u) := FiniteFrucht.Vertex (@paint S) ⊕ Bool

def holder (x : Record S) : FiniteFrucht.Vertex (@paint S) := .base ⟨.term,x⟩

def recordGraph (B : SimpleGraph S) (p : S) (u : Record S) : SimpleGraph (Marked S) :=
  addTriangle (FiniteFrucht.graph (skeleton B p) paint) (holder u)

theorem record_distinguishes (B : SimpleGraph S) (p : S) (rigid : PointRigid B p) {x y : Record S}
    (iso : Iso (recordGraph B p x).Adj (recordGraph B p y).Adj) : x = y := by
  let A := skeleton B p
  let U := FiniteFrucht.graph A paint
  have free := paths_no_triangle A paint side (fun h => skeleton_bipartite B p h)
  have hasNbr (t : Record S) : ∃ r, U.Adj (holder t) r :=
    ⟨.base ⟨.hub,⟨⟩⟩, Or.inr trivial⟩
  obtain ⟨f,hf,move⟩ := recover_mark U free (hasNbr x) (hasNbr y) iso
  let g := FiniteFrucht.oldPerm A paint f hf
  have fixed := skeleton_terms_fixed B p rigid g (FiniteFrucht.old_adj A paint f hf) (FiniteFrucht.old_color A paint f hf) x
  have e : f (holder x) = holder x := (FiniteFrucht.old_base A paint f hf ⟨.term,x⟩).trans (congrArg _ fixed)
  exact eq_of_heq (Sigma.mk.inj (FiniteFrucht.Vertex.base.inj (e.symm.trans move))).2

private def payloadCode (k : Role) : Payload S k → Record S :=
  match k with
  | .hub => fun _ => .num 0
  | .term | .wire₁ | .wire₂ | .left | .right | .edge | .point => id

private def cellCode (c : Skeleton S) : Record S := .pair (.num c.1.code) (payloadCode c.1 c.2)

private theorem cellCode_inj : Function.Injective (@cellCode S) := by
  rintro ⟨k,x⟩ ⟨t,y⟩ eq
  have h := Record.pair.inj eq
  obtain rfl : k=t := role_inj (Record.num.inj h.1)
  apply congrArg (Sigma.mk k)
  cases k <;> first | exact Subsingleton.elim x y | exact h.2

private def vertexCode : FiniteFrucht.Vertex (@paint S) → Record S
  | .base r => .pair (.num 0) (cellCode r)
  | .tip r b j _ => .pair (.num 1) (.pair (cellCode r) (.pair (.num b.val) (.num j)))

private theorem vertexCode_inj : Function.Injective (@vertexCode S) := by
  intro a z eq
  cases a <;> cases z
  rename_i r s
  · exact congrArg FiniteFrucht.Vertex.base (cellCode_inj (Record.pair.inj eq).2)
  · exact False.elim (Nat.noConfusion (Record.num.inj (Record.pair.inj eq).1))
  · exact False.elim (Nat.noConfusion (Record.num.inj (Record.pair.inj eq).1))
  · rename_i r b j hj s c k hk
    have h := Record.pair.inj (Record.pair.inj eq).2
    have e := Record.pair.inj h.2
    obtain rfl := cellCode_inj h.1
    obtain rfl : b=c := Fin.ext (Record.num.inj e.1)
    obtain rfl := Record.num.inj e.2
    rfl

private def labelCode : Marked S → Record S
  | .inl r => .pair (.num 0) (vertexCode r)
  | .inr false => .num 0
  | .inr true => .num 1

private theorem labelCode_inj : Function.Injective (@labelCode S) := by
  rintro (r|b) (s|c) eq
  · exact congrArg Sum.inl (vertexCode_inj (Record.pair.inj eq).2)
  · cases c <;> cases eq
  · cases b <;> cases eq
  · cases b <;> cases c <;> first | rfl | cases eq

private def code {V : Type v} (i : V → S) : Node V (Marked S) → Record S
  | .origin => .num 0
  | .fresh x c => .pair (.num 0) (.pair (code i x) (.atom (i c)))
  | .marker x c q => .pair (.num 1) (.pair (code i x) (.pair (.atom (i c)) (labelCode q)))
  | .joint x c a b z => .pair (.num 2) (.pair (code i x) (.pair (.atom (i c))
      (.pair (labelCode a) (.pair (labelCode b) (.atom (i z))))))

private theorem code_inj {V : Type v} {i : V → S} (inj : Function.Injective i) : Function.Injective (code i) := by
  intro x
  induction x with
  | origin => intro y h; cases y <;> simp_all [code]
  | fresh x c ih =>
    intro y h; cases y <;> simp [code] at h ⊢
    exact ⟨ih h.1,inj h.2⟩
  | marker x c q ih =>
    intro y h; cases y <;> simp [code] at h ⊢
    exact ⟨ih h.1,inj h.2.1,labelCode_inj h.2.2⟩
  | joint x c a b z ih =>
    intro y h; cases y <;> simp [code] at h ⊢
    exact ⟨ih h.1,inj h.2.1,labelCode_inj h.2.2.1,labelCode_inj h.2.2.2.1,inj h.2.2.2.2⟩

/-- A single pointed rigid graph containing the target supplies unpointed
connected graph labels for every finite record of the entire expansion. All
labels have a common carrier; no further choices at later stages are needed. -/
theorem labels_of_embedding {V : Type v} (i : V → S) (inj : Function.Injective i)
    (B : SimpleGraph S) (p : S) (rigid : PointRigid B p) : Nonempty (Labels V (Marked S)) := by
  let L (x : Node V (Marked S)) := recordGraph B p (code i x)
  have conn (x : Node V (Marked S)) (a b : Marked S) : Reach (L x).Adj a b :=
    mark_connected _ (paths_connected _ _ (skeleton_connected B p)) _ a b
  refine ⟨⟨L,⟨.inr false⟩,conn,?_,fun _ _ h => code_inj inj (record_distinguishes B p rigid h)⟩⟩
  intro x a
  obtain ⟨b,ne⟩ : ∃ b : Marked S, a ≠ b := by
    cases a with
    | inl _ => exact ⟨.inr false,fun eq => by cases eq⟩
    | inr c => exact ⟨.inr (!c),fun h => by cases c <;> cases h⟩
  have last (u : Marked S) (path : Reach (L x).Adj b u) : u=b ∨ ∃ z, (L x).Adj u z := by
    cases path with
    | refl => exact Or.inl rfl
    | tail _ e => exact Or.inr ⟨_,e.symm⟩
  exact (last a (conn x b a)).elim (fun h => (ne h).elim) id

/-- The global rigid-embedding principle entails the full CWFAFA₂ decoration
property, for all extensional accessible pointed digraphs. -/
theorem rigid_embeddings_imply_cwf (em : ∀ p : Prop, p ∨ ¬p)
    (embed : ∀ I : Type u, ∃ (S : Type u) (B : SimpleGraph S) (p : S) (i : I → S),
      PointRigid B p ∧ Function.Injective i) {V : Type u} (D : V → V → Prop) (o : V)
    (acc : AccessibleFrom D o) (extD : Extensional D) : Nonempty (Representation.{u,u} D o) := by
  apply reusable_labels_suffice em _ D o acc extD
  intro I
  obtain ⟨S,B,p,i,rigid,inj⟩ := embed I
  exact ⟨Marked S, labels_of_embedding i inj B p rigid⟩

end WeakFrucht

namespace WeakFrucht

/-- Two fixed columns in addition to one column per element. -/
abbrev Site (X : Type u) := ℤ × Option (Option X)

def EventuallyShift {X : Type u} (f : Equiv.Perm (Site X)) : Prop :=
  ∃ k N : ℤ, ∀ z ≥ N, ∀ t, f (z,t) = (z+k,t)

/-- Permutations agreeing with a single translation on all sufficiently high rows. -/
abbrev Shift (X : Type u) := {f : Equiv.Perm (Site X) // EventuallyShift f}

namespace Shift

variable {X : Type u}

theorem comp_tail {f g : Equiv.Perm (Site X)} (hf : EventuallyShift f) (hg : EventuallyShift g) :
    EventuallyShift (g.trans f) := by
  obtain ⟨i,m,a⟩ := hf
  obtain ⟨j,n,b⟩ := hg
  refine ⟨j+i,max n (m-j),fun z hz t => ?_⟩
  change f (g (z,t)) = _
  have bound := Int.add_le_add_right (le_trans (le_max_right n (m-j)) hz) j
  rw [Int.sub_add_cancel] at bound
  rw [b z (le_trans (le_max_left ..) hz) t,a (z+j) bound t,add_assoc]

theorem inv_tail {f : Equiv.Perm (Site X)} (hf : EventuallyShift f) : EventuallyShift f.symm := by
  obtain ⟨k,n,a⟩ := hf
  refine ⟨-k,n+k,fun z hz t => ?_⟩
  apply f.injective
  have bound : n ≤ z + -k := by
    exact Int.le_sub_right_of_add_le hz
  rw [f.apply_symm_apply,a (z + -k) bound t,← sub_eq_add_neg,sub_add_cancel]

instance group : Group (Shift X) where
  mul f g := ⟨g.val.trans f.val,comp_tail f.property g.property⟩
  one := ⟨Equiv.refl _,0,0,fun z _ t => by simp⟩
  inv f := ⟨f.val.symm,inv_tail f.property⟩
  mul_assoc _ _ _ := rfl
  one_mul _ := Subtype.ext (Equiv.ext fun _ => rfl)
  mul_one _ := Subtype.ext (Equiv.ext fun _ => rfl)
  inv_mul_cancel f := Subtype.ext (Equiv.ext f.val.symm_apply_apply)

def up : Shift X := ⟨{
    toFun := fun (z,t) => (z+1,t)
    invFun := fun (z,t) => (z-1,t)
    left_inv := by rintro ⟨z,t⟩; simp
    right_inv := by rintro ⟨z,t⟩; simp },
  1,0,fun _ _ _ => rfl⟩

def exchange {Y : Type v} [DecidableEq Y] (a b x : Y) := if x=a then b else if x=b then a else x

theorem exchange_left {Y : Type v} [DecidableEq Y] (a b : Y) : exchange a b a = b := by
  unfold exchange; rw [ite_eq_left rfl]

theorem exchange_fixes {Y : Type v} [DecidableEq Y] {a b x : Y} (xa : x ≠ a) (xb : x ≠ b) :
    exchange a b x = x := by unfold exchange; rw [ite_eq_right xa,ite_eq_right xb]

theorem exchange_twice {Y : Type v} [DecidableEq Y] {a b : Y} (ab : a ≠ b) (x : Y) :
    exchange a b (exchange a b x) = x := by
  have right : exchange a b b = a := by unfold exchange; rw [ite_eq_right ab.symm,ite_eq_left rfl]
  by_cases xa : x=a
  · rw [xa,exchange_left,right]
  by_cases xb : x=b
  · rw [xb,right,exchange_left]
  · rw [exchange_fixes xa xb,exchange_fixes xa xb]

theorem high_row_ne_zero {z : ℤ} (hz : 1 ≤ z) : z ≠ 0 :=
  (Int.lt_of_lt_of_le Int.zero_lt_one hz).ne'

def swapZero [DecidableEq X] (t : Option X) : Shift X :=
  let a : Site X := (0,none)
  let b : Site X := (0,some t)
  have ne : a ≠ b := by intro e; have h := congrArg (fun p : Site X => p.2) e; cases h
  ⟨⟨exchange a b,exchange a b,exchange_twice ne,exchange_twice ne⟩,
   0,1,by
    intro z hz u
    change exchange a b (z,u) = (z+0,u)
    rw [exchange_fixes (fun e => high_row_ne_zero hz (congrArg Prod.fst e)) (fun e => high_row_ne_zero hz (congrArg Prod.fst e)),add_zero]⟩

def pin [DecidableEq X] : Shift X := swapZero none

def encode [DecidableEq X] (x : X) : Shift X := swapZero (some x)

theorem encode_injective [DecidableEq X] : Function.Injective (@encode X _) := by
  intro x y e
  have h := congrArg (fun f : Shift X => f.val (0,none)) e
  change exchange (Y := Site X) (0,none) (0,some (some x)) (0,none) = exchange (0,none) (0,some (some y)) (0,none) at h
  simp only [exchange_left] at h
  exact Option.some.inj (Option.some.inj (congrArg Prod.snd h))

/-- Commutation with the vertical unit shift propagates the high-row formula to
every row. The single swap of the two fixed columns then forces zero displacement. -/
theorem centralizer [DecidableEq X] (f : Shift X) (cu : f*up = up*f) (cs : f*pin = pin*f) : f=1 := by
  obtain ⟨k,N,tail⟩ := f.property
  have unit (z : ℤ) (t : Option (Option X)) :
      f.val (z+1,t) = ((f.val (z,t)).1+1,(f.val (z,t)).2) := by
    exact congrArg (fun a : Shift X => a.val (z,t)) cu
  have many (z : ℤ) (t : Option (Option X)) (n : ℕ) :
      f.val (z+n,t) = ((f.val (z,t)).1+n,(f.val (z,t)).2) := by
    induction n with
    | zero => simp
    | succ n ih =>
      change f.val (z + ((n:ℤ)+1),t) = ((f.val (z,t)).1 + ((n:ℤ)+1),(f.val (z,t)).2)
      rw [← add_assoc,unit,ih]; simp [add_assoc]
  have all (z : ℤ) (t : Option (Option X)) : f.val (z,t) = (z+k,t) := by
    let n := (N-z).toNat
    have hn : N ≤ z + (n:ℤ) := by dsimp [n]; omega
    have e := (many z t n).symm.trans (tail _ hn t)
    apply Prod.ext
    · have h := congrArg Prod.fst e
      change (f.val (z,t)).1 + (n:ℤ) = z+(n:ℤ)+k at h
      omega
    · have es := congrArg (fun p : Site X => p.2) e
      exact es
  have kk : k=0 := by
    by_contra hk
    have e := congrArg (fun a : Shift X => a.val (0,none)) cs
    change f.val (exchange (Y := Site X) (0,none) (0,some none) (0,none)) = exchange (0,none) (0,some none) (f.val (0,none)) at e
    rw [exchange_left,all,all,zero_add,exchange_fixes
      (fun eq => hk (congrArg Prod.fst eq)) (fun eq => hk (congrArg Prod.fst eq))] at e
    have es := congrArg (fun p : Site X => p.2) e
    cases es
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨z,t⟩
  change f.val (z,t) = (z,t)
  simpa only [kk,add_zero] using all z t

end Shift
end WeakFrucht

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

namespace WeakFrucht

/-- The new direction of the draft, in the pointwise group-action formulation.
Ordinary two-valued propositional logic is explicit. The construction uses
Frucht at the one group of eventual translations associated to the target. -/
theorem action_frucht_implies_cwf [d : ∀ p : Prop, Decidable p] (ft : ActionFrucht.{u})
    {V : Type u} (D : V → V → Prop) (o : V) (acc : AccessibleFrom D o) (extD : Extensional D) :
    Nonempty (Representation.{u,u} D o) :=
  rigid_embeddings_imply_cwf (fun p => match d p with | .isTrue h => Or.inl h | .isFalse h => Or.inr h)
    (embedding_of_actions ft) D o acc extD

/-- Frucht's theorem for full automorphism groups of simple graphs implies
CWFAFA₂ for all extensional accessible pointed directed graphs. -/
theorem frucht_implies_cwf (ft : Frucht.{u}) {V : Type u} (D : V → V → Prop) (o : V)
    (acc : AccessibleFrom D o) (extD : Extensional D) : Nonempty (Representation.{u,u} D o) := by
  classical
  exact action_frucht_implies_cwf (actions_of_frucht ft) D o acc extD

end WeakFrucht
