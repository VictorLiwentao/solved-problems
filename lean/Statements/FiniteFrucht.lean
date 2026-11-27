module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Equiv.Defs

@[expose] public section

namespace FiniteFrucht

/-- A nonempty finite set, with finiteness asserted by existence of a listing.
The list is a propositionally truncated witness and is not part of the object. -/
def Family (Y : Type u) := {F : Set Y // (∃ y, y ∈ F) ∧ ∃ l : List Y, ∀ y, y ∈ F ↔ y ∈ l}

/-- Choice for all nonempty finite subsets of Y, simultaneously over the sizes. -/
def ChoiceFin (Y : Type u) : Prop := ∃ s : Family Y → Y, ∀ F, s F ∈ F.val

/-- The action on subsets induced by a permutation. -/
def img {X : Type u} (g : Equiv.Perm X) (S : Set X) : Set X := fun x => g.symm x ∈ S

@[simp] theorem mem_img {X : Type u} (g : Equiv.Perm X) (S : Set X) (x : X) :
    g x ∈ img g S ↔ x ∈ S := by change g.symm (g x) ∈ S ↔ _; rw [g.symm_apply_apply]

private theorem img_injective {X : Type u} (g : Equiv.Perm X) : Function.Injective (img g) := by
  intro S T h
  ext x
  exact (mem_img g S x).symm.trans (h ▸ mem_img g T x)

private theorem img_singleton {X : Type u} (g : Equiv.Perm X) (x : X) :
    img g {x} = {g x} := by
  ext z
  change g.symm z = x ↔ z = g x
  exact ⟨fun h => (g.apply_symm_apply z).symm.trans (congrArg g h),
    fun h => (congrArg g.symm h).trans (g.symm_apply_apply x)⟩

private def step {X} (g : Equiv.Perm X) : ℕ → Equiv.Perm X
  | 0 => Equiv.refl X
  | n+1 => (step g n).trans g

private theorem commutes {X} (g : Equiv.Perm X) (n : ℕ) (x : X) :
    step g n (g x) = g (step g n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg g ih

private theorem inv_commutes {X} (g : Equiv.Perm X) (n : ℕ) (x : X) :
    (step g n).symm (g x) = g ((step g n).symm x) := by
  apply (step g n).injective
  rw [Equiv.apply_symm_apply,commutes,Equiv.apply_symm_apply]

private def point {X} (g : Equiv.Perm X) (x : X) : ℤ → X
  | .ofNat n => step g n x
  | .negSucc n => (step g (n+1)).symm x

private theorem next_point {X} (g : Equiv.Perm X) (x : X) (z : ℤ) :
    g (point g x z) = point g x (z + 1) := by
  cases z with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero => exact g.apply_symm_apply x
    | succ n =>
      rw [show Int.negSucc (n+1) + 1 = Int.negSucc n by omega]
      change g ((step g (n+1)).symm (g.symm x)) = (step g (n+1)).symm x
      rw [← inv_commutes,g.apply_symm_apply]

private theorem point_zero {X} (g : Equiv.Perm X) (x : X) : point g x 0 = x := rfl

private theorem point_moved {X} {g : Equiv.Perm X} {x : X} (h : g x ≠ x) (z : ℤ) :
    g (point g x z) ≠ point g x z := by
  intro eq
  apply h
  cases z with
  | ofNat n => exact (step g n).injective ((commutes g n x).trans eq)
  | negSucc n => exact (step g (n+1)).symm.injective ((inv_commutes g (n+1) x).trans eq)

private def cycle {X} (g : Equiv.Perm X) (x : X) (n : ℕ) (hn : 0 < n) : Family (Set X) :=
  ⟨{S | ∃ k < n, S = {point g x k}}, ⟨_,0,hn,rfl⟩,
    (List.range n).map (fun k : ℕ => ({point g x k} : Set X)), fun S => by
      change (∃ k < n, S = {point g x k}) ↔ _
      simp only [List.mem_map, List.mem_range]
      exact ⟨fun ⟨k,h,e⟩ => ⟨k,h,e.symm⟩, fun ⟨k,h,e⟩ => ⟨k,h,e.symm⟩⟩⟩

private theorem cycle_stable {X} (g : Equiv.Perm X) (x : X) {n : ℕ} (hn : 0 < n)
    (per : point g x n = x) (S : Set X) : S ∈ (cycle g x n hn).val ↔ img g S ∈ (cycle g x n hn).val := by
  constructor
  · rintro ⟨k,hk,rfl⟩
    rw [img_singleton,next_point]
    rcases Nat.lt_or_eq_of_le (show k+1 ≤ n by omega) with lt | eq
    · exact ⟨k+1,lt,by simp⟩
    · exact ⟨0,hn,by simpa [← eq,point_zero] using congrArg (fun z => ({z} : Set X)) per⟩
  · rintro ⟨k,hk,eq⟩
    cases k with
    | zero =>
      refine ⟨n-1, by omega, img_injective g ?_⟩
      rw [eq,img_singleton,next_point]
      have h : ((n-1 : ℕ) : ℤ) + 1 = n := by omega
      rw [h,per]; simp [point_zero]
    | succ k =>
      exact ⟨k,by omega,img_injective g (by rw [eq,img_singleton,next_point]; simp)⟩

private def evenOrbit {X} (g : Equiv.Perm X) (x : X) : Set X :=
  {y | ∃ z : ℤ, y = point g x (2*z)}

private theorem even_twice {X} (g : Equiv.Perm X) (x : X) :
    img g (img g (evenOrbit g x)) = evenOrbit g x := by
  ext y
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z+1,?_⟩
    have eq := congrArg g (congrArg g hz)
    simpa [next_point,show 2*(z+1) = 2*z+1+1 by omega] using eq
  · rintro ⟨z,rfl⟩
    refine ⟨z-1,?_⟩
    apply g.injective
    apply g.injective
    simp [next_point,show 2*(z-1)+1+1 = 2*z by omega]

private theorem positive_period {X} (g : Equiv.Perm X) (x : X) (q : ℤ) (nz : q ≠ 0)
    (hp : point g x q = x) : ∃ n : ℕ, 0 < n ∧ point g x n = x := by
  cases q with
  | ofNat n => exact ⟨n,Nat.pos_of_ne_zero (fun e => nz (by rw [e]; rfl)),hp⟩
  | negSucc n =>
    have h := congrArg (step g (n+1)) hp
    change (step g (n+1)) ((step g (n+1)).symm x) = _ at h
    rw [Equiv.apply_symm_apply] at h
    exact ⟨n+1,by omega,h.symm⟩

private def pairFamily {X} (A B : Set X) : Family (Set X) :=
  ⟨{S | S = A ∨ S = B}, ⟨A,Or.inl rfl⟩, [A,B], fun S => by simp⟩

/-- An equivariant finite selector cannot move any point of the underlying set.
A periodic moving point gives a finite family of singletons. An aperiodic point
gives a two-element family, the alternating halves of its integer orbit. -/
theorem selector_fixes {X : Type u} (em : ∀ p : Prop, p ∨ ¬p)
    (s : Family (Set X) → Set X) (member : ∀ F, s F ∈ F.val) (g : Equiv.Perm X)
    (stable : ∀ F : Family (Set X), (∀ S, S ∈ F.val ↔ img g S ∈ F.val) → img g (s F) = s F)
    (x : X) : g x = x := by
  rcases em (g x = x) with h | moved
  · exact h
  exfalso
  rcases em (∃ n : ℕ, 0 < n ∧ point g x n = x) with per | aper
  · obtain ⟨n,hn,hp⟩ := per
    let F := cycle g x n hn
    have fixed := stable F (cycle_stable g x hn hp)
    obtain ⟨k,_,hs⟩ := member F
    rw [hs,img_singleton] at fixed
    exact point_moved moved k (Set.singleton_injective fixed)
  · let A := evenOrbit g x
    let B := img g A
    have swap : img g B = A := even_twice g x
    have ne : B ≠ A := by
      intro eq
      have hx : x ∈ A := ⟨0, by simp [point_zero]⟩
      have hB : g x ∈ B := (mem_img g A x).mpr hx
      obtain ⟨z,hz⟩ := (eq ▸ hB : g x ∈ A)
      apply aper (positive_period g x (2*z-1) (by omega) ?_)
      apply g.injective
      rw [next_point, show 2*z-1+1 = 2*z by omega, ← hz]
    let F := pairFamily A B
    have fixed := stable F (fun S => by
      change (S = A ∨ S = B) ↔ img g S = A ∨ img g S = B
      constructor
      · rintro (rfl|rfl)
        · exact Or.inr rfl
        · exact Or.inl swap
      · rintro (h|h)
        · exact Or.inr (img_injective g (h.trans swap.symm))
        · exact Or.inl (img_injective g h))
    rcases (member F : s F = A ∨ s F = B) with h | h
    · rw [h] at fixed
      exact ne fixed
    · rw [h,swap] at fixed
      exact ne fixed.symm

end FiniteFrucht

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

/-- The two copies of G are kept distinct. A multiplication triple has separate
input and output vertices, even if its two group arguments coincide. -/
inductive Tag | pt | label | subset | family | pick | triple | input | output

def Tag.code : Tag → ℕ
  | .pt => 0 | .label => 1 | .subset => 2 | .family => 3
  | .pick => 4 | .triple => 5 | .input => 6 | .output => 7

private theorem code_injective : Function.Injective Tag.code := by
  intro i j h
  cases i <;> cases j <;> simp_all [Tag.code]

abbrev Data (G : Type u) : Tag → Type u
  | .pt | .label => G
  | .subset => Set G
  | .family | .pick => Family (Set G)
  | .triple | .input | .output => G × G

abbrev Core (G : Type u) := Sigma (Data G)

def color {G : Type u} (q : Core G) := q.1.code

variable {G : Type u} [Group G] (sel : Family (Set G) → Set G)

/-- Adjacency between distinct sorts records both membership relations, the
selector, and the three ordered arguments of the multiplication relation. -/
def arcs : (i j : Tag) → Data G i → Data G j → Prop
  | .pt, .input, x, t => x = t.1
  | .pt, .output, x, t => x = t.1*t.2
  | .label, .subset, x, S => x ∈ S
  | .label, .triple, x, t => x = t.2
  | .subset, .family, S, F => S ∈ F.val
  | .subset, .pick, S, F => S = sel F
  | .family, .pick, F, H => F = H
  | .triple, .input, t, q => t = q
  | .triple, .output, t, q => t = q
  | _, _, _, _ => False

def coreGraph : SimpleGraph (Core G) where
  Adj u v := arcs sel u.1 v.1 u.2 v.2 ∨ arcs sel v.1 u.1 v.2 u.2
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by rintro ⟨i,x⟩; cases i <;> simp [arcs]⟩

/-- Left multiplication acts on group points and on the first component of a
multiplication triple. It acts identically on the whole label structure. -/
def translation (a : G) : (i : Tag) → Data G i → Data G i
  | .pt, x => a*x
  | .label, x => x
  | .subset, S => S
  | .family, F => F
  | .pick, F => F
  | .triple, t => (a*t.1,t.2)
  | .input, t => (a*t.1,t.2)
  | .output, t => (a*t.1,t.2)

def corePerm (a : G) : Equiv.Perm (Core G) where
  toFun q := ⟨q.1, translation a q.1 q.2⟩
  invFun q := ⟨q.1, translation a⁻¹ q.1 q.2⟩
  left_inv := by rintro ⟨i,x⟩; cases i <;> simp [translation]
  right_inv := by rintro ⟨i,x⟩; cases i <;> simp [translation]

theorem corePerm_color (a : G) (q : Core G) : color (corePerm a q) = color q := rfl

private theorem translation_arcs (a : G) (i j : Tag) (x : Data G i) (y : Data G j) :
    arcs sel i j (translation a i x) (translation a j y) ↔ arcs sel i j x y := by
  cases i <;> cases j <;> simp [arcs,translation,mul_assoc]
  all_goals exact ⟨fun h => Prod.ext h.1 h.2,fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩

theorem corePerm_adj (a : G) : Preserves (coreGraph sel) (corePerm a) := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  exact or_congr (translation_arcs sel a i j x y) (translation_arcs sel a j i y x)

private def valAt {K : Type v} {T : K → Type u} (q : Sigma T) {k : K} (e : q.1 = k) : T k :=
  e ▸ q.2

private theorem mk_valAt {K : Type v} {T : K → Type u} (q : Sigma T) {k : K} (e : q.1 = k) :
    (⟨k,valAt q e⟩ : Sigma T) = q := by cases q; cases e; rfl

private theorem mk_inj {K : Type v} {T : K → Type u} {k : K} {x y : T k}
    (h : (⟨k,x⟩ : Sigma T) = ⟨k,y⟩) : x = y := eq_of_heq (Sigma.mk.inj h).2

private theorem symm_typed {K : Type v} {T : K → Type u} (f : Equiv.Perm (Sigma T))
    (typed : ∀ u, (f u).1 = u.1) (u : Sigma T) : (f.symm u).1 = u.1 := by
  simpa using (typed (f.symm u)).symm

private def sortPerm {K : Type v} {T : K → Type u} (f : Equiv.Perm (Sigma T))
    (typed : ∀ u, (f u).1 = u.1) (k : K) : Equiv.Perm (T k) where
  toFun x := valAt (f ⟨k,x⟩) (typed ⟨k,x⟩)
  invFun x := valAt (f.symm ⟨k,x⟩) (symm_typed f typed ⟨k,x⟩)
  left_inv x := by
    apply mk_inj; dsimp only; rw [mk_valAt,mk_valAt,f.symm_apply_apply]
  right_inv x := by
    apply mk_inj; dsimp only; rw [mk_valAt,mk_valAt,f.apply_symm_apply]

private theorem sort_eq {K : Type v} {T : K → Type u} (f : Equiv.Perm (Sigma T))
    (typed : ∀ u, (f u).1 = u.1) (k : K) (x : T k) :
    f ⟨k,x⟩ = ⟨k,sortPerm f typed k x⟩ := (mk_valAt _ _).symm

/-- A color-preserving automorphism is uniquely a left translation. Its group
element is read off at the identity point. -/
theorem core_is_translation (em : ∀ p : Prop, p ∨ ¬p) (member : ∀ F, sel F ∈ F.val)
    (f : Equiv.Perm (Core G)) (hc : ∀ u, color (f u) = color u)
    (hf : Preserves (coreGraph sel) f) : ∃ a : G, ∀ u, f u = corePerm a u := by
  have typed (u : Core G) : (f u).1 = u.1 := code_injective (hc u)
  let a := sortPerm f typed
  have adj (i j : Tag) (x : Data G i) (y : Data G j) :
      (coreGraph sel).Adj ⟨i,a i x⟩ ⟨j,a j y⟩ ↔ (coreGraph sel).Adj ⟨i,x⟩ ⟨j,y⟩ := by
    rw [← sort_eq f typed,← sort_eq f typed]
    exact hf _ _
  have inc (x : G) (S : Set G) : a .label x ∈ a .subset S ↔ x ∈ S := by
    simpa [coreGraph,arcs] using adj .label .subset x S
  have img_eq (S : Set G) : a .subset S = img (a .label) S := by
    ext y
    change y ∈ a .subset S ↔ (a .label).symm y ∈ S
    simpa only [Equiv.apply_symm_apply] using inc ((a .label).symm y) S
  have fam (S : Set G) (F : Family (Set G)) : a .subset S ∈ (a .family F).val ↔ S ∈ F.val := by
    simpa [coreGraph,arcs] using adj .subset .family S F
  have pick_eq (F : Family (Set G)) : a .family F = a .pick F := by
    simpa [coreGraph,arcs] using (adj .family .pick F F).mpr (Or.inl rfl)
  have choose_eq (F : Family (Set G)) : a .subset (sel F) = sel (a .family F) := by
    rw [pick_eq]; simpa [coreGraph,arcs] using (adj .subset .pick (sel F) F).mpr (Or.inl rfl)
  have family_fixed (F : Family (Set G)) (stable : ∀ S, S ∈ F.val ↔ a .subset S ∈ F.val) : a .family F = F := by
    apply Subtype.ext
    ext T
    obtain ⟨S,rfl⟩ := (a .subset).surjective T
    exact (fam S F).trans (stable S)
  have label_fixed : ∀ x : G, a .label x = x := by
    apply selector_fixes em sel member
    intro F invariant
    have fixF := family_fixed F (fun S => by rw [img_eq]; exact invariant S)
    rw [← img_eq,choose_eq,fixF]
  have subset_fixed (S : Set G) : a .subset S = S := by
    ext x; simpa only [label_fixed] using inc x S
  have fam_fixed (F : Family (Set G)) : a .family F = F := family_fixed F (fun S => by rw [subset_fixed])
  have pick_fixed (F : Family (Set G)) : a .pick F = F := (pick_eq F).symm.trans (fam_fixed F)
  have third (h g : G) : (a .triple (h,g)).2 = g := by
    have := (adj .label .triple g (h,g)).mpr (Or.inl rfl)
    symm; simpa [coreGraph,arcs,label_fixed] using this
  have inlet (h g : G) : a .input (h,g) = a .triple (h,g) := by
    symm; simpa [coreGraph,arcs] using (adj .triple .input (h,g) (h,g)).mpr (Or.inl rfl)
  have outlet (h g : G) : a .output (h,g) = a .triple (h,g) := by
    symm; simpa [coreGraph,arcs] using (adj .triple .output (h,g) (h,g)).mpr (Or.inl rfl)
  have first (h g : G) : (a .triple (h,g)).1 = a .pt h := by
    have := (adj .pt .input h (h,g)).mpr (Or.inl rfl)
    symm; simpa [coreGraph,arcs,inlet] using this
  have trans (h : G) : a .pt h = (a .pt 1)*h := by
    have := (adj .pt .output h (1,h)).mpr (Or.inl (one_mul h).symm)
    simpa [coreGraph,arcs,outlet,first,third] using this
  have pair (h g : G) : a .triple (h,g) = ((a .pt 1)*h,g) := Prod.ext ((first h g).trans (trans h)) (third h g)
  refine ⟨a .pt 1,?_⟩
  rintro ⟨i,x⟩
  rw [sort_eq f typed]; change (⟨i,a i x⟩ : Core G) = ⟨i,translation _ i x⟩
  apply congrArg (Sigma.mk i)
  cases i with
  | pt => exact trans x
  | label => exact label_fixed x
  | subset => exact subset_fixed x
  | family => exact fam_fixed x
  | pick => exact pick_fixed x
  | triple => exact pair x.1 x.2
  | input => exact (inlet x.1 x.2).trans (pair x.1 x.2)
  | output => exact (outlet x.1 x.2).trans (pair x.1 x.2)

end FiniteFrucht

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
