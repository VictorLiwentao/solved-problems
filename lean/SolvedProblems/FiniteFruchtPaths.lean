module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.End

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
