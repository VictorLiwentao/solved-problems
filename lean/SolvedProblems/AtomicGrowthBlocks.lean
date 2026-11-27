module

public import SolvedProblems.AtomicGrowthPatterns
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open List

namespace AtomicGrowth

abbrev Class := Set Word

noncomputable def level (A : Class) (n : ℕ) : Finset Word := by
  classical
  exact (List.range n).permutations.toFinset.filter (· ∈ A)

theorem mem_level {A : Class} {n : ℕ} {w : Word} :
    w ∈ level A n ↔ IsPerm w ∧ w.length = n ∧ w ∈ A := by
  classical
  rw [level,Finset.mem_filter,List.mem_toFinset,List.mem_permutations]
  constructor
  · rintro ⟨hp,hA⟩
    have hn : w.length=n := by simpa using hp.length_eq
    exact ⟨by simpa [IsPerm,hn] using hp,hn,hA⟩
  · rintro ⟨hp,hn,hA⟩
    exact ⟨by simpa [IsPerm,hn] using hp,hA⟩

def Hereditary (A : Class) : Prop := ∀ v ∈ A, ∀ u, Contains u v → u ∈ A

def Atomic (A : Class) : Prop := ∀ u ∈ A, ∀ v ∈ A, ∃ t ∈ A, Contains u t ∧ Contains v t

def blocks : List Word → Word
  | [] => []
  | w::ws => direct w (blocks ws)

@[simp] theorem direct_length (u v : Word) : (direct u v).length = u.length+v.length := by simp [direct]

@[simp] theorem direct_nil (w : Word) : direct w [] = w := by simp [direct]
@[simp] theorem nil_direct (w : Word) : direct [] w = w := by simp [direct]

theorem direct_assoc (u v w : Word) : direct (direct u v) w = direct u (direct v w) := by
  simp [direct,List.map_map,Function.comp_def,Nat.add_assoc]

theorem blocks_append (xs ys : List Word) : blocks (xs++ys) = direct (blocks xs) (blocks ys) := by
  induction xs with
  | nil => simp [blocks]
  | cons x xs ih => simp [blocks,ih,direct_assoc]

theorem blocks_perm (xs : List Word) (h : ∀ x ∈ xs, IsPerm x) : IsPerm (blocks xs) := by
  induction xs with
  | nil => exact List.Perm.refl []
  | cons x xs ih => exact direct_perm (h x (by simp)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem block_contains {xs : List Word} {x : Word} (h : x ∈ xs) (hp : IsPerm x) : Contains x (blocks xs) := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨x,List.sublist_append_left ..,standard_of_perm hp⟩
    · obtain ⟨y,hy,he⟩ := ih h
      exact ⟨y.map (a.length+·),(hy.map _).trans (List.sublist_append_right ..),(standard_shift _ _).trans he⟩

theorem prefix_contains {xs ys : List Word} {x : Word} (h : Contains x (blocks xs)) : Contains x (blocks (xs++ys)) := by
  obtain ⟨y,hy,he⟩ := h
  rw [blocks_append]
  exact ⟨y,hy.trans (List.sublist_append_left ..),he⟩

def stages (s : ℕ → List Word) (k : ℕ) : List Word := (List.range k).flatMap s

def jointClass (s : ℕ → List Word) : Class := {w | ∃ k, Contains w (blocks (stages s k))}

theorem stages_add (s : ℕ → List Word) (k d : ℕ) :
    stages s (k+d) = stages s k ++ (List.range d).flatMap (fun i => s (k+i)) := by
  simp [stages,List.range_add,List.flatMap_map]

theorem stages_perm {s : ℕ → List Word} (h : ∀ i, ∀ x ∈ s i, IsPerm x) (k) : IsPerm (blocks (stages s k)) := by
  apply blocks_perm
  intro x hx
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hx
  exact h i x hi

theorem joint_atomic {s : ℕ → List Word} (h : ∀ i, ∀ x ∈ s i, IsPerm x) : Atomic (jointClass s) := by
  rintro u ⟨i,hi⟩ v ⟨j,hj⟩
  have hl (w k l) (hkl : k≤l) (hw : Contains w (blocks (stages s k))) : Contains w (blocks (stages s l)) := by
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hkl
    rw [stages_add]
    exact prefix_contains hw
  let l := max i j
  exact ⟨blocks (stages s l),⟨l,Contains.refl (stages_perm h l)⟩,hl _ i l (le_max_left ..) hi,hl _ j l (le_max_right ..) hj⟩

theorem joint_hereditary (s : ℕ → List Word) : Hereditary (jointClass s) := by
  rintro u ⟨k,hk⟩ v hv
  exact ⟨k,hv.trans hk⟩

theorem joint_perms {s : ℕ → List Word} (h : ∀ i, ∀ x ∈ s i, IsPerm x) :
    ∀ x ∈ jointClass s, IsPerm x := by
  rintro x ⟨k,y,hy,rfl⟩
  exact standard_perm (hy.nodup ((stages_perm h k).nodup_iff.mpr List.nodup_range))

theorem stage_mem_class {s : ℕ → List Word} {i : ℕ} {x : Word} (h : x ∈ s i) (hp : IsPerm x) :
    x ∈ jointClass s := ⟨i+1,block_contains (List.mem_flatMap.mpr ⟨i,by simp,h⟩) hp⟩

/-- An explicit finite set containing all direct sums of nonempty Q-blocks
at each size. A repeated representation costs only one element. -/
noncomputable def products (Q : ℕ → Finset Word) : (n : ℕ) → Finset Word
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion (fun k : Fin (n+1) => ((Q (k.val+1)) ×ˢ products Q (n-k.val)).image (fun t => direct t.1 t.2))
termination_by n => n

theorem products_prepend {Q : ℕ → Finset Word} {r k : ℕ} (hr : 0<r) {u v : Word} (hu : u ∈ Q r) (hv : v ∈ products Q k) :
    direct u v ∈ products Q (r+k) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [show r+1+k=(r+k)+1 by omega,products]
  let i : Fin (r+k+1) := ⟨r,by omega⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,?_⟩,rfl⟩⟩
  simpa [i] using hv

theorem products_suffix {Q : ℕ → Finset Word} {m : ℕ} (bs : List Word)
    (hp : ∀ b ∈ bs, IsPerm b)
    (hq : ∀ b ∈ bs, ∀ z, z.Sublist b → z.length ≤ m → z ≠ [] → standard z ∈ Q z.length)
    (z : Word) (hz : z.Sublist (blocks bs)) (hlen : z.length≤m) : standard z ∈ products Q z.length := by
  induction bs generalizing z with
  | nil =>
    have : z=[] := by simpa [blocks] using hz
    simp [this,standard,products]
  | cons b bs ih =>
    obtain ⟨u,v,rfl,hu,hv⟩ := List.sublist_append_iff.mp hz
    obtain ⟨v,hv',rfl⟩ := (List.sublist_map_iff (f:=(b.length+·)) (l₂:=blocks bs)).mp hv
    have hm : u.length+v.length≤m := by simpa using hlen
    have sep : ∀ x ∈ u, ∀ y ∈ v.map (b.length+·), x<y := by
      intro x hx y hy
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hy
      have hlt := List.mem_range.mp ((hp b (by simp)).mem_iff.mp (hu.subset hx))
      omega
    rw [standard_append _ _ sep,standard_shift,List.length_append,List.length_map]
    have hvs := ih (fun t ht => hp t (by simp [ht])) (fun t ht => hq t (by simp [ht])) v hv' (by omega)
    by_cases he : u = []
    · simpa [he,standard] using hvs
    · have h₁ : 0<u.length := List.length_pos_iff.mpr he
      exact products_prepend h₁ (hq b (by simp) u hu (by omega) he) hvs

end AtomicGrowth
