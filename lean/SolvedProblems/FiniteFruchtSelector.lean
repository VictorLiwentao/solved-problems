module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Set.Insert

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
