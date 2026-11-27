module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

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
