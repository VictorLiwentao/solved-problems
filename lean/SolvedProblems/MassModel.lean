module

public import Std

@[expose] public section

namespace PromiseMass

/-- The coordinatewise ternary addition relation in the k-fold strict template. -/
inductive Adds : List Bool → List Bool → List Bool → Prop
  | nil : Adds [] [] []
  | cons {a b c : Bool} {xs ys zs} :
      a.toNat + b.toNat = c.toNat → Adds xs ys zs → Adds (a::xs) (b::ys) (c::zs)

def poly (k m : Nat) (f : List Bool → Nat) :=
  f (List.replicate k false) = 0 ∧ f (List.replicate k true) = m ∧
  (∀ xs, xs.length = k → f xs ≤ m) ∧
  ∀ xs ys zs, xs.length = k → Adds xs ys zs → f xs + f ys = f zs

/-- Invariance under the cyclic group, expressed as rotation at any cut. -/
def cyclic (k : Nat) (f : List Bool → Nat) :=
  ∀ u v : List Bool, u.length + v.length = k → f (u ++ v) = f (v ++ u)

def symmetric (k : Nat) (f : List Bool → Nat) :=
  ∀ u v : List Bool, u.length = k → u.Perm v → f u = f v

end PromiseMass
