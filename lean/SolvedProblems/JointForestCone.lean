module

public import SolvedProblems.JointForestModel

@[expose] public section

namespace JointForest

open SimpleGraph

/-- Add one loopless vertex adjacent to every old vertex. -/
def cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | some u, some v => G.Adj u v
    | _, _ => True
  symm := ⟨fun u v => by cases u <;> cases v <;> first | exact fun h => h | exact fun h => G.symm.symm _ _ h⟩
  loopless := ⟨fun u => by cases u <;> simp⟩

/-- Candidate preimages of the cone vertex. -/
abbrev Independent {U : Type*} (F : SimpleGraph U) :=
  {s : Set U // ∀ u ∈ s, ∀ v ∈ s, ¬ F.Adj u v}

/-- Remove the specified preimage of the hub from the pattern. -/
def outside {U : Type*} (F : SimpleGraph U) (s : Independent F) :
    SimpleGraph {u // u ∉ s.val} := F.comap Subtype.val

def hubSet {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} (f : F →g cone G) : Independent F :=
  ⟨{u | f u = none}, fun u (hu : f u = none) v (hv : f v = none) huv => by
    have h := f.map_adj huv
    rw [hu, hv] at h
    exact h⟩

abbrev HubFiber {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V) (s : Independent F) :=
  {f : F →g cone G // hubSet f = s}

theorem in_hub_iff {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) (x : U) : x ∈ s.val ↔ f.val x = none := by
  exact Iff.of_eq (congrArg (fun t : Independent F => x ∈ t.val) f.property.symm)

def rimVal {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) (x : {u // u ∉ s.val}) : V :=
  (f.val x.val).get (Option.isSome_iff_ne_none.mpr fun h => x.property ((in_hub_iff f _).mpr h))

theorem some_rimVal {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) (x : {u // u ∉ s.val}) : some (rimVal f x) = f.val x.val := Option.some_get _

def restrictHub {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : HubFiber F G s) : outside F s →g G where
  toFun := rimVal f
  map_rel' := fun {x y} h => by
    have hh := f.val.map_adj (show F.Adj x.val y.val from h)
    rw [← some_rimVal f x, ← some_rimVal f y] at hh
    exact hh

noncomputable def extendHub {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : outside F s →g G) : F →g cone G := by
  classical
  refine ⟨fun x => if h : x ∈ s.val then none else some (f ⟨x,h⟩), ?_⟩
  intro x y hxy
  split_ifs with hx hy hy
  · exact (s.property x hx y hy hxy).elim
  · trivial
  · trivial
  · exact f.map_adj hxy

theorem extend_hubSet {U V : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {s : Independent F}
    (f : outside F s →g G) : hubSet (extendHub f) = s := by
  classical
  apply Subtype.ext
  ext x
  change (if h : x ∈ s.val then none else some (f ⟨x,h⟩)) = none ↔ _
  split <;> simp_all

/-- Specifying precisely the preimage of the hub leaves an arbitrary rim
homomorphism on the induced complement. -/
noncomputable def hubEquiv {U V : Type*} (F : SimpleGraph U) (G : SimpleGraph V) (s : Independent F) :
    HubFiber F G s ≃ (outside F s →g G) where
  toFun := restrictHub
  invFun f := ⟨extendHub f, extend_hubSet f⟩
  left_inv f := by
    classical
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    by_cases h : x ∈ s.val
    · simpa [extendHub, h] using ((in_hub_iff f x).mp h).symm
    · simpa [extendHub, restrictHub, h] using some_rimVal f ⟨x,h⟩
  right_inv r := by
    classical
    apply DFunLike.ext
    intro x
    apply Option.some.inj
    exact (some_rimVal (⟨extendHub r, extend_hubSet r⟩ : HubFiber F G s) x).trans (by simp [extendHub, x.property])

attribute [local instance] Classical.propDecidable

/-- Exact cone homomorphism identity for all finite simple patterns and hosts,
including the empty pattern and empty rim. -/
theorem cone_hom_count {U V : Type*} [Fintype U] [Fintype V] (F : SimpleGraph U) (G : SimpleGraph V) :
    homCount F (cone G) = ∑ s : Independent F, homCount (outside F s) G := by
  classical
  let e := Equiv.sigmaFiberEquiv (hubSet (F := F) (G := G))
  rw [homCount, ← Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun s _ => Nat.card_congr (hubEquiv F G s))

end JointForest
