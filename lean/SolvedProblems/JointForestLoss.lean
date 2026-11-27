module

public import SolvedProblems.JointForestLong

@[expose] public section

namespace JointForest

open SimpleGraph

def emptySide {T : Type*} (F : SimpleGraph T) : Independent F := ⟨∅, by simp⟩

def outsideEmpty {T : Type*} (F : SimpleGraph T) : outside F (emptySide F) ≃g F where
  toFun := Subtype.val
  invFun t := ⟨t, Set.notMem_empty _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem empty_count {T V : Type*} (F : SimpleGraph T) (G : SimpleGraph V) :
    homCount (outside F (emptySide F)) G = homCount F G :=
  Nat.card_congr ((outsideEmpty F).homCongr (SimpleGraph.Iso.refl : G ≃g G))

/-- For every cyclic pattern a suitable twist strictly decreases its actual
homomorphism count into the cone, for every number of parallel long paths and
more interior positions than vertices of the pattern. -/
theorem cone_twist_loss {T : Type*} [LinearOrder T] [Fintype T] (F : SimpleGraph T)
    (hF : ¬F.IsAcyclic) (m r : ℕ) (hr : Fintype.card T < r) :
    ∃ d : Side T, homCount F (cone (signedLift (expanded T m r) (signing true d))) <
      homCount F (cone (signedLift (expanded T m r) (signing false d))) := by
  classical
  obtain ⟨d, hd, hw⟩ := cyclic_side F hF
  refine ⟨d, ?_⟩
  rw [cone_hom_count, cone_hom_count]
  apply Finset.sum_lt_sum
  · intro s _
    apply lift_hom_le
    apply positive_lift
    exact lt_of_le_of_lt (Fintype.card_subtype_le _) hr
  · refine ⟨emptySide F, by simp, ?_⟩
    rw [empty_count, empty_count]
    exact lift_hom_lt F _ _ _ (positive_lift hr d) (templateHom F m r) (twisted_no_lift F m r d hd hw)

theorem cone_connected {V : Type*} (G : SimpleGraph V) : (cone G).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, fun x => ?_⟩
  cases x with
  | none => exact .refl _
  | some u => exact SimpleGraph.Adj.reachable (show (cone G).Adj none (some u) from trivial)

theorem cone_dist_le_two {V : Type*} (G : SimpleGraph V) (x y : Option V) : (cone G).dist x y ≤ 2 := by
  cases x with
  | none =>
    cases y with
    | none => simp
    | some v => simp [(cone G).dist_eq_one_iff_adj.mpr (show (cone G).Adj none (some v) from trivial)]
  | some u =>
    cases y with
    | none => simp [(cone G).dist_eq_one_iff_adj.mpr (show (cone G).Adj (some u) none from trivial)]
    | some v =>
      let w : (cone G).Walk (some u) (some v) := .cons (v := none) trivial (.cons (v := some v) trivial .nil)
      exact SimpleGraph.dist_le w

/-- Opposite sheets of the same base vertex are precisely two steps apart. -/
theorem opposite_sheets_dist {T : Type*} (B : SimpleGraph T) (s : Signing T) (u : T) :
    (cone (signedLift B s)).dist (some (u,false)) (some (u,true)) = 2 := by
  let G := cone (signedLift B s)
  let x : Option (T × Bool) := some (u,false)
  let y : Option (T × Bool) := some (u,true)
  have hle := cone_dist_le_two (signedLift B s) x y
  have hz : G.dist x y ≠ 0 := fun h => by have := (cone_connected _).dist_eq_zero_iff.mp h; simp [x, y] at this
  have ho : G.dist x y ≠ 1 := fun h => B.loopless.irrefl u (G.dist_eq_one_iff_adj.mp h).1
  change G.dist x y = 2
  change G.dist x y ≤ 2 at hle
  omega

end JointForest
