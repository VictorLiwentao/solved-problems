module

public import SolvedProblems.JointForestCone

@[expose] public section

namespace JointForest

open SimpleGraph

/-- A Boolean sign is relevant only on an edge. The value `true` exchanges sheets. -/
structure Signing (V : Type*) where
  neg : V → V → Bool
  symm : ∀ x y, neg x y = neg y x

def signedLift {V : Type*} (B : SimpleGraph V) (s : Signing V) : SimpleGraph (V × Bool) where
  Adj u v := B.Adj u.1 v.1 ∧ (u.2 ^^ v.2) = s.neg u.1 v.1
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Bool.xor_comm, ← s.symm]; exact h.2⟩⟩
  loopless := ⟨fun u h => B.loopless.irrefl u.1 h.1⟩

/-- Sheet labels extending one specified map into the base. -/
abbrev Sheets {U V : Type*} {K : SimpleGraph U} {B : SimpleGraph V} (s : Signing V) (f : K →g B) :=
  {c : U → Bool // ∀ ⦃u v⦄, K.Adj u v → (c u ^^ c v) = s.neg (f u) (f v)}

def liftData {U V : Type*} (K : SimpleGraph U) (B : SimpleGraph V) (s : Signing V) :
    (K →g signedLift B s) ≃ Σ f : K →g B, Sheets s f where
  toFun h := ⟨⟨fun i => (h i).1, fun he => (h.map_adj he).1⟩,
    ⟨fun i => (h i).2, fun _ _ he => (h.map_adj he).2⟩⟩
  invFun x := ⟨fun i => (x.1 i, x.2.val i), fun h => ⟨x.1.map_adj h, x.2.property h⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem constant_on_walk {U : Type*} {K : SimpleGraph U} {c : U → Bool}
    (h : ∀ ⦃i j⦄, K.Adj i j → c i = c j) {i j : U} (p : K.Walk i j) : c i = c j := by
  induction p with
  | nil => rfl
  | cons e _ ih => exact (h e).trans ih

theorem xor_shift (a b t : Bool) : ((a ^^ t) ^^ (b ^^ t)) = (a ^^ b) := by decide +revert

theorem xor_differences (a b x y : Bool) : (a ^^ b) = (x ^^ y) → (a ^^ x) = (b ^^ y) := by
  decide +revert

theorem xor_recover (a b : Bool) : (a ^^ (a ^^ b)) = b := by decide +revert

/-- Once there is one lift, every other lift differs by one independent sheet
choice on each connected component of the pattern. -/
def sheetsEquiv {U V : Type*} {K : SimpleGraph U} {B : SimpleGraph V} {s : Signing V}
    {f : K →g B} (base : Sheets s f) : (K.ConnectedComponent → Bool) ≃ Sheets s f where
  toFun t := ⟨fun i => base.val i ^^ t (K.connectedComponentMk i), fun i j e => by
    dsimp only
    rw [SimpleGraph.ConnectedComponent.sound e.reachable, xor_shift, base.property e]⟩
  invFun d := ConnectedComponent.lift (fun i => base.val i ^^ d.val i) (fun _ _ p _ =>
    constant_on_walk (fun {i j} e => xor_differences _ _ _ _ ((base.property e).trans (d.property e).symm)) p)
  left_inv t := by
    funext c
    induction c using ConnectedComponent.ind with
    | h i => exact xor_recover ..
  right_inv d := by
    apply Subtype.ext
    funext i
    exact xor_recover ..

/-- The number of lifts of every base map is either zero or exactly two to the
number of connected components, including the unique lift of the empty pattern. -/
theorem sheet_count {U V : Type*} [Finite U] {K : SimpleGraph U} {B : SimpleGraph V}
    (s : Signing V) (f : K →g B) : Nat.card (Sheets s f) =
    (by classical exact if Nonempty (Sheets s f) then 2 ^ Nat.card K.ConnectedComponent else 0) := by
  classical
  split_ifs with hn
  · obtain ⟨c⟩ := hn
    rw [← Nat.card_congr (sheetsEquiv c), Nat.card_fun]
    simp
  · have : IsEmpty (Sheets s f) := not_nonempty_iff.mp hn
    simp

attribute [local instance] Fintype.ofFinite

theorem lift_hom_sum {U V : Type*} [Finite U] [Finite V] (K : SimpleGraph U) (B : SimpleGraph V)
    (s : Signing V) : homCount K (signedLift B s) = ∑ f : K →g B, Nat.card (Sheets s f) := by
  rw [homCount, Nat.card_congr (liftData K B s), Nat.card_sigma]

theorem lift_hom_le {U V : Type*} [Finite U] [Finite V] (K : SimpleGraph U) (B : SimpleGraph V)
    (s t : Signing V) (h : ∀ f : K →g B, Nonempty (Sheets s f)) :
    homCount K (signedLift B t) ≤ homCount K (signedLift B s) := by
  classical
  rw [lift_hom_sum, lift_hom_sum]
  apply Finset.sum_le_sum
  intro f _
  rw [sheet_count, sheet_count]
  split_ifs <;> simp_all

theorem lift_hom_lt {U V : Type*} [Finite U] [Finite V] (K : SimpleGraph U) (B : SimpleGraph V)
    (s t : Signing V) (h : ∀ f : K →g B, Nonempty (Sheets s f)) (f₀ : K →g B)
    (hn : ¬ Nonempty (Sheets t f₀)) : homCount K (signedLift B t) < homCount K (signedLift B s) := by
  classical
  rw [lift_hom_sum, lift_hom_sum]
  apply Finset.sum_lt_sum
  · intro f _
    rw [sheet_count, sheet_count]
    split_ifs <;> simp_all
  · refine ⟨f₀, by simp, ?_⟩
    rw [sheet_count, sheet_count]
    simp [h f₀, hn]

end JointForest
