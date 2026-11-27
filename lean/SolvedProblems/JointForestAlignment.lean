module

public import SolvedProblems.JointForestResponse
public import SolvedProblems.JointForestLoss

@[expose] public section

namespace JointForest

open SimpleGraph

/-- A pairwise sheet exchange can vary with the ordered pair, while retaining
both resistance and adjacency on that same exchange. -/
structure Alignment {V : Type*} (B : SimpleGraph V) (s t : Signing V) (S T : V → V → ℚ) where
  flip : V → V → Bool
  diag : ∀ u, flip u u = false
  symm : ∀ u v, flip u v = flip v u
  edge : ∀ u v, B.Adj u v → t.neg u v = (s.neg u v ^^ flip u v)
  green : ∀ u v, T u v = polarity (flip u v) * S u v

/-- The new apex forces every proper nonedge to have distance two. -/
theorem cone_distance {V : Type*} (G : SimpleGraph V) (x y : Option V) : (cone G).dist x y =
    (by classical exact if x = y then 0 else if (cone G).Adj x y then 1 else 2) := by
  classical
  split_ifs with he ha
  · exact (cone_connected G).dist_eq_zero_iff.mpr he
  · exact (cone G).dist_eq_one_iff_adj.mpr ha
  · have hz := (cone_connected G).dist_eq_zero_iff.not.mpr he
    have ho := (cone G).dist_eq_one_iff_adj.not.mpr ha
    have hle := cone_dist_le_two G x y
    omega

theorem sheetGreen_aligned {V : Type*} {B : SimpleGraph V} {s t : Signing V} {S T : V → V → ℚ}
    (al : Alignment B s t S T) (P : V → V → ℚ) (u v : V) (a b c d : Bool)
    (h : (a ^^ b) = ((c ^^ d) ^^ al.flip u v)) :
    sheetGreen P S (u,a) (v,b) = sheetGreen P T (u,c) (v,d) := by
  have hq := congrArg polarity h
  simp only [polarity_xor] at hq
  simp only [sheetGreen, al.green u v, hq]
  ring

def forgetSheet {V : Type*} : Option (V × Bool) → Option V := Option.map Prod.fst

/-- Match the target sheets in each fiber independently. -/
def flipSheets {V : Type*} (k : V → Bool) : Option (V × Bool) ≃ Option (V × Bool) :=
  let bit (v : V) : Bool ≃ Bool :=
    { toFun := fun b => b ^^ k v
      invFun := fun b => b ^^ k v
      left_inv := fun b => by cases b <;> cases k v <;> rfl
      right_inv := fun b => by cases b <;> cases k v <;> rfl }
  (Equiv.prodShear (Equiv.refl V) bit).optionCongr

@[simp] theorem flipSheets_none {V : Type*} (k : V → Bool) : flipSheets k none = none := rfl

@[simp] theorem flipSheets_some {V : Type*} (k : V → Bool) (u : V) (e : Bool) :
    flipSheets k (some (u,e)) = some (u,e ^^ k u) := rfl

theorem flipSheets_forget {V : Type*} (k : V → Bool) (x : Option (V × Bool)) :
    forgetSheet (flipSheets k x) = forgetSheet x := by cases x <;> rfl

theorem fiber_equivalent {V : Type*} [Fintype V] (a b : Option (V × Bool) → Option (V × Bool) → ℕ × ℚ)
    (rows : ∀ x x', forgetSheet x = forgetSheet x' → ∃ k : V → Bool,
      ∀ y, a x y = b x' (flipSheets k y)) : Equivalent a b := by
  have hc (n : ℕ) : ∀ x x', forgetSheet x = forgetSheet x' → color a n x = color b n x' := by
    induction n with
    | zero => exact fun _ _ _ => rfl
    | succ n ih =>
      intro x x' hx
      obtain ⟨k, hk⟩ := rows x x' hx
      let e := flipSheets k
      have h (y : Option (V × Bool)) : ((a x y).1, (a x y).2, color a n y) =
        ((b x' (e y)).1, (b x' (e y)).2, color b n (e y)) := by
        rw [hk, ih y (e y) (flipSheets_forget k y).symm]
      change Finset.univ.val.map (fun y => ((a x y).1, (a x y).2, color a n y)) = _
      simp_rw [h]
      have he := congrArg (Multiset.map (fun y => ((b x' y).1, (b x' y).2, color b n y))) (Multiset.map_univ_val_equiv e)
      simpa only [Multiset.map_map, Function.comp_def, color] using he
  intro n
  simp_rw [show color a n = color b n from funext (fun x => hc n x x rfl)]

/-- An alignment of the signed Green entries lifts to equality of all rounds
of the actual joint shortest-path and unit-resistance refinement on the cones. -/
theorem cones_equivalent {V : Type*} [Fintype V] (B : SimpleGraph V) (s t : Signing V)
    (S T : V → V → ℚ) (hS : ∀ a x, signedShift B s (S a) x = pulse x a)
    (hT : ∀ a x, signedShift B t (T a) x = pulse x a) (al : Alignment B s t S T) :
    Equivalent (jointLabels (cone (signedLift B s))) (jointLabels (cone (signedLift B t))) := by
  classical
  obtain ⟨P,hP⟩ := unsigned_green_exists B
  let gs := sheetGreen P S
  let gt := sheetGreen P T
  have rs := cone_resistance_of_green (signedLift B s) gs (sheetGreen_solve B s P S hP hS)
  have rt := cone_resistance_of_green (signedLift B t) gt (sheetGreen_solve B t P T hP hT)
  have diag (u : V) (a b : Bool) : gs (u,a) (u,a) = gt (u,b) (u,b) :=
    sheetGreen_aligned al P u u a a b b (by simp [al.diag])
  apply fiber_equivalent
  intro x x' hx
  cases x with
  | none =>
    cases x' with
    | some v => cases hx
    | none =>
      refine ⟨fun _ => false, ?_⟩
      intro y
      cases y with
      | none => simp [jointLabels, resistance]
      | some z =>
        obtain ⟨v,e⟩ := z
        simp only [flipSheets_some, Bool.xor_false]
        apply Prod.ext
        · change (cone (signedLift B s)).dist none (some (v,e)) = (cone (signedLift B t)).dist none (some (v,e))
          rw [cone_distance, cone_distance]; simp [cone]
        · change resistance _ none (some (v,e)) = resistance _ none (some (v,e))
          rw [rs, rt]; simpa only [coneGreen, sub_zero, zero_sub, sub_neg_eq_add, zero_add, zero_sub_zero] using diag _ _ _
  | some u =>
    obtain ⟨u, a⟩ := u
    cases x' with
    | none => cases hx
    | some v =>
      obtain ⟨u', b⟩ := v
      have hu : u = u' := Option.some.inj hx
      subst u'
      let k (v : V) := ((a ^^ b) ^^ al.flip u v)
      refine ⟨k, ?_⟩
      intro y
      cases y with
      | none =>
        apply Prod.ext
        · rw [show flipSheets k none = none from rfl]
          change (cone (signedLift B s)).dist _ none = (cone (signedLift B t)).dist _ none
          rw [cone_distance, cone_distance]; simp [cone]
        · change resistance _ (some (u,a)) none = resistance _ (some (u,b)) none
          rw [rs, rt]; simpa only [coneGreen, sub_zero, sub_self] using diag u a b
      | some z =>
        obtain ⟨v,c⟩ := z
        let d := c ^^ k v
        have hab : (a ^^ c) = ((b ^^ d) ^^ al.flip u v) := by
          dsimp [d,k]; cases a <;> cases b <;> cases c <;> cases al.flip u v <;> rfl
        have hba : (c ^^ a) = ((d ^^ b) ^^ al.flip v u) := by
          simpa only [Bool.xor_comm c a, Bool.xor_comm d b, al.symm v u] using hab
        have heq : (some (u,a)) = some (v,c) ↔ (some (u,b)) = some (v,d) := by
          by_cases hu : u = v
          · subst v
            simp only [Option.some.injEq, Prod.mk.injEq, true_and] at *
            dsimp [d,k]; rw [al.diag]; cases a <;> cases b <;> cases c <;> decide
          · simp [hu]
        have hed : (cone (signedLift B s)).Adj (some (u,a)) (some (v,c)) ↔
            (cone (signedLift B t)).Adj (some (u,b)) (some (v,d)) := by
          change (B.Adj u v ∧ (a ^^ c) = _) ↔ (B.Adj u v ∧ (b ^^ d) = _)
          by_cases he : B.Adj u v
          · rw [al.edge u v he, hab]
            simp only [he, true_and]
            cases b <;> cases d <;> cases s.neg u v <;> cases al.flip u v <;> decide
          · simp [he]
        apply Prod.ext
        · change (cone (signedLift B s)).dist (some (u,a)) (some (v,c)) =
            (cone (signedLift B t)).dist (some (u,b)) (some (v,d))
          rw [cone_distance, cone_distance]
          split_ifs <;> simp_all
        · change resistance _ (some (u,a)) (some (v,c)) = resistance _ (some (u,b)) (some (v,d))
          rw [rs, rt]
          simp only [coneGreen]
          have huv : gs (u,a) (v,c) = gt (u,b) (v,d) := sheetGreen_aligned al P u v a c b d hab
          have hvu : gs (v,c) (u,a) = gt (v,d) (u,b) := sheetGreen_aligned al P v u c a d b hba
          rw [diag u a b, diag v c d, huv, hvu]

end JointForest
