module

public import SolvedProblems.DominationModel
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

namespace DominationVC

/-- The membership example has one side of points and one side of subsets. -/
inductive Host (d : ℕ) where
  | point (x : Fin d)
  | subset (s : Finset (Fin d))
  deriving DecidableEq, Fintype

namespace Host

variable {d : ℕ}

/-- The only strict comparisons go from a point to a set omitting it. -/
def below : Host d → Host d → Prop
  | .point x, .subset s => x ∉ s
  | _, _ => False

instance : PartialOrder (Host d) where
  le x y := x = y ∨ below x y
  le_refl _ := .inl rfl
  le_trans x y z h₁ h₂ := by
    rcases h₁ with rfl | h₁
    · exact h₂
    rcases h₂ with rfl | h₂
    · exact .inr h₁
    cases x <;> cases y <;> cases z <;> simp_all [below]
  le_antisymm x y h₁ h₂ := by
    rcases h₁ with rfl | h₁
    · rfl
    rcases h₂ with he | h₂
    · exact he.symm
    cases x <;> cases y <;> simp_all [below]

theorem lt_iff_below (x y : Host d) : x < y ↔ below x y := by
  change ((_ ∨ _) ∧ ¬(_ ∨ _)) ↔ _
  cases x <;> cases y <;> simp [below] <;> grind

def pointSide (d : ℕ) : Finset (Host d) := Finset.univ.image point

theorem point_card (d : ℕ) : (pointSide d).card = d := by
  rw [pointSide, Finset.card_image_of_injective _ (fun _ _ => Host.point.inj)]
  simp

theorem adjacency_point_subset (x : Fin d) (s : Finset (Fin d)) :
    (incomparability (Host d)).Adj (.point x) (.subset s) ↔ x ∈ s := by
  change (_ ≠ _ ∧ ¬_ < _ ∧ ¬_ < _) ↔ _
  simp [lt_iff_below, below]

/-- Every subset of the point side is exactly its trace on the neighborhood of
the corresponding subset vertex, including the empty trace. -/
theorem points_shattered (d : ℕ) :
    (closedFamily (incomparability (Host d))).Shatters (pointSide d) := by
  classical
  intro t ht
  let s : Finset (Fin d) := Finset.univ.filter fun x => point x ∈ t
  unfold closedFamily
  apply Exists.intro (Finset.univ.filter fun v => v = subset s ∨ (incomparability (Host d)).Adj (subset s) v)
  constructor
  · exact Finset.mem_image.mpr ⟨subset s, Finset.mem_univ _, rfl⟩
  · ext v
    cases v with
    | point x =>
      rw [Finset.mem_inter]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hin : point x ∈ pointSide d := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
      rw [((incomparability (Host d)).adj_comm (subset s) _), adjacency_point_subset]
      simp [hin, s]
    | subset u =>
      have hn : subset u ∉ pointSide d := by simp [pointSide]
      have ht' : subset u ∉ t := fun h => hn (ht h)
      simp [hn,ht']

def isPoint : Host d → Bool
  | .point _ => true
  | .subset _ => false

theorem same_side_adj {x y : Host d} (h : isPoint x = isPoint y) (hne : x ≠ y) :
    (incomparability (Host d)).Adj x y := by
  refine ⟨hne, ?_, ?_⟩ <;> cases x <;> cases y <;> simp_all [isPoint, lt_iff_below, below]

/-- A connected target clique forced into the point side has at most d vertices. -/
theorem point_capacity {n : ℕ} (f : Fin n → Host d) (hf : Function.Injective f)
    (hp : ∀ i, isPoint (f i) = true) : n ≤ d := by
  classical
  have hv (i : Fin n) : ∃ q, f i = point q := by
    cases h : f i with
    | point x => exact ⟨x,rfl⟩
    | subset s => simpa [h,isPoint] using hp i
  have hinj : Function.Injective (fun i => (hv i).choose) := by
    intro x y h
    apply hf
    rw [(hv x).choose_spec, (hv y).choose_spec]
    exact congrArg point h
  simpa using Fintype.card_le_of_injective _ hinj

theorem card_host (d : ℕ) : Fintype.card (Host d) = d + 2^d := by
  let e : Host d ≃ Fin d ⊕ Finset (Fin d) :=
    ⟨(fun x => match x with | point p => .inl p | subset s => .inr s), Sum.elim point subset,
     (fun x => by cases x <;> rfl), (fun x => by cases x <;> rfl)⟩
  simp [Fintype.card_congr e]

end Host
end DominationVC
