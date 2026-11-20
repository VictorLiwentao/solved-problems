module

public import SolvedProblems.BoundedJumpClaim
public import SolvedProblems.BoundedJumpPatterns

@[expose] public section

namespace BoundedJump

/-- Enumerate all rank words of a fixed length. -/
def rankWords (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | l+1 => (List.range k).flatMap fun v => (rankWords k l).map (v :: ·)

theorem rankWords_complete (p : List Nat) (h : ∀ v ∈ p, v < k) : p ∈ rankWords k p.length := by
  induction p with
  | nil => simp [rankWords]
  | cons a as ih =>
    simp only [List.length_cons,rankWords,List.mem_flatMap,List.mem_map,List.mem_range]
    exact ⟨a,h a (by simp),as,ih (fun v hv => h v (by simp [hv])),rfl⟩

def candidates (k : Nat) := (List.range (k+1)).flatMap (rankWords k)

def basis (k : Nat) (B : List (List Nat)) := (candidates k).filter (fun p => decide (p ∈ B))

theorem mem_basis (h : Fits k B) (p : List Nat) : p ∈ basis k B ↔ p ∈ B := by
  simp only [basis,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
  intro hp
  obtain ⟨hl,hv⟩ := h p hp
  exact List.mem_flatMap.mpr ⟨p.length, List.mem_range.mpr (by omega),rankWords_complete _ hv⟩

/-- The compiler first canonicalizes the supplied forbidden family, so duplicating
or reordering its list cannot change the machine or its size. -/
def fromBasis (m : Nat) (B : List (List Nat)) : Machine (Letter m) :=
  ((Formula.validF id).conj (Formula.avoidF id B)).compile

def machine (m k : Nat) (B : List (List Nat)) := fromBasis m (basis k B)

theorem machine_spec (h : Fits k B) (w : Fin n → Letter m) :
    (machine m k B).accepts (List.ofFn w) = true ↔ Valid w ∧ Avoid B (Strict w) := by
  change ((Formula.validF id).conj (Formula.avoidF id (basis k B))).compile.accept
    (((Formula.validF id).conj (Formula.avoidF id (basis k B))).compile.run w) = true ↔ _
  rw [Formula.compile_spec]
  simp only [Formula.Holds,Formula.validF_spec,Formula.avoidF_spec,id_eq,Avoid,mem_basis h]

/-- Maximum of f over all subsequences of the finite candidate list. -/
def subBound : List A → (List A → Nat) → Nat
  | [], f => f []
  | x::xs, f => max (subBound xs f) (subBound xs fun ys => f (x :: ys))

theorem filter_le_subBound (p : A → Bool) (xs : List A) (f : List A → Nat) :
    f (xs.filter p) ≤ subBound xs f := by
  induction xs generalizing f with
  | nil => exact le_rfl
  | cons x xs ih =>
    cases h : p x
    · simpa [List.filter_cons,h,subBound] using (le_trans (ih f)
        (le_max_left (subBound xs f) (subBound xs (fun ys => f (x::ys)))))
    · simpa [List.filter_cons,h,subBound] using (le_trans (ih (fun ys => f (x::ys)))
        (le_max_right (subBound xs f) (subBound xs (fun ys => f (x::ys)))))

def stateBound (m k : Nat) := subBound (candidates k) (fun l => (fromBasis m l).finite.elems.card)

theorem machine_size (m k : Nat) (B : List (List Nat)) :
    (machine m k B).finite.elems.card ≤ stateBound m k :=
  filter_le_subBound (fun p : List Nat => decide (p ∈ B)) (candidates k)
    (fun l => (fromBasis m l).finite.elems.card)

end BoundedJump
