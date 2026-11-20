module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace BoundedJump

/-- A deterministic word automaton scanning from right to left. -/
structure Machine (α : Type) where
  State : Type
  finite : Fintype State
  eqState : DecidableEq State
  start : State
  step : α → State → State
  accept : State → Bool

def Machine.accepts (M : Machine α) (w : List α) : Bool :=
  M.accept (w.foldr M.step M.start)


/-- None denotes the final value. A right/left offset has magnitude k + 1. -/
abbrev Letter (m : Nat) := Option (Bool × Fin m)

/-- The pattern entries are visited in position order. Each new value goes
above or below each earlier one according to the pattern's ranks. -/
def OccursFrom (r : Fin n → Fin n → Prop) :
    List Nat → List (Nat × Fin n) → Prop
  | [], _ => True
  | a :: rest, prev => ∃ j, (∀ u ∈ prev, r u.2 j ∧
      (if u.1 < a then u.2 < j else if a < u.1 then j < u.2 else False)) ∧
      OccursFrom r rest ((a,j) :: prev)

def Avoid (B : List (List Nat)) (r : Fin n → Fin n → Prop) :=
  ∀ p ∈ B, ¬OccursFrom r p []

def Counted (m : Nat) (B : List (List Nat)) {n : Nat} (p : Equiv.Perm (Fin n)) : Prop :=
  (∀ i j, (p i).val+1 = (p j).val → Nat.dist i.val j.val ≤ m) ∧
    Avoid B (fun i j => p i < p j)


/-- Number of accepted words of length n when the rightmost letter is read from q. -/
def Machine.wordCount {α : Type} [Fintype α] (M : Machine α) (n : Nat) (q : M.State) : Nat :=
  (Finset.univ.filter (fun w : Fin n → α => M.accept ((List.ofFn w).foldr M.step q) = true)).card


/-- Coefficients of the draft's series, including its empty-permutation convention. -/
noncomputable def permutationCount (m : Nat) (B : List (List Nat)) (n : Nat) : Nat := by
  classical
  exact if n = 0 then 1 else Fintype.card {p : Equiv.Perm (Fin n) // Counted m B p}

/-- A finite denominator with constant coefficient one and a finite numerator;
the convolution is the coefficient identity for their quotient. -/
def RationalCounts (a : Nat → Nat) : Prop :=
  ∃ (d : Nat) (den num : Nat → ℤ), den 0 = 1 ∧
    (∀ i > d, den i = 0 ∧ num i = 0) ∧
    ∀ n, (∑ i ∈ Finset.range (n+1), den i * (a (n-i) : ℤ)) = num n

/-- The table counts accepted words from every state. Each of the n updates
sums over a fixed alphabet. Every partial sum fits in A*n+1 bits. -/
def TableBounds (M : Machine (Letter m)) : Prop :=
  (∀ q, M.wordCount 0 q = if M.accept q then 1 else 0) ∧
  (∀ n q, M.wordCount (n+1) q = ∑ a : Letter m, M.wordCount n (M.step a q)) ∧
  ∀ n : Nat, let A := Fintype.card (Letter m)
             let S := M.finite.elems.card
             (∑ _t ∈ Finset.range n, ∑ _q ∈ M.finite.elems, A) = n*S*A ∧
             (∀ t < n, ∀ (q : M.State) (U : Finset (Letter m)),
               (∑ a ∈ U, M.wordCount t (M.step a q)) < 2^(A*n+1)) ∧
             (n*S*A)*(A*n+1) ≤ (S*(A+1)^2)*(n+1)^2

/-- A single construction works uniformly in the jump bound and forbidden patterns. -/
def Enumeration (m : Nat) (B : List (List Nat)) (M : Machine (Letter m)) : Prop :=
  (∀ n, Nonempty ({w : Fin n → Letter m // M.accepts (List.ofFn w) = true} ≃
                    {p : Equiv.Perm (Fin n) // Counted m B p})) ∧
  (∀ n, 0 < n → M.wordCount n M.start = permutationCount m B n) ∧
  RationalCounts (permutationCount m B) ∧ TableBounds M

/-- Zero-based classical patterns of length at most k use only ranks below k. -/
def Fits (k : Nat) (B : List (List Nat)) : Prop :=
  ∀ p ∈ B, p.length ≤ k ∧ ∀ v ∈ p, v < k

/-- For every jump bound and finite set of classical forbidden patterns, construct
a deterministic automaton in bijection with the restricted permutations. Its state
bound depends only on the jump bound and maximum pattern length. -/
theorem finiteEnumeration :
    ∃ (build : (m k : Nat) → List (List Nat) → Machine (Letter m)) (bound : Nat → Nat → Nat),
      ∀ m k B, Fits k B → Enumeration m B (build m k B) ∧
        (build m k B).finite.elems.card ≤ bound m k := by sorry

end BoundedJump
