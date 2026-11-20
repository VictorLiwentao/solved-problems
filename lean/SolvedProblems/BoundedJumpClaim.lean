module

public import SolvedProblems.BoundedJumpRelations
public import SolvedProblems.BoundedJumpCountModel
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace BoundedJump

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

end BoundedJump
