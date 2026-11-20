module

public import SolvedProblems.ClosureSupportAtoms
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Order.WellFounded

@[expose] public section

namespace ClosureSupport

/-- An internal field may move under arbitrary permutations of atoms. After supporting its
domain and operations by P, its stabilizer acts by field automorphisms. Every element of the
field has its own finite support. -/
structure Presentation (K : Type u) [Field K] where
  domainSupport : Support
  act : stabilizer domainSupport →* (K ≃+* K)
  localSupport : ∀ x : K, ∃ Q : Support, ∀ g : stabilizer domainSupport,
    Fixes Q g.val → act g x = x

/-- A polynomial is an internal object if one partition fixes all its coefficients. -/
def InternalPolynomial {K : Type u} [Field K] (A : Presentation K) (p : Polynomial K) : Prop :=
  ∃ Q : Support, ∀ g : stabilizer A.domainSupport, Fixes Q g.val →
    ∀ n, A.act g (p.coeff n) = p.coeff n

def InternallyClosed {K : Type u} [Field K] (A : Presentation K) : Prop :=
  ∀ p : Polynomial K, InternalPolynomial A p → p.Splits

/-- A well-order is internal if some finite partition supports the relation itself. -/
def WellOrderable {K : Type u} [Field K] (A : Presentation K) : Prop :=
  ∃ (r : K → K → Prop) (_ : IsWellOrder K r) (Q : Support),
    ∀ g : stabilizer A.domainSupport, Fixes Q g.val → ∀ x y, r (A.act g x) (A.act g y) ↔ r x y

/-- The graph of a map has a finite support after including both field-structure supports. -/
def InternalMap {K : Type u} {L : Type v} [Field K] [Field L] (A : Presentation K)
    (B : Presentation L) (f : K → L) : Prop :=
  ∃ Q : Support, ∀ (g : Equiv.Perm ℕ) (ha : g ∈ stabilizer A.domainSupport)
    (hb : g ∈ stabilizer B.domainSupport), Fixes Q g →
      ∀ x, B.act ⟨g,hb⟩ (f x) = f (A.act ⟨g,ha⟩ x)

def HasInternalClosure {K : Type u} [Field K] (A : Presentation K) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsAlgClosure K L)
    (B : Presentation L), InternalMap A B (algebraMap K L)

end ClosureSupport
