module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Order.WellFounded

@[expose] public section

namespace ClosureSupport

/-- Membership in finitely many subsets gives the cells of a finite partition of the atoms. -/
abbrev Support := List (Set ℕ)

def Fixes (P : Support) (g : Equiv.Perm ℕ) : Prop :=
  ∀ S ∈ P, ∀ x, g x ∈ S ↔ x ∈ S

def stabilizer (P : Support) : Subgroup (Equiv.Perm ℕ) where
  carrier := {g | Fixes P g}
  one_mem' := fun _ _ _ => Iff.rfl
  mul_mem' ha hb := fun _ h x => (ha _ h _).trans (hb _ h x)
  inv_mem' {g} hg := fun S hs x => by simpa using (hg S hs (g.symm x)).symm

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

/-- In Bruce's finite partition model every algebraically closed field is internally
well-orderable. An internal field has an internal algebraic closure exactly when
well-orderable, and any two internal closures admit an internal base-field isomorphism. -/
theorem closureClassification {K : Type u} [Field K] (A : Presentation K) :
    (InternallyClosed A ↔ IsAlgClosed K) ∧ (InternallyClosed A → WellOrderable A) ∧
    (HasInternalClosure A ↔ WellOrderable A) ∧
    ∀ (L : Type v) (M : Type w) [Field L] [Field M] [Algebra K L] [Algebra K M]
      [IsAlgClosure K L] [IsAlgClosure K M] (B : Presentation L) (C : Presentation M),
      InternalMap A B (algebraMap K L) → InternalMap A C (algebraMap K M) →
      ∃ e : L ≃ₐ[K] M, InternalMap B C e := by
  sorry

end ClosureSupport
