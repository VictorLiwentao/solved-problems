module

public import SolvedProblems.ClosureSupportModel
import SolvedProblems.ClosureSupportField
import SolvedProblems.ClosureSupportPerm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.Order

public section

namespace ClosureSupport

private theorem fixes_union {P Q : Support} {g : Equiv.Perm ℕ} :
    Fixes (P ++ Q) g ↔ Fixes P g ∧ Fixes Q g := by
  constructor
  · intro h
    exact ⟨fun S hs => h S (List.mem_append.mpr (.inl hs)),
      fun S hs => h S (List.mem_append.mpr (.inr hs))⟩
  · rintro ⟨h,k⟩ S hs
    exact (List.mem_append.mp hs).elim (h S) (k S)

private theorem coefficients_supported {K : Type u} [Field K] (A : Presentation K)
    (p : Polynomial K) : InternalPolynomial A p := by
  classical
  have finite (ns : List ℕ) : ∃ Q : Support, ∀ g : stabilizer A.domainSupport,
      Fixes Q g.val → ∀ n ∈ ns, A.act g (p.coeff n) = p.coeff n := by
    induction ns with
    | nil => exact ⟨[],fun _ _ _ h => False.elim (List.not_mem_nil h)⟩
    | cons n ns ih =>
      obtain ⟨P,hP⟩ := A.localSupport (p.coeff n)
      obtain ⟨Q,hQ⟩ := ih
      refine ⟨P ++ Q, fun g hg a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hP g (fixes_union.mp hg).1
      · exact hQ g (fixes_union.mp hg).2 a ha
  obtain ⟨Q,hQ⟩ := finite p.support.toList
  refine ⟨Q,fun g hg n => ?_⟩
  by_cases h : p.coeff n = 0
  · simp [h]
  · exact hQ g hg n (Finset.mem_toList.mpr (Polynomial.mem_support_iff.mpr h))

private theorem internally_closed_iff {K : Type u} [Field K] (A : Presentation K) :
    InternallyClosed A ↔ IsAlgClosed K :=
  ⟨fun h => ⟨fun p => h p (coefficients_supported A p)⟩,
    fun h p _ => @IsAlgClosed.splits K _ h p⟩

private def Uniform {K : Type u} [Field K] (A : Presentation K) : Prop :=
  ∃ Q : Support, ∀ g : stabilizer A.domainSupport, Fixes Q g.val → ∀ x, A.act g x = x

private theorem order_iff {K : Type u} [Field K] (A : Presentation K) :
    WellOrderable A ↔ Uniform A := by
  constructor
  · rintro ⟨r,well,Q,hr⟩
    let : IsWellOrder K r := well
    refine ⟨Q, fun g hg x => ?_⟩
    let e : r ≃r r := { toEquiv := (A.act g).toEquiv, map_rel_iff' := hr g hg _ _ }
    exact (InitialSeg.refl r).eq_relIso e x
  · rintro ⟨Q,fix⟩
    exact ⟨WellOrderingRel, inferInstance, Q, fun g hg x y => by rw [fix g hg x, fix g hg y]⟩

/-- An action must fix all elements after supporting the chosen square root of -1. -/
private theorem closure_uniform {K : Type u} [Field K] [IsAlgClosed K] (A : Presentation K) :
    Uniform A := by
  obtain ⟨i,hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1:K) (by decide : 0 < 2)
  obtain ⟨Q,hQ⟩ := A.localSupport i
  refine ⟨Q, fun g hg x => ?_⟩
  let H := stabilizer (A.domainSupport ++ Q)
  have inc : H ≤ stabilizer A.domainSupport := fun _ h => (fixes_union.mp h).1
  let restrict := Subgroup.inclusion inc
  let p : H := ⟨g.val, fixes_union.mpr ⟨g.property,hg⟩⟩
  obtain ⟨a,b,ha,hb,hab⟩ := factors (A.domainSupport ++ Q) p
  have each (v : H) (sq : v*v = 1) (z : K) : A.act (restrict v) z = z := by
    apply fixed_by_involution (A.act (restrict v)) _ i hi _ z
    · intro t
      have eq := congrArg (fun h : H => A.act (restrict h) t) sq
      simpa [map_mul] using eq
    · exact hQ _ (fixes_union.mp v.property).2
  change A.act (restrict p) x = x
  rw [hab, map_mul, map_mul]
  change A.act (restrict a) (A.act (restrict b) x) = x
  rw [each b hb, each a ha]

private theorem inherit_uniform {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : Presentation K) (B : Presentation L) (map : InternalMap A B (algebraMap K L))
    (hB : Uniform B) : Uniform A := by
  obtain ⟨Q,hm⟩ := map
  obtain ⟨R,hr⟩ := hB
  refine ⟨B.domainSupport ++ Q ++ R, fun g hg x => ?_⟩
  obtain ⟨hBQ,hR⟩ := fixes_union.mp hg
  obtain ⟨hB,hQ⟩ := fixes_union.mp hBQ
  apply (algebraMap K L).injective
  rw [← hm g.val g.property hB hQ x, hr ⟨g.val,hB⟩ hR _]

private def purePresentation (K : Type u) [Field K] : Presentation K where
  domainSupport := []
  act := 1
  localSupport _ := ⟨[],fun _ _ => rfl⟩

private theorem existence {K : Type u} [Field K] (A : Presentation K) :
    HasInternalClosure A ↔ WellOrderable A := by
  constructor
  · rintro ⟨L, field, alg, cl, B, map⟩
    let : Field L := field
    let : Algebra K L := alg
    let : IsAlgClosure K L := cl
    let : IsAlgClosed L := IsAlgClosure.isAlgClosed K
    exact (order_iff A).mpr (inherit_uniform A B map (closure_uniform B))
  · intro h
    obtain ⟨Q,hQ⟩ := (order_iff A).mp h
    refine ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance,
      purePresentation _, Q, fun g ha _ hq x => ?_⟩
    rw [hQ ⟨g,ha⟩ hq x]
    rfl

private theorem uniform_map {K : Type u} {L : Type v} [Field K] [Field L] (A : Presentation K)
    (B : Presentation L) (f : K → L) (ha : Uniform A) (hb : Uniform B) :
    InternalMap A B f := by
  obtain ⟨P,hP⟩ := ha
  obtain ⟨Q,hQ⟩ := hb
  refine ⟨P ++ Q, fun g a b h x => ?_⟩
  rw [hP ⟨g,a⟩ (fixes_union.mp h).1, hQ ⟨g,b⟩ (fixes_union.mp h).2]

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
  refine ⟨internally_closed_iff A, fun h =>
    (order_iff A).mpr (@closure_uniform _ _ ((internally_closed_iff A).mp h) A), existence A, ?_⟩
  intro L M _ _ _ _ hl hm B C _ _
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let : IsAlgClosed M := IsAlgClosure.isAlgClosed K
  exact ⟨IsAlgClosure.equiv K L M, uniform_map B C _ (closure_uniform B) (closure_uniform C)⟩

end ClosureSupport
