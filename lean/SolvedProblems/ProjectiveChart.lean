module

public import SolvedProblems.ProjectiveExtraction
public import SolvedProblems.ProjectiveBlockGeometry
import SolvedProblems.ProjectiveCodeMatch

public section

namespace ProjectiveIndiscernibles

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveAlgebraic ProjectiveTransfer Set Function

variable {L : Language} {M : Type*} [L.Structure M] {d : ℕ} {κ I : Type}

private theorem coord_eq {J : Type*} {x y : J → M} (m : tupleType L x = tupleType L y) (i j : J) :
    x i = x j ↔ y i = y j := by
  have h := Set.ext_iff.mp m ((Term.var i).equal (Term.var j))
  exact Formula.realize_equal.symm.trans (h.trans Formula.realize_equal)

private theorem based_many {core : κ → M} {R : ℕ → Fin d → M} {B : ℚ → Fin d → M}
    (base : BasedOn L core R B) {J : Type} [Finite J] (p : J → ℚ) (hp : Injective p) :
    ∃ t : J → ℕ, Injective t ∧ Matched L core (B ∘ p) (R ∘ t) := by
  classical
  let := Fintype.ofFinite J
  let e := Fintype.equivFin J
  obtain ⟨u,inj,mu⟩ := base (p ∘ e.symm) (hp.comp e.symm.injective)
  refine ⟨u ∘ e,inj.comp e.injective,?_⟩
  have eq := restrict_match mu e
  simpa only [Function.comp_assoc,_root_.Equiv.symm_comp_self,Function.comp_id] using eq

private theorem local_inj {core : κ → M} {R : ℕ → Fin d → M} {B : ℚ → Fin d → M}
    (chart : BlockChart L core R) (base : BasedOn L core R B) {J : Type} [Finite J] (p : J → ℚ) (hp : Injective p) :
    Injective (layout core (B ∘ p)) := by
  obtain ⟨u,inj,h⟩ := based_many base p hp
  intro i j eq
  have r := (coord_eq h i j).mp eq
  let incl : κ ⊕ (J × Fin d) → κ ⊕ (ℕ × Fin d) := Sum.map id (Prod.map u id)
  have cut (i) : layout core (R ∘ u) i = layout core R (incl i) := by cases i <;> rfl
  rw [cut,cut] at r
  have same := chart.disjoint r
  rcases i with i|⟨i,a⟩ <;> rcases j with j|⟨j,b⟩ <;> simp_all [incl,inj.eq_iff]

private theorem full_inj {core : κ → M} {R : ℕ → Fin d → M} {B : ℚ → Fin d → M}
    (chart : BlockChart L core R) (base : BasedOn L core R B) : Injective (layout core B) := by
  classical
  intro i j eq
  let tag : κ ⊕ (ℚ × Fin d) → ℚ := Sum.elim (fun _ => 0) Prod.fst
  let S : Finset ℚ := {tag i,tag j}
  let pack (p : κ ⊕ (ℚ × Fin d)) (hp : tag p ∈ S) : κ ⊕ (S × Fin d) := match p with
    | .inl a => .inl a
    | .inr (t,b) => .inr (⟨t,hp⟩,b)
  let incl : κ ⊕ (S × Fin d) → κ ⊕ (ℚ × Fin d) := Sum.map id (Prod.map Subtype.val id)
  have back (p hp) : incl (pack p hp) = p := by cases p <;> rfl
  have val (p hp) : layout core (B ∘ (Subtype.val : S → ℚ)) (pack p hp) = layout core B p := by cases p <;> rfl
  have mi : tag i ∈ S := by simp [S]
  have mj : tag j ∈ S := by simp [S]
  have h := local_inj chart base (Subtype.val : S → ℚ) Subtype.val_injective ((val i mi).trans (eq.trans (val j mj).symm))
  exact (back i mi).symm.trans ((congrArg incl h).trans (back j mj))

/-- Pointwise type matching transfers the fact that the displayed block
exhausts the singleton closure off the core, including all possible additional
ambient elements outside the displayed points. -/
theorem inherit_chart [Finite κ] (fin : FiniteTypes L M) {core : κ → M} {R : ℕ → Fin d → M}
    {B : ℚ → Fin d → M} (chart : BlockChart L core R) (base : BasedOn L core R B) : BlockChart L core B := by
  refine ⟨chart.core_exact,full_inj chart base,?_⟩
  intro t j
  let p (_ : Unit) := t
  obtain ⟨u,_,mat⟩ := based_many base p (fun i l _ => Subsingleton.elim i l)
  let X := layout core (B ∘ p)
  let Y := layout core (R ∘ u)
  ext x
  obtain ⟨v,joint⟩ := extendTuple L (Eq.refl _) (fin ((κ ⊕ (Unit × Fin d)) ⊕ Unit)) mat (fun _ : Unit => x)
  have m : tupleType L (point X x) = tupleType L (point Y (v ())) := by
    have eq : (fun _ : Unit => v ()) = v := funext fun z => by cases z; rfl
    simpa [point,eq,X,Y] using joint
  let idx := Sum.inr ((),j) (α := κ)
  let keep : Unit ⊕ Unit → (κ ⊕ (Unit × Fin d)) ⊕ Unit := Sum.map (fun _ => idx) id
  have cut (y : κ ⊕ (Unit × Fin d) → M) (z : M) : point y z ∘ keep = point (fun _ : Unit => y idx) z := by
    funext i; cases i <;> rfl
  have sub := match_subtuple m keep
  rw [cut,cut] at sub
  have alg := algebraic_match fin sub
  have one (a : M) : tupleClosure L (fun _ : Unit => a) = acl L {a} := by rw [← acl_range]; simp
  rw [one,one] at alg
  change x ∈ acl L {B t j} ↔ v () ∈ acl L {R (u ()) j} at alg
  rw [chart.singleton_exact _ _] at alg
  have coord (i : κ ⊕ (Unit × Fin d)) : X i = x ↔ Y i = v () := coord_eq m (.inl i) (.inr ())
  refine alg.trans ⟨?_,?_⟩
  · rintro (⟨a,h⟩ | ⟨l,h⟩)
    · exact Or.inl ⟨a,(coord (.inl a)).mpr h⟩
    · exact Or.inr ⟨l,(coord (.inr ((),l))).mpr h⟩
  · rintro (⟨a,h⟩ | ⟨l,h⟩)
    · exact Or.inl ⟨a,(coord (.inl a)).mp h⟩
    · exact Or.inr ⟨l,(coord (.inr ((),l))).mp h⟩

/-- The core together with any collection of whole blocks is algebraically
closed when the pregeometry is degenerate. -/
theorem chart_closed (fin : FiniteTypes L M) (deg : Degenerate L M) {core : κ → M}
    {B : I → Fin d → M} (chart : BlockChart L core B) {J : Type} (p : J → I) :
    acl L (Set.range (layout core (B ∘ p))) = Set.range (layout core (B ∘ p)) := by
  have cores : Set.range core ⊆ Set.range (layout core (B ∘ p)) := by
    rintro _ ⟨c,rfl⟩; exact ⟨.inl c,rfl⟩
  apply closed_of_singletons deg _ (chart.core_exact ▸ cores)
  rintro _ ⟨i,rfl⟩
  rcases i with c|⟨i,j⟩
  · have h : core c ∈ acl L (∅ : Set M) := chart.core_exact.subset (Set.mem_range_self c)
    have sub := (acl_mono (L := L) (Set.singleton_subset_iff.mpr h)).trans (acl_idempotent fin ∅).subset
    exact sub.trans (chart.core_exact ▸ cores)
  · change acl L {B (p i) j} ⊆ _
    rw [chart.singleton_exact]
    refine Set.union_subset cores ?_
    rintro _ ⟨k,rfl⟩; exact ⟨.inr (i,k),rfl⟩

/-- A new block's point is generic over any finitely many other blocks. -/
theorem chart_independent [Finite κ] (fin : FiniteTypes L M) (deg : Degenerate L M) {core : κ → M}
    {B : ℚ → Fin d → M} (chart : BlockChart L core B) (i₀ : Fin d) : IndependentBlocks L core B i₀ := by
  intro ι _ m t fresh member
  have inside : B t i₀ ∈ Set.range (layout core (B ∘ m)) :=
    (chart_closed fin deg chart m).subset ((acl_range (L := L) (marked core B m)).superset member)
  obtain ⟨j,h⟩ := inside
  rcases j with c|⟨i,l⟩
  · have same := chart.disjoint (a₁ := Sum.inl c) (a₂ := Sum.inr (t,i₀)) h
    cases same
  · have same := chart.disjoint (a₁ := Sum.inr (m i,l)) (a₂ := Sum.inr (t,i₀)) h
    exact fresh ⟨i,congrArg Prod.fst (Sum.inr.inj same)⟩

theorem chart_algebraic {core : κ → M} {B : ℚ → Fin d → M} (chart : BlockChart L core B)
    (i₀ : Fin d) : AlgebraicBlocks L B i₀ := by
  intro t j
  have one : tupleClosure L (fun _ : Unit => B t i₀) = acl L {B t i₀} := by rw [← acl_range]; simp
  rw [one,chart.singleton_exact]
  exact Or.inr (Set.mem_range_self j)

end ProjectiveIndiscernibles
