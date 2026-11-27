module

public import SolvedProblems.OrdinalCubeRefine
public import SolvedProblems.OrdinalCubePath

@[expose] public section

namespace OrdinalCube

variable {I : Type v} {X : Type u} [LinearOrder I] [TruthValues]

/-- The cell of x at coordinate i is determined by all its earlier child numbers.
This also defines limit cells, by intersection. -/
def Before (row : I → X → ℕ) (i : I) (x y : X) : Prop := ∀ j < i, row j y = row j x

omit [TruthValues] in
private theorem before_refl (row : I → X → ℕ) (i : I) (x : X) : Before row i x x :=
  fun _ _ => rfl

omit [TruthValues] in
private theorem before_eq {row : I → X → ℕ} {i : I} {x y : X} (h : Before row i x y) :
    Before row i x = Before row i y := by
  funext z
  apply propext
  exact ⟨fun hz j hj => (hz j hj).trans (h j hj).symm, fun hz j hj => (hz j hj).trans (h j hj)⟩

variable (bit : X → I → Bool) (wf : WellFounded ((· < ·) : I → I → Prop))

/-- A cell refines exactly when its two bits differ at the current coordinate.
Every nonsingleton half then splits immediately at its own first difference. -/
noncomputable def rows : I → X → ℕ := wf.fix fun i earlier x =>
  let C := fun y => ∀ j (h : j < i), earlier j h y = earlier j h x
  if Splits bit C i then rank bit C i x else 0

private theorem rows_eq (i : I) (x : X) :
    rows bit wf i x = if Splits bit (Before (rows bit wf) i x) i then
      rank bit (Before (rows bit wf) i x) i x else 0 := by
  conv_lhs => unfold rows; rw [WellFounded.fix_eq]
  rfl

private theorem rows_on_cell {i : I} {u : X} (x : {x // Before (rows bit wf) i u x}) :
    rows bit wf i x = if Splits bit (Before (rows bit wf) i u) i then
      rank bit (Before (rows bit wf) i u) i x else 0 := by
  rw [rows_eq bit wf i x, ← before_eq x.property]

/-- Connect consecutive children at the first stage at which two points separate. -/
def Edge (x y : X) : Prop := ∃ i, Before (rows bit wf) i x y ∧
  rows bit wf i x + 1 = rows bit wf i y

private theorem edge_on_cell {i : I} {u : X} (x y : {x // Before (rows bit wf) i u x})
    (diff : rows bit wf i x ≠ rows bit wf i y) :
    Edge bit wf x y ↔ rows bit wf i x + 1 = rows bit wf i y := by
  have h : Before (rows bit wf) i x.val y.val := fun j hj => (y.property j hj).trans (x.property j hj).symm
  constructor
  · rintro ⟨j,hj,adj⟩
    rcases lt_trichotomy j i with lt | rfl | gt
    · rw [h j lt] at adj; omega
    · exact adj
    · exact False.elim (diff (hj i gt).symm)
  · exact fun adj => ⟨i,h,adj⟩

private theorem fixes_rows (embed : Function.Injective bit) (f : Equiv.Perm X)
    (hf : Preserves (Edge bit wf) f) (i : I) : ∀ u, rows bit wf i (f u) = rows bit wf i u := by
  induction i using wf.induction with
  | h i ih =>
    intro u
    let C := Before (rows bit wf) i u
    have stable (x : X) : C x ↔ C (f x) := by
      constructor
      · exact fun hx j hj => (ih j hj x).trans (hx j hj)
      · exact fun hx j hj => (ih j hj x).symm.trans (hx j hj)
    let g : Equiv.Perm (Subtype C) := f.subtypeEquiv stable
    let R (x y : Subtype C) := Edge bit wf x.val y.val
    have hg : Preserves R g := fun x y => hf x y
    let u₀ : Subtype C := ⟨u,before_refl _ _ u⟩
    rcases truthCases (Splits bit C i) with splits | skip
    · let child (x : Subtype C) : Fin (arity bit C i) := ⟨rank bit C i x, rank_lt bit C i x⟩
      have eqChild (x : Subtype C) : rows bit wf i x = (child x).val := by
        exact (rows_on_cell bit wf x).trans (ite_eq_left splits)
      have onto : Function.Surjective child := by
        intro j
        obtain ⟨x,hx,hr⟩ := rank_onto bit C wf splits j.val j.isLt
        exact ⟨⟨x,hx⟩,Fin.ext hr⟩
      have path : PathPartition R child := by
        intro x y hxy
        have diff : rows bit wf i x ≠ rows bit wf i y := fun h => hxy (Fin.ext (by simpa only [eqChild] using h))
        simpa only [eqChild] using edge_on_cell bit wf x y diff
      have fixed : child (g u₀) = child u₀ := by
        rcases arity_options bit C i with two | three | four
        · have inj : Function.Injective child := fun x y h =>
            Subtype.ext (rank_injective_two bit C embed two x.property y.property (congrArg Fin.val h))
          apply child_fixed_of_partition onto path g hg _ u₀
          intro x y
          exact ⟨fun h => congrArg child (g.injective (inj h)), fun h => congrArg (fun a => child (g a)) (inj h)⟩
        · exact path_children_fixed (Or.inl three) onto path g hg u₀
        · exact path_children_fixed (Or.inr four) onto path g hg u₀
      exact (eqChild (g u₀)).trans ((congrArg Fin.val fixed).trans (eqChild u₀).symm)
    · have zero (x : Subtype C) : rows bit wf i x = 0 := by
        exact (rows_on_cell bit wf x).trans (ite_eq_right skip)
      exact (zero (g u₀)).trans (zero u₀).symm

/-- For every injection into a well-ordered binary cube, the canonical edge
relation on the original carrier has no nonidentity automorphisms. The only
logical parameter in its construction is decidability of propositions. -/
theorem ordinal_cube_rigid (embed : Function.Injective bit) (f : Equiv.Perm X)
    (hf : Preserves (Edge bit wf) f) (x : X) : f x = x := by
  have fixed := fixes_rows bit wf embed f hf
  apply embed
  funext i
  let C := Before (rows bit wf) i x
  have hx : C x := before_refl _ _ x
  have hfx : C (f x) := fun j _ => fixed j x
  apply Decidable.by_contra
  intro diff
  have split : Splits bit C i := ⟨f x,x,hfx,hx,diff⟩
  have eqR (z : Subtype C) : rows bit wf i z = rank bit C i z := by
    exact (rows_on_cell bit wf z).trans (ite_eq_left split)
  exact diff (rank_bit bit C ((eqR ⟨f x,hfx⟩).symm.trans ((fixed i x).trans (eqR ⟨x,hx⟩))))

/-- A loop-free directed graph on the specified carrier whose only automorphism
is the identity. Vertices, including those of a singleton or empty set, are not enlarged. -/
def HasRigidGraph (Y : Type w) : Prop :=
  ∃ R : Y → Y → Prop, (∀ x, ¬ R x x) ∧ ∀ f : Equiv.Perm Y, Preserves R f → ∀ x, f x = x

include wf in
theorem graph_of_embedding (embed : Function.Injective bit) : HasRigidGraph X := by
  refine ⟨Edge bit wf, ?_, ordinal_cube_rigid bit wf embed⟩
  rintro x ⟨i,_,h⟩
  omega

end OrdinalCube

namespace OrdinalCube

/-- Howard–Tachtsis Problem 5. The subset may be arbitrary and the coordinate
well-order may have any order type. -/
theorem ordinal_subsets {I : Type v} [LinearOrder I]
    (wf : WellFounded ((· < ·) : I → I → Prop)) (S : Set (I → Bool)) : HasRigidGraph S := by
  let _ : TruthValues := ⟨Classical.propDecidable⟩
  exact graph_of_embedding (fun x : S => x.val) wf Subtype.val_injective

/-- The first Kinna–Wagner hypothesis at the given universe levels, phrased as
an injection into the powerset of some well-ordered set for each carrier. -/
def HasOrdinalCoding.{u',v'} (Y : Type u') : Prop :=
  ∃ (J : Type v') (ord : LinearOrder J), WellFounded ord.lt ∧
    ∃ e : Y → Set J, Function.Injective e

/-- From a powerset injection on each carrier obtain a rigid relation on each.
The embeddings in the hypothesis are existential for each individual carrier. -/
theorem kwp_with_truth_values [TruthValues] (kwp : ∀ Y : Type u, HasOrdinalCoding.{u,v} Y)
    (Y : Type u) : HasRigidGraph Y := by
  obtain ⟨J,ord,hJ,e,he⟩ := kwp Y
  let _ : LinearOrder J := ord
  let bits (y : Y) (j : J) := decide (j ∈ e y)
  apply graph_of_embedding bits hJ
  intro x y h
  apply he
  ext j
  have hb := (congrArg (fun b => b = true) (congrFun h j)).to_iff
  simpa only [bits, decide_eq_true_eq] using hb

/-- The first Kinna–Wagner principle implies the rigid relation principle. -/
theorem kwp_implies_rigid (kwp : ∀ Y : Type u, HasOrdinalCoding.{u,v} Y) (Y : Type u) :
    HasRigidGraph Y := by
  let _ : TruthValues := ⟨Classical.propDecidable⟩
  exact kwp_with_truth_values kwp Y

end OrdinalCube
