module

public import Mathlib.Combinatorics.SimpleGraph.Maps

public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne
open Set Cardinal Ordinal Order Filter
/-- Indices are the actual ground-model first uncountable ordinal. -/
abbrev Row := (ω₁ : Ordinal.{0}).ToType

theorem row_cof : Order.cof Row = ℵ₁ := (Ordinal.cof_toType _).trans Cardinal.cof_omega_one

theorem row_cof_ne : Order.cof Row ≠ ℵ₀ := row_cof ▸ Cardinal.aleph0_lt_aleph_one.ne'

instance row_regular : IsRegularCardinalOrder Row := ⟨by rw [row_cof,Ordinal.type_toType,Cardinal.ord_aleph]⟩

instance row_nonempty : Nonempty Row := Ordinal.nonempty_toType_iff.mpr ((Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one).ne')
noncomputable instance row_bot : OrderBot Row := WellFoundedLT.toOrderBot _
instance row_noMax : NoMaxOrder Row :=
  (noTopOrder_iff_noMaxOrder _).1 (Order.one_lt_cof_iff.1 (one_lt_aleph0.trans_le (row_cof ▸ aleph0_lt_aleph_one.le)))

def Small (D : Set Row) : Prop := ∃ C, IsClub C ∧ Disjoint D C

theorem above (a : Row) : IsClub (Ioi a) := by
  refine ⟨?_,fun x => ?_⟩
  · intro t ht ne _ y lub
    obtain ⟨z,hz⟩ := ne
    exact lt_of_lt_of_le (ht hz) (lub.1 hz)
  · obtain ⟨y,hy⟩ := exists_gt (max a x)
    exact ⟨y,(le_max_left ..).trans_lt hy,((le_max_right ..).trans_lt hy).le⟩

theorem small_union {D E : Set Row} (h : Small D) (j : Small E) : Small (D ∪ E) := by
  obtain ⟨C,hC,e⟩ := h; obtain ⟨K,hK,f⟩ := j
  refine ⟨C∩K,hC.inter row_cof_ne hK,Set.disjoint_left.2 ?_⟩
  intro x hx h
  exact hx.elim (fun d => Set.disjoint_left.1 e d h.1) (fun t => Set.disjoint_left.1 f t h.2)

theorem small_countable_union {I : Type v} [Countable I] (D : I → Set Row) (h : ∀ i, Small (D i)) :
    Small (⋃ i, D i) := by
  choose C club dis using h
  refine ⟨⋂ i,C i,IsClub.iInter_of_countable row_cof_ne club,Set.disjoint_left.2 ?_⟩
  intro x hx hxC
  obtain ⟨i,hi⟩ := Set.mem_iUnion.1 hx
  exact Set.disjoint_left.1 (dis i) hi (Set.mem_iInter.1 hxC i)

theorem cofinal_uncountable {J : Set Row} (h : IsCofinal J) : ¬ J.Countable := by
  intro c
  have le := (Order.cof_le h).trans (Cardinal.le_aleph0_iff_set_countable.mpr c)
  exact Cardinal.aleph0_lt_aleph_one.not_ge (row_cof ▸ le)

/-- A cofinal sequence of finite row sets admits an uncountable subfamily with
one nonstationary support. Pressing down the maximum below the index replaces
the manuscript's delta-system extraction. -/
theorem thin_finite (F : Row → Finset Row) : ∃ (J C : Set Row), IsCofinal J ∧ IsClub C ∧
    ∀ i ∈ J, ∀ x ∈ F i, x ∉ C := by
  classical
  let low (i : Row) := ((F i).filter (· < i)).sup id
  have reg (i : Row) (hi : i ∈ Ioi (⊥ : Row)) : low i < i := by
    exact (Finset.sup_lt_iff hi).2 (fun _ hx => (Finset.mem_filter.1 hx).2)
  obtain ⟨b,stat⟩ := exists_isStationary_preimage_singleton row_cof_ne ((above ⊥).isStationary row_cof_ne) reg
  have next (a : Row) : ∃ i, a < i ∧ low i = b := by
    obtain ⟨i,hi,high⟩ := stat (above a)
    exact ⟨i,high,hi.2⟩
  choose g gt level using next
  let lim := {δ : Row | ∀ i < δ, (F (g i)).sup id < δ}
  have club : IsClub lim := IsClub.diag row_cof_ne (fun i => above ((F (g i)).sup id))
  let C := lim ∩ Ioi b
  have hC : IsClub C := club.inter row_cof_ne (above b)
  refine ⟨g '' C,C,?_,hC,?_⟩
  · intro x
    obtain ⟨a,ha,xa⟩ := hC.isCofinal x
    exact ⟨g a,⟨a,ha,rfl⟩,xa.trans (gt a).le⟩
  · rintro _ ⟨a,ha,rfl⟩ x hx hCₓ
    by_cases lt : x < g a
    · have le : x ≤ low (g a) := Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hx,lt⟩)
      exact (level a ▸ le).not_gt hCₓ.2
    · have lt' : a < x := (gt a).trans_le (le_of_not_gt lt)
      exact (Finset.le_sup (f := id) hx).not_gt (hCₓ.1 a lt')
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Filter Order
variable {I : Type u} (rank : I → Row)
def seen (U : Ultrafilter I) : Set Row := {b | rank ⁻¹' Iic b ∈ U}

noncomputable def endpoint (U : Ultrafilter I) : Row := by
  classical
  exact if h : (seen rank U).Nonempty then wellFounded_lt.min (seen rank U) h else ⊥

private theorem bounded_complement (U : Ultrafilter I) (hb : (seen rank U).Nonempty) {C : Set Row}
    (club : IsClub C) (outside : endpoint rank U ∉ C) : (rank ⁻¹' C)ᶜ ∈ U := by
  classical
  apply Ultrafilter.compl_mem_iff_notMem.mpr
  intro inside
  let γ := endpoint rank U
  have he (U : Ultrafilter I) (hb : (seen rank U).Nonempty) :
      endpoint rank U = wellFounded_lt.min (seen rank U) hb := by simp [endpoint,hb]
  have bounded : rank ⁻¹' Iic γ ∈ U := by
    change γ ∈ seen rank U
    dsimp [γ]; rw [he U hb]; exact wellFounded_lt.min_mem _ _
  let t := C ∩ Iic γ
  have both : rank ⁻¹' t ∈ U := inter_mem inside bounded
  obtain ⟨x,hx⟩ := Filter.nonempty_of_mem both
  have nonempty : t.Nonempty := ⟨rank x,hx⟩
  have bound : BddAbove t := ⟨γ,fun _ h => h.2⟩
  let _ := WellFoundedLT.conditionallyCompleteLinearOrderBot (α := Row)
  let b := sSup t
  have cb : b ∈ C := club.csSup_mem inter_subset_left nonempty bound
  have bg : b < γ := lt_of_le_of_ne (csSup_le nonempty (fun _ h => h.2))
    (fun eq => outside (show γ ∈ C from eq ▸ cb))
  have mem : b ∈ seen rank U := mem_of_superset both (fun i hi => le_csSup bound hi)
  exact (wellFounded_lt.not_lt_min _ mem) (he U hb ▸ bg)

/-- For uncountably many indices there is one nonstationary member of all
their ultrafilters, whenever each finite family initially has such a member.
The map to ω₁ accommodates an arbitrary residual set of rows. -/
theorem thin_ultrafilters (F : Row → Finset (Ultrafilter I))
    (individual : ∀ α, ∃ D : Set Row, Small D ∧ ∀ U ∈ F α, rank ⁻¹' D ∈ U) :
    ∃ J D : Set Row, IsCofinal J ∧ Small D ∧ ∀ α ∈ J, ∀ U ∈ F α, rank ⁻¹' D ∈ U := by
  classical
  choose D small member using individual
  choose K club dis using small
  let d := {x : Row | ∃ α < x, x ∈ D α}
  let k := {x : Row | ∀ α < x, x ∈ K α}
  have hd : Small d := ⟨k,IsClub.diag row_cof_ne club,Set.disjoint_left.2 (by
    rintro x ⟨α,hα,hx⟩ hk; exact Set.disjoint_left.1 (dis α) hx (hk α hα))⟩
  let bounds (α : Row) := ((F α).filter (fun U => (seen rank U).Nonempty)).image (endpoint rank)
  obtain ⟨J,C,cof,hC,miss⟩ := thin_finite bounds
  refine ⟨J,d ∪ Cᶜ,cof,small_union hd ⟨C,hC,disjoint_compl_left⟩,?_⟩
  intro α hα U hU
  by_cases hb : (seen rank U).Nonempty
  · have m := bounded_complement rank U hb hC (miss α hα _ (Finset.mem_image.2
        ⟨U,Finset.mem_filter.2 ⟨hU,hb⟩,rfl⟩))
    exact mem_of_superset m (fun _ h => Or.inr h)
  · have outside : rank ⁻¹' Iic α ∉ U := fun mem => hb ⟨α,mem⟩
    have both := inter_mem (member α U hU) (Ultrafilter.compl_mem_iff_notMem.mpr outside)
    exact mem_of_superset both (fun i h => Or.inl ⟨α,lt_of_not_ge h.2,h.1⟩)
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Cardinal Ordinal Order Filter
variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V]
/-- A point in a residual row action is fixed by the full product on
the complement of the indicated coordinates. -/
def PointSupport (T : Set I) (x : V) : Prop := ∀ g : I → P, (∀ i ∈ T, g i = 1) → g • x = x

def AtomSupports (rank : I → Row) : Prop :=
  ∀ x : V, ∃ D, Small D ∧ PointSupport (P := P) (rank ⁻¹' D) x

def OrbitDescriptors : Prop := ∀ x : V, Countable (MulAction.orbit (I → P) x) →
  ∃ F : Finset (Ultrafilter I), ∀ T : Set I, PointSupport (P := P) T x ↔ ∀ U ∈ F, T ∈ U

def ComparableAtOmegaOne (rank : I → Row) : Prop :=
  (∃ (e : V ↪ ℕ) (D : Set Row), Small D ∧ ∀ g : I → P, (∀ i ∈ rank ⁻¹' D, g i = 1) → ∀ x, e (g • x) = e x) ∨
  (∃ (e : Row ↪ V) (D : Set Row), Small D ∧ ∀ a, PointSupport (P := P) (rank ⁻¹' D) (e a))

theorem row_embedding {Y : Type w} (h : ¬ Countable Y) : Nonempty (Row ↪ Y) := by
  apply Cardinal.lift_mk_le.{0}.mp
  have large : ℵ₁ ≤ #Y := Cardinal.aleph_one_le_iff.mpr (lt_of_not_ge (fun e => h (Cardinal.mk_le_aleph0_iff.mp e)))
  simpa [Row] using large

/-- All the points of each orbit share the support of any one representative,
since the subgroup fixing a given set of complete rows is normal. -/
theorem support_orbit {T : Set I} {x : V} (hx : PointSupport (P := P) T x) {y : V}
    (hy : y ∈ MulAction.orbit (I → P) x) : PointSupport (P := P) T y := by
  obtain ⟨k,rfl⟩ := MulAction.mem_orbit_iff.mp hy
  intro g hg
  have h : ∀ i ∈ T, (k⁻¹ * g * k) i = 1 := by
    intro i hi; simp [hg i hi]
  have e := congrArg (fun y : V => k • y) (hx _ h)
  simpa only [← mul_smul,mul_inv_cancel_left,mul_assoc,mul_inv_cancel,one_mul] using e

/-- The manuscript's comparison argument for every hereditary object carrier.
The index set can be any residual set of rows of a supported parent. Large
orbits use normality; in the countable-orbit case the club thinning supplies
one support for an ω₁-indexed family of distinct points. -/
theorem comparison_from_descriptors (rank : I → Row) (points : AtomSupports (P := P) (V := V) rank)
    (describes : OrbitDescriptors (P := P) (I := I) (V := V)) :
    ComparableAtOmegaOne (P := P) (V := V) rank := by
  classical
  by_cases cnt : Countable V
  · let _ := cnt
    obtain ⟨f,inj⟩ := Countable.exists_injective_nat V
    choose D small fix using points
    refine Or.inl ⟨⟨f,inj⟩,⋃ x, D x,small_countable_union D small,?_⟩
    intro g hg x
    exact congrArg f (fix x g (fun i hi => hg i (Set.mem_iUnion.2 ⟨x,hi⟩)))
  by_cases all : ∀ x : V, Countable (MulAction.orbit (I → P) x)
  · obtain ⟨f⟩ := row_embedding cnt
    choose F describe using fun a : Row => describes (f a) (all _)
    have each (a : Row) : ∃ D : Set Row, Small D ∧ ∀ U ∈ F a, rank ⁻¹' D ∈ U := by
      obtain ⟨D,small,fix⟩ := points (f a)
      exact ⟨D,small,(describe a _).mp fix⟩
    obtain ⟨J,D,cof,small,agree⟩ := thin_ultrafilters rank F each
    let e := ((Order.enum J cof).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)).trans f
    exact Or.inr ⟨e,D,small,fun a => (describe _ _).mpr (agree _ (Order.enum J cof a).property)⟩
  · obtain ⟨x,big⟩ := not_forall.mp all
    obtain ⟨f⟩ := row_embedding big
    obtain ⟨D,small,fix⟩ := points x
    exact Or.inr ⟨f.trans (Function.Embedding.subtype _),D,small,fun a => support_orbit fix (f a).property⟩
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Cardinal Ordinal Order Filter
/-- Residual product group fixing every row named in a support. -/
def OnSupport {P : Type u} [Group P] (E : Set Row) (g : Row → P) := ∀ i ∈ E, g i = 1

def Holds {P : Type u} [Group P] {V : Type v} [MulAction (Row → P) V] (E : Set Row) (x : V) :=
  ∀ g : Row → P, OnSupport E g → g • x = x

abbrev FiveGroup := alternatingGroup (Fin 5)

theorem five_perfect : commutator FiveGroup = ⊤ :=
  commutator_alternatingGroup_eq_top (by simp)

end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Filter
variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V]
def supportFilter (x : V) : Filter I where
  sets := {T | PointSupport (P := P) T x}
  univ_sets := by
    intro g hg; have eq : g = 1 := funext (fun i => hg i trivial)
    rw [eq,one_smul]
  sets_of_superset h sub := fun g hg => h g (fun i hi => hg i (sub hi))
  inter_sets {A B} hA hB := by
    classical
    intro g hg
    let f (i : I) := if i ∈ A then (1 : P) else g i
    let k (i : I) := if i ∈ A then g i else 1
    have e : g = f*k := by funext i; by_cases hi : i∈A <;> simp [f,k,hi]
    have hk : ∀ i ∈ B, k i = 1 := by
      intro i hi; by_cases ha : i∈A
      · simpa [k,ha] using hg i ⟨ha,hi⟩
      · simp [k,ha]
    rw [e,mul_smul,hB k hk,hA f (by intro i hi; simp [f,hi])]

def extSlice (F : Filter I) (A : Set I) : Set (Ultrafilter I) := {U | U.toFilter ≤ F ∧ A ∈ U}

private theorem refine_slice (F : Filter I) (A : Set I) (many : (extSlice F A).Infinite) :
    ∃ B C : Set I, B ⊆ A ∧ C ⊆ A ∧ Disjoint B C ∧ (extSlice F B).Infinite ∧ (extSlice F C).Nonempty := by
  classical
  obtain ⟨U,hU⟩ := many.nonempty
  obtain ⟨V,hV,neq⟩ := many.exists_notMem_finset {U}
  have ne : U ≠ V := fun e => neq (by simp [e])
  have sep : ∃ t : Set I, t ∈ U ∧ t ∉ V := by
    by_contra! h
    apply ne
    exact (Ultrafilter.eq_of_le (show V.toFilter ≤ U.toFilter from fun _ ht => h _ ht)).symm
  obtain ⟨t,ut,vt⟩ := sep
  let B := A ∩ t
  let C := A ∩ tᶜ
  have ub : U ∈ extSlice F B := ⟨hU.1,inter_mem hU.2 ut⟩
  have vc : V ∈ extSlice F C := ⟨hV.1,inter_mem hV.2 (Ultrafilter.compl_mem_iff_notMem.mpr vt)⟩
  have dis : Disjoint B C := Set.disjoint_left.2 (fun _ hb hc => hc.2 hb.2)
  have cover : extSlice F A ⊆ extSlice F B ∪ extSlice F C := by
    intro W h
    rcases W.mem_or_compl_mem t with p | p
    · exact Or.inl ⟨h.1,inter_mem h.2 p⟩
    · exact Or.inr ⟨h.1,inter_mem h.2 p⟩
  rcases Set.infinite_union.mp (many.mono cover) with inf | inf
  · exact ⟨B,C,inter_subset_left,inter_subset_left,dis,inf,⟨V,vc⟩⟩
  · exact ⟨C,B,inter_subset_left,inter_subset_left,dis.symm,inf,⟨U,ub⟩⟩

/-- A filter with no countably infinite disjoint sequence of positive sets is
the intersection of finitely many ultrafilters. This includes the improper
filter, represented by the empty family. -/
theorem finite_descriptors (F : Filter I)
    (noSeq : ¬ ∃ s : ℕ → Set I, Pairwise (fun i j => Disjoint (s i) (s j)) ∧ ∀ n, (s n)ᶜ ∉ F) :
    ∃ family : Finset (Ultrafilter I), ∀ T : Set I, T ∈ F ↔ ∀ U ∈ family, T ∈ U := by
  classical
  let all := {U : Ultrafilter I | U.toFilter ≤ F}
  have finite : all.Finite := by
    by_contra inf
    let State := {A : Set I // (extSlice F A).Infinite}
    have init : (extSlice F univ).Infinite := by
      apply Set.Infinite.mono (s := all) _ inf
      exact fun U hU => ⟨hU,Filter.univ_mem⟩
    choose next out subNext subOut dis infinite pos using fun a : State => refine_slice F a.val a.property
    let state : ℕ → State := Nat.rec ⟨univ,init⟩ (fun _ a => ⟨next a,infinite a⟩)
    have down (n : ℕ) : (state (n+1)).val ⊆ (state n).val := subNext _
    have nested {n m : ℕ} (h : n ≤ m) : (state m).val ⊆ (state n).val := by
      induction h with
      | refl => exact Subset.rfl
      | step _ ih => exact (down _).trans ih
    have apart {n m : ℕ} (h : n < m) : Disjoint (out (state n)) (out (state m)) :=
      (dis _).symm.mono_right ((subOut _).trans (nested (show n+1 ≤ m from h)))
    apply noSeq
    refine ⟨fun n => out (state n),fun n m h => (lt_or_gt_of_ne h).elim (fun l => apart l) (fun l => (apart l).symm),?_⟩
    intro n bad
    obtain ⟨U,hU,mem⟩ := pos (state n)
    exact (Ultrafilter.compl_mem_iff_notMem.mp (hU bad)) mem
  refine ⟨finite.toFinset,fun T => ?_⟩
  simpa [all,Set.Finite.mem_toFinset] using (Filter.mem_iff_ultrafilter (f := F) (s := T))
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Subgroup
variable {I : Type u} {P : Type v} [Group P]
def blockMap (T : Set I) [DecidablePred (· ∈ T)] : (T → P) →* (I → P) where
  toFun f i := if h : i∈T then f ⟨i,h⟩ else 1
  map_one' := by funext i; by_cases hi : i∈T <;> simp [hi]
  map_mul' f g := by funext i; by_cases hi : i∈T <;> simp [hi]

theorem locally_finite_power [Finite P] (s : Finset (I → P)) :
    Finite (Subgroup.closure (s : Set (I → P))) := by
  classical
  let read (i : I) (g : s) := g.val i
  let φ : ((s → P) → P) →* (I → P) :=
    {toFun := fun f i => f (read i), map_one' := rfl, map_mul' := fun _ _ => rfl}
  have le : Subgroup.closure (s : Set (I → P)) ≤ φ.range :=
    (Subgroup.closure_le _).mpr (fun f hf => ⟨(fun t => t ⟨f,hf⟩),rfl⟩)
  have fr : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact Finite.of_injective (Subgroup.inclusion le) (Subgroup.inclusion_injective le)

private def constBlock (T : Set I) [DecidablePred (· ∈ T)] : P →* (I → P) where
  toFun a i := if i∈T then a else 1
  map_one' := by funext i; simp
  map_mul' f g := by funext i; by_cases hi : i∈T <;> simp [hi]

theorem perfect_power [Finite P] (perfect : commutator P = ⊤) :
    commutator (I → P) = ⊤ := by
  classical
  let _ := Fintype.ofFinite P
  apply top_unique
  intro f _
  have mapped (T : Set I) (p : P) : constBlock (I := I) T p ∈ commutator (I → P) := by
    let h := constBlock (P := P) T
    have m : h p ∈ (commutator P).map h := ⟨p,by rw [perfect]; exact trivial,rfl⟩
    rw [map_commutator_eq] at m
    exact Subgroup.commutator_mono le_top le_top m
  let part (s : Finset P) (i : I) := if f i ∈ s then f i else 1
  have ok (s : Finset P) : part s ∈ commutator (I → P) := by
    induction s using Finset.induction_on with
    | empty =>
      have e : part ∅ = (1 : I→P) := by funext i; simp [part]
      rw [e]; exact (commutator (I→P)).one_mem
    | @insert a s ha ih =>
      have e : part (insert a s) = constBlock {i | f i = a} a * part s := by
        funext i
        by_cases hi : f i = a <;> simp [part,constBlock,hi,ha]
      exact e ▸ (commutator (I→P)).mul_mem (mapped _ a) ih
  simpa [part] using ok Finset.univ

theorem block_commute {A B : Set I} [DecidablePred (·∈A)] [DecidablePred (·∈B)] (dis : Disjoint A B)
    (a : A → P) (b : B → P) : Commute (blockMap A a) (blockMap B b) := by
  funext i
  by_cases ha : i∈A
  · have hb : i∉B := Set.disjoint_left.1 dis ha
    simp [blockMap,ha,hb]
  · simp [blockMap,ha]
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Subgroup
open scoped commutatorElement
variable {G : Type u} [Group G] {V : Type v} [MulAction G V]
def respects (S : Set V) : Subgroup G where
  carrier := {g | ∀ v, g • v ∈ S ↔ v ∈ S}
  one_mem' _ := by rw [one_smul]
  mul_mem' {a b} ha hb v := by rw [mul_smul]; exact (ha _).trans (hb v)
  inv_mem' {a} ha v := by simpa only [smul_inv_smul] using (ha (a⁻¹ • v)).symm

def permOn (S : Set V) : respects (G := G) S →* Equiv.Perm S where
  toFun g := (MulAction.toPerm g.val).subtypeEquiv (p := fun v => v∈S) (q := fun v => v∈S) (fun v => (g.property v).symm)
  map_one' := Equiv.ext (fun v => Subtype.ext (one_smul G v.val))
  map_mul' a b := Equiv.ext (fun v => Subtype.ext (mul_smul a.val b.val v.val))

theorem noncommuting_image {H : Type u} [Group H] {K : Type v} [Group K] (φ : H →* K)
    (perfect : commutator H = ⊤) (nontriv : ∃ p, φ p ≠ 1) : ∃ a b, ¬ Commute (φ a) (φ b) := by
  classical
  by_contra! comm
  have ker : commutator H ≤ φ.ker := by
    rw [commutator_eq_closure]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨a,b,rfl⟩
    exact (map_commutatorElement _ _ _).trans (commutatorElement_eq_one_iff_commute.mpr (comm a b))
  obtain ⟨p,hp⟩ := nontriv
  exact hp (ker (perfect ▸ (show p ∈ (⊤ : Subgroup H) from trivial)))

private theorem transports (L : Subgroup G) (x : V) {a : G}
    (comm : ∀ h ∈ L, Commute a h) (mem : a • x ∈ MulAction.orbit L x)
    {y : V} (hy : y ∈ MulAction.orbit L x) : a • y ∈ MulAction.orbit L x := by
  obtain ⟨h,rfl⟩ := MulAction.mem_orbit_iff.mp hy
  change a • (h.val • x) ∈ _
  rw [← mul_smul,(comm h.val h.property).eq,mul_smul]
  exact MulAction.mem_orbit_of_mem_orbit h mem

theorem escape {H : ℕ → Type w} [∀ n, Group (H n)] (φ : ∀ n, H n →* G)
    (perfect : ∀ n, commutator (H n) = ⊤)
    (cross : ∀ i j, i ≠ j → ∀ a b, Commute (φ i a) (φ j b)) (L : Subgroup G) [Finite L] (x : V)
    (pos : ∀ n, ∃ h, φ n h • x ≠ x) (central : ∀ n h k, k ∈ L → Commute (φ n h) k) :
    ∃ (n : ℕ) (a b : H n), φ n ⁅a,b⁆ • x ∉ MulAction.orbit L x := by
  classical
  by_contra! confined
  let S := MulAction.orbit L x
  have fin : Finite S := Finite.of_surjective (fun h : L => (⟨h • x,MulAction.mem_orbit x h⟩ : S)) (by
    intro y; obtain ⟨h,eq⟩ := MulAction.mem_orbit_iff.mp y.property; exact ⟨h,Subtype.ext eq⟩)
  have maps (n : ℕ) (h : H n) : φ n h ∈ respects (G := G) S := by
    have inc : commutator (H n) ≤ (respects (G := G) S).comap (φ n) := by
      rw [commutator_eq_closure]
      apply (Subgroup.closure_le _).2
      rintro _ ⟨a,b,rfl⟩
      intro v
      constructor
      · intro hv
        have back := transports L x (central n ⁅b,a⁆) (confined n b a) hv
        have e : φ n ⁅b,a⁆ = (φ n ⁅a,b⁆)⁻¹ := by rw [← map_inv,commutatorElement_inv]
        simpa only [e,inv_smul_smul] using back
      · exact transports L x (central n ⁅a,b⁆) (confined n a b)
    exact inc ((perfect n) ▸ (show h ∈ (⊤ : Subgroup (H n)) from trivial))
  let ψ (n : ℕ) := (permOn (G := G) S).comp ((φ n).codRestrict (respects S) (maps n))
  have nontriv (n : ℕ) : ∃ h, ψ n h ≠ 1 := by
    obtain ⟨h,move⟩ := pos n
    refine ⟨h,fun eq => move ?_⟩
    exact congrArg (fun e : Equiv.Perm S => (e ⟨x,MulAction.mem_orbit_self x⟩).val) eq
  choose a b ne using fun n => noncommuting_image (ψ n) (perfect n) (nontriv n)
  have collision : ¬ Function.Injective (fun n => ψ n (a n)) := by
    intro inj
    let _ := Finite.of_injective _ inj
    exact _root_.not_finite ℕ
  obtain ⟨i,j,same,diff⟩ := Function.not_injective_iff.mp collision
  apply ne j
  rw [← same]
  apply Equiv.ext
  intro y
  apply Subtype.ext
  change φ i (a i) • (φ j (b j) • y.val) = φ j (b j) • (φ i (a i) • y.val)
  rw [← mul_smul,← mul_smul,(cross i j diff (a i) (b j)).eq]
end ChoiceOmegaOne
namespace ChoiceOmegaOne.Cantor
open Set
abbrev Branch := ℕ → Bool
abbrev Word := Σ n : ℕ, Fin n → Bool

def node (s : Branch) (n : ℕ) : Word := ⟨n,fun i => s i⟩
def On (s : Branch) (t : Word) : Prop := ∀ k : Fin t.1, s k = t.2 k

theorem same_node {s : Branch} {t : Word} (h : On s t) : node s t.1 = t := by
  obtain ⟨n,w⟩ := t
  exact congrArg (Sigma.mk n) (funext h)

private theorem uncountable : ¬ Countable Branch := by
  intro c
  obtain ⟨f,surj⟩ := @exists_surjective_nat Branch ⟨fun _ => false⟩ c
  obtain ⟨n,h⟩ := surj (fun n => !(f n n))
  have e := congrFun h n
  cases he : f n n <;> simp [he] at e

private theorem large_color {Y : Type u} [Countable Y] (f : Branch → Y) : ∃ c, ¬ (f ⁻¹' {c}).Countable := by
  classical
  by_contra! h
  apply uncountable
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion h).mono
  exact fun x _ => Set.mem_iUnion.2 ⟨f x,rfl⟩

private theorem condensation {B : Set Branch} (h : ¬ B.Countable) :
    ∃ s ∈ B, ∀ n, ¬ {r ∈ B | On r (node s n)}.Countable := by
  classical
  by_contra! all
  let slice (w : Word) := {r ∈ B | On r w}
  let small := {w : Word // (slice w).Countable}
  apply h
  apply (Set.countable_iUnion (fun w : small => w.property)).mono
  intro s hs
  obtain ⟨n,hn⟩ := all s hs
  exact Set.mem_iUnion.2 ⟨⟨node s n,hn⟩,hs,fun _ => rfl⟩

structure Split (s t : Branch) (n : ℕ) : Prop where
  earlier : ∀ k < n, s k = t k
  differ : s n ≠ t n

private theorem different (s : Branch) {B : Set Branch} (many : ∀ n, ¬ {r ∈ B | On r (node s n)}.Countable)
    (n : ℕ) : ∃ r ∈ B, ∃ m ≥ n, Split r s m := by
  classical
  have extra : ∃ r ∈ B, On r (node s n) ∧ r ≠ s := by
    by_contra! h
    apply many n
    apply (Set.countable_singleton s).mono
    intro x hx; exact h x hx.1 hx.2
  obtain ⟨r,hr,pre,ne⟩ := extra
  have dif : ∃ k, r k ≠ s k := by
    by_contra! eq
    exact ne (funext eq)
  let m := Nat.find dif
  have before (k : ℕ) (hk : k < m) : r k = s k := not_not.mp (Nat.find_min dif hk)
  refine ⟨r,hr,m,?_,before,Nat.find_spec dif⟩
  by_contra! short
  exact (Nat.find_spec dif) (pre ⟨m,short⟩)

theorem four_same {Y : Type u} [Countable Y] (f : Branch → Y) :
    ∃ (r v s w : Branch) (a b c : ℕ), f r=f s ∧ f v=f w ∧ a<b ∧ b<c ∧
      Split r s a ∧ Split v s b ∧ Split w s c := by
  obtain ⟨y,large⟩ := large_color f
  obtain ⟨s,hs,big⟩ := condensation large
  obtain ⟨r,hr,a,_,ar⟩ := different s big 0
  obtain ⟨v,hv,b,ab,bv⟩ := different s big (a+1)
  obtain ⟨w,hw,c,bc,cw⟩ := different s big (b+1)
  exact ⟨r,v,s,w,a,b,c,(show f r=y from hr).trans (show f s=y from hs).symm,
    (show f v=y from hv).trans (show f w=y from hw).symm,ab,bc,ar,bv,cw⟩

private theorem on_short {r s : Branch} {a : ℕ} (h : Split r s a) {t : Word} (ht : t.1 ≤ a) :
    On r t ↔ On s t := by
  constructor <;> intro f k
  · exact (h.earlier k (k.isLt.trans_le ht)).symm.trans (f k)
  · exact (h.earlier k (k.isLt.trans_le ht)).trans (f k)

private theorem not_both {r s : Branch} {a : ℕ} (h : Split r s a) {t : Word} (ht : a < t.1) :
    ¬ (On r t ∧ On s t) := fun e => h.differ ((e.1 ⟨a,ht⟩).trans (e.2 ⟨a,ht⟩).symm)

def path (s : Branch) (b c : ℕ) : Finset Word := (Finset.Ioc b c).image (node s)

theorem path_nonempty (s : Branch) {b c : ℕ} (lt : b < c) : (path s b c).Nonempty := by
  exact ⟨node s c,Finset.mem_image.2 ⟨c,Finset.mem_Ioc.2 ⟨lt,le_rfl⟩,rfl⟩⟩

theorem path_signs {r v s w : Branch} {a b c : ℕ} (ab : a<b) (bc : b<c)
    (ar : Split r s a) (bv : Split v s b) (cw : Split w s c) (t : Word) :
    (t ∈ path s b c → ¬ On r t ∧ On s t ∧ ¬ On v t ∧ On w t) ∧
    (t ∉ path s b c → (On r t ↔ On s t) ∨ (On v t ↔ On w t)) := by
  classical
  constructor
  · intro ht
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨bd,dc⟩ := Finset.mem_Ioc.mp hd
    have os : On s (node s d) := fun _ => rfl
    exact ⟨fun h => not_both ar (ab.trans bd) ⟨h,os⟩,os,fun h => not_both bv bd ⟨h,os⟩,
      (on_short cw dc).mpr os⟩
  · intro ht
    by_cases small : t.1 ≤ a
    · exact Or.inl (on_short ar small)
    have aa : a < t.1 := lt_of_not_ge small
    by_cases or' : On r t
    · right
      have exclude {z : Branch} (eq : z a = s a) : ¬On z t := fun on =>
        ar.differ (((or' ⟨a,aa⟩).trans (on ⟨a,aa⟩).symm).trans eq)
      exact iff_of_false (exclude (bv.earlier a ab)) (exclude (cw.earlier a (ab.trans bc)))
    by_cases os : On s t
    · right
      by_cases bb : t.1 ≤ b
      · exact (on_short bv bb).trans (on_short cw (bb.trans bc.le)).symm
      have high : b < t.1 := lt_of_not_ge bb
      have far : c < t.1 := by
        by_contra! short
        exact ht (Finset.mem_image.2 ⟨t.1,Finset.mem_Ioc.2 ⟨high,short⟩,same_node os⟩)
      exact iff_of_false (fun h => not_both bv high ⟨h,os⟩) (fun h => not_both cw far ⟨h,os⟩)
    · exact Or.inl (iff_of_false or' os)
end ChoiceOmegaOne.Cantor
namespace ChoiceOmegaOne
open Set Subgroup
open scoped commutatorElement
variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V]
def blockFix (T : Set I) : Subgroup (I → P) where
  carrier := {g | ∀ i ∈ T, g i=1}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb i hi := by simp [ha i hi,hb i hi]
  inv_mem' {a} ha i hi := by simp [ha i hi]

structure Move (I : Type u) (P : Type v) [Group P] (blocks : ℕ → Set I) where
  tag : ℕ
  a : I → P
  b : I → P
  offA : ∀ i ∉ blocks tag, a i=1
  offB : ∀ i ∉ blocks tag, b i=1
namespace Move
variable {blocks : ℕ → Set I}
def gens (l : List (Move I P blocks)) : Finset (I → P) := by
  classical
  exact (l.map Move.a ++ l.map Move.b).toFinset

def earlier (l : List (Move I P blocks)) : Subgroup (I → P) := Subgroup.closure (gens l : Set _)

theorem generators_mem {l : List (Move I P blocks)} {m : Move I P blocks} (h : m ∈ l) :
    m.a ∈ earlier l ∧ m.b ∈ earlier l := by
  classical
  constructor <;> apply Subgroup.subset_closure
  · exact List.mem_toFinset.2 (List.mem_append_left _ (List.mem_map.2 ⟨m,h,rfl⟩))
  · exact List.mem_toFinset.2 (List.mem_append_right _ (List.mem_map.2 ⟨m,h,rfl⟩))

private theorem later (s : ℕ) (l : List (Move I P blocks)) (higher : ∀ m ∈ l, m.tag < s)
    (apart : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) : earlier l ≤ blockFix (blocks s) := by
  classical
  apply (Subgroup.closure_le _).2
  intro f hf
  have h := List.mem_append.1 (List.mem_toFinset.1 (show f ∈ gens l from hf))
  rcases h with h | h
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.1 h
    exact fun i hi => m.offA i (fun old => Set.disjoint_left.1 (apart (higher m hm).ne) old hi)
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.1 h
    exact fun i hi => m.offB i (fun old => Set.disjoint_left.1 (apart (higher m hm).ne) old hi)

/-- Select a previously unused block and a commutator carrying the point
outside the entire orbit of all the generators picked earlier. -/
theorem next [Finite P] (perfect : commutator P = ⊤)
    (apart : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) (x : V)
    (positive : ∀ n, ¬ PointSupport (P := P) (blocks n)ᶜ x) (l : List (Move I P blocks)) :
    ∃ m : Move I P blocks, (∀ k ∈ l, k.tag < m.tag) ∧ ⁅m.a,m.b⁆ • x ∉ MulAction.orbit (earlier l) x := by
  classical
  let N := l.toFinset.sup Move.tag + 1
  have tag_lt (m : Move I P blocks) (h : m ∈ l) : m.tag < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := Move.tag) (List.mem_toFinset.2 h))
  let s (n : ℕ) := blocks (N+n)
  let φ (n : ℕ) := blockMap (P := P) (s n)
  let L := earlier l
  have finite : Finite L := locally_finite_power (gens l)
  have central (n : ℕ) (a : s n → P) (g : I→P) (hg : g∈L) : Commute (φ n a) g := by
    funext i
    by_cases hi : i∈s n
    · have e : g i=1 := later (N+n) l (fun m hm => (tag_lt m hm).trans_le (Nat.le_add_right ..)) apart hg i hi
      simp [e]
    · simp [φ,blockMap,hi]
  have pos (n : ℕ) : ∃ a : s n → P, φ n a • x ≠ x := by
    by_contra! h
    apply positive (N+n)
    intro g hg
    have eq : φ n (fun i => g i.val) = g := by
      funext i; by_cases hi : i∈s n
      · simp [φ,blockMap,hi]
      · simp [φ,blockMap,hi,hg i hi]
    exact eq ▸ h _
  obtain ⟨n,a,b,esc⟩ := escape φ (fun _ => perfect_power perfect)
    (fun i j ne => block_commute (apart (fun e => ne (Nat.add_left_cancel e)))) L x pos central
  have off (a : s n → P) (i : I) (hi : i∉s n) : φ n a i=1 := by simp [φ,blockMap,hi]
  refine ⟨⟨N+n,φ n a,φ n b,off a,off b⟩,fun m hm => (tag_lt m hm).trans_le (Nat.le_add_right ..),?_⟩
  rwa [map_commutatorElement] at esc
end Move
structure Witness (I : Type u) (P : Type v) [Group P] (V : Type w) [MulAction (I→P) V] (x : V) where
  blocks : ℕ → Set I
  apart : Pairwise (fun i j => Disjoint (blocks i) (blocks j))
  a : ℕ → I → P
  b : ℕ → I → P
  offA : ∀ n i, i ∉ blocks n → a n i=1
  offB : ∀ n i, i ∉ blocks n → b n i=1
  moves : ∀ (n : ℕ) (l : List ℕ), (∀ j ∈ l, j<n) →
    ((l.map (fun j => ⁅a j,b j⁆)).prod * ⁅a n,b n⁆) • x ≠ x

theorem witness_of_disjoint [Finite P] (perfect : commutator P = ⊤) (s : ℕ → Set I)
    (apart : Pairwise (fun i j => Disjoint (s i) (s j))) (x : V)
    (positive : ∀ n, ¬ PointSupport (P := P) (s n)ᶜ x) : Nonempty (Witness I P V x) := by
  classical
  choose pick high step using Move.next perfect apart x positive
  let hist : ℕ → List (Move I P s) := Nat.rec [] (fun _ l => pick l :: l)
  let m (n : ℕ) := pick (hist n)
  have earlier {i j : ℕ} (h : i < j) : m i ∈ hist j := by
    induction j with
    | zero => omega
    | succ j ih =>
      change m i ∈ m j :: hist j
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
      · exact List.mem_cons_of_mem _ (ih h)
      · exact List.mem_cons_self
  have strict : StrictMono (fun n => (m n).tag) := fun _ _ lt => high _ _ (earlier lt)
  refine ⟨⟨fun n => s (m n).tag,fun i j ne => apart (fun eq => ne (strict.injective eq)),fun n => (m n).a,
     fun n => (m n).b,fun n => (m n).offA,fun n => (m n).offB,?_⟩⟩
  intro n l bound fix
  let L := Move.earlier (hist n)
  let p := (l.map (fun j => ⁅(m j).a,(m j).b⁆)).prod
  have hp : p ∈ L := L.list_prod_mem (by
    intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_map.1 hg
    obtain ⟨ha,hb⟩ := Move.generators_mem (earlier (bound j hj))
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb))
  apply step (hist n)
  refine MulAction.mem_orbit_iff.2 ⟨⟨p⁻¹,L.inv_mem hp⟩,?_⟩
  have h : p • (⁅(m n).a,(m n).b⁆ • x) = x := (mul_smul ..).symm.trans fix
  exact (inv_smul_eq_iff.mpr h.symm)
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Subgroup
open scoped commutatorElement
variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V] {x : V}
variable (W : Witness I P V x)
def locate (i : I) : Option ℕ := by
  classical
  exact if h : ∃ n, i ∈ W.blocks n then some h.choose else none

private theorem locate_some {i : I} {n : ℕ} (h : locate W i = some n) : i ∈ W.blocks n := by
  classical
  unfold locate at h
  split at h
  · rename_i yes
    exact Option.some.inj h ▸ yes.choose_spec
  · cases h

private theorem locate_none {i : I} (h : locate W i = none) : ∀ n, i ∉ W.blocks n := by
  intro n hn
  classical
  simp [locate,show ∃ j, i∈W.blocks j from ⟨n,hn⟩] at h

def simultaneous (flag : ℕ → Prop) (f : ℕ → I → P) (i : I) : P := by
  classical
  exact match locate W i with | none => 1 | some n => if flag n then f n i else 1

private theorem product_at (u : ℕ → I → P) (l : List ℕ) (i : I) :
    (l.map u).prod i = (l.map (fun j => u j i)).prod := by
  induction l with
  | nil => rfl
  | cons j l ih => simp [ih]

private theorem sparse (f : ℕ → P) (k : ℕ) (off : ∀ j, j ≠ k → f j=1) (l : List ℕ) (nd : l.Nodup) :
    (l.map f).prod = if k∈l then f k else 1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨fresh,nd'⟩ := List.nodup_cons.mp nd
    by_cases eq : j=k
    · subst j; simp [ih nd',fresh]
    · simp [ih nd',off j eq,Ne.symm eq]

/-- For four flags of blocks, cancellation outside a finite list and two
positive signs on it identify the commutator exactly, coordinate by coordinate. -/
theorem assemble (r s v w : ℕ → Prop) (l : List ℕ) (nd : l.Nodup)
    (inside : ∀ n ∈ l, ¬ r n ∧ s n ∧ ¬ v n ∧ w n)
    (outside : ∀ n ∉ l, (r n ↔ s n) ∨ (v n ↔ w n)) :
    ⁅(simultaneous W r W.a)⁻¹ * simultaneous W s W.a,
       (simultaneous W v W.b)⁻¹ * simultaneous W w W.b⁆ = (l.map (fun j => ⁅W.a j,W.b j⁆)).prod := by
  classical
  funext i
  rw [product_at]
  change ⁅(simultaneous W r W.a i)⁻¹ * simultaneous W s W.a i,
    (simultaneous W v W.b i)⁻¹ * simultaneous W w W.b i⁆ = _
  cases e : locate W i with
  | none =>
    have all (n : ℕ) : ⁅W.a n,W.b n⁆ i = 1 := by
      have no := locate_none W e n
      simp [commutatorElement_def,W.offA n i no,W.offB n i no]
    rw [show (fun n => ⁅W.a n,W.b n⁆ i) = (fun _ => (1:P)) from funext all]
    simp [simultaneous,e]
  | some k =>
    have mem := locate_some W e
    let u (j : ℕ) := ⁅W.a j,W.b j⁆ i
    have off (j : ℕ) (ne : j ≠ k) : u j=1 := by
      have dis : i ∉ W.blocks j := fun m => Set.disjoint_left.1 (W.apart ne) m mem
      simp [u,commutatorElement_def,W.offA j i dis,W.offB j i dis]
    rw [sparse u k off l nd]
    by_cases h : k∈l
    · obtain ⟨hr,hs,hv,hw⟩ := inside k h
      simp [u,commutatorElement_def,simultaneous,e,h,hr,hs,hv,hw]
    · rcases outside k h with eq | eq
      · simp only [simultaneous,e,eq,inv_mul_cancel,commutatorElement_one_left,ite_eq_right h]
      · simp only [simultaneous,e,eq,inv_mul_cancel,commutatorElement_one_right,ite_eq_right h]

include W in
theorem witness_uncountable : ¬ Countable (MulAction.orbit (I→P) x) := by
  classical
  intro cnt
  let _ := cnt
  obtain ⟨code,injection⟩ := Countable.exists_injective_nat Cantor.Word
  let flag (r : Cantor.Branch) (n : ℕ) := ∃ t : Cantor.Word, code t=n ∧ Cantor.On r t
  have of_word (r : Cantor.Branch) (t : Cantor.Word) : flag r (code t) ↔ Cantor.On r t := by
    constructor
    · rintro ⟨w,e,h⟩; exact injection e ▸ h
    · exact fun h => ⟨t,rfl,h⟩
  let A r := simultaneous W (flag r) W.a
  let B r := simultaneous W (flag r) W.b
  let point (g : I→P) : MulAction.orbit (I→P) x := ⟨g • x,MulAction.mem_orbit x g⟩
  obtain ⟨r,v,s,w,a,b,c,ha,hb,ab,bc,ar,bv,cw⟩ := Cantor.four_same (fun r => (point (A r),point (B r)))
  have fixA : (A r)⁻¹ * A s ∈ MulAction.stabilizer (I→P) x := by
    have eq := congrArg (fun p : MulAction.orbit (I→P) x × MulAction.orbit (I→P) x => p.1.val) ha
    change ((A r)⁻¹ * A s) • x = x
    rw [mul_smul,← show A r • x = A s • x from eq,inv_smul_smul]
  have fixB : (B v)⁻¹ * B w ∈ MulAction.stabilizer (I→P) x := by
    have eq := congrArg (fun p : MulAction.orbit (I→P) x × MulAction.orbit (I→P) x => p.2.val) hb
    change ((B v)⁻¹ * B w) • x = x
    rw [mul_smul,← show B v • x = B w • x from eq,inv_smul_smul]
  let path := Cantor.path s b c
  let M := path.image code
  have nonempty : M.Nonempty := (Cantor.path_nonempty s bc).image code
  let n := M.max' nonempty
  have hn : n∈M := M.max'_mem nonempty
  let rest := (M.erase n).toList
  let l := rest ++ [n]
  have memL (j : ℕ) : j∈l ↔ j∈M := by
    by_cases eq : j=n
    · subst j; simp [l,rest,hn]
    · simp [l,rest,eq]
  have nd : l.Nodup := by
    simp [l,rest,List.nodup_append,Finset.nodup_toList]
    exact fun _ h _ => h
  have signs := Cantor.path_signs ab bc ar bv cw
  have inner (j : ℕ) (hj : j∈l) : ¬flag r j ∧ flag s j ∧ ¬flag v j ∧ flag w j := by
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ((memL j).mp hj)
    simpa only [of_word] using (signs t).1 ht
  have outer (j : ℕ) (hj : j∉l) : (flag r j ↔ flag s j) ∨ (flag v j ↔ flag w j) := by
    by_cases coded : ∃ t, code t=j
    · obtain ⟨t,rfl⟩ := coded
      have no : t∉path := fun ht => hj ((memL _).mpr (Finset.mem_image.2 ⟨t,ht,rfl⟩))
      simpa only [of_word] using (signs t).2 no
    · have no (t : Cantor.Branch) : ¬flag t j := fun ⟨w,h,_⟩ => coded ⟨w,h⟩
      exact Or.inl (iff_of_false (no r) (no s))
  let K := MulAction.stabilizer (I→P) x
  have fixed : ⁅(A r)⁻¹ * A s,(B v)⁻¹ * B w⁆ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem fixA fixB) (K.inv_mem fixA)) (K.inv_mem fixB)
  have eq := assemble W (flag r) (flag s) (flag v) (flag w) l nd inner outer
  rw [eq] at fixed
  apply W.moves n rest (fun j hj => lt_of_le_of_ne
    (M.le_max' _ (Finset.mem_erase.1 (Finset.mem_toList.1 hj)).2) (Finset.mem_erase.1 (Finset.mem_toList.1 hj)).1)
  simpa [l] using (show (l.map (fun j => ⁅W.a j,W.b j⁆)).prod • x = x from fixed)
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set Filter Order
variable {I : Type u} {P : Type v} [Group P] [Finite P] {V : Type w} [MulAction (I → P) V]
theorem descriptors_of_perfect (perfect : commutator P = ⊤) : OrbitDescriptors (I := I) (P := P) (V := V) := by
  intro x cnt
  apply finite_descriptors (supportFilter (P := P) x)
  rintro ⟨s,apart,pos⟩
  obtain ⟨w⟩ := witness_of_disjoint perfect s apart x pos
  exact witness_uncountable w cnt

theorem comparison_of_perfect (rank : I → Row) (perfect : commutator P = ⊤)
    (points : AtomSupports (P := P) (V := V) rank) : ComparableAtOmegaOne (P := P) (V := V) rank :=
  comparison_from_descriptors rank points (descriptors_of_perfect perfect)
end ChoiceOmegaOne
namespace ChoiceOmegaOne
open Set
variable {P : Type u} [Group P] {A : Type v} [MulAction (Row→P) A]
def SymmetricSet (X : Set A) : Prop := ∃ E : Set Row, Small E ∧
  ∀ g : Row→P, OnSupport E g → ∀ a, g • a ∈ X ↔ a ∈ X

def SymmetricPoints (X : Set A) : Prop := ∀ a ∈ X, ∃ D : Set Row, Small D ∧ Holds (P := P) D a

def SetComparison (X : Set A) : Prop :=
  (∃ (_ : X ↪ ℕ) (D : Set Row), Small D ∧ ∀ a ∈ X, Holds (P := P) D a) ∨
  (∃ (e : Row ↪ X) (D : Set Row), Small D ∧ ∀ i, Holds (P := P) D (e i).val)

/-- Cardinal comparison for all internal set carriers, with the action of the
full product on their ambient objects. Restriction to the residual product is
necessary because the full group may move the set itself. -/
theorem set_comparison [Finite P] (perfect : commutator P = ⊤) (X : Set A)
    (setSym : SymmetricSet (P := P) X) (points : SymmetricPoints (P := P) X) :
    SetComparison (P := P) X := by
  classical
  obtain ⟨E,smallE,hE⟩ := setSym
  let I := {i : Row // i∉E}
  let extend := blockMap (P := P) Eᶜ
  have onE (g : I→P) : OnSupport E (extend g) := by
    intro i hi; simp [extend,blockMap,hi]
  let hom := (permOn (G := Row→P) X).comp (extend.codRestrict (respects X)
    (fun g => hE (extend g) (onE g)))
  let _ : MulAction (I→P) X := MulAction.compHom X hom
  have act (g : I→P) (a : X) : (g • a).val = extend g • a.val := rfl
  have sub : AtomSupports (P := P) (V := X) (fun i : I => i.val) := by
    intro a
    obtain ⟨D,smallD,fixed⟩ := points a.val a.property
    refine ⟨D,smallD,fun g hg => Subtype.ext ((act g a).trans (fixed _ ?_))⟩
    intro i hi
    by_cases mem : i ∈ E
    · simp [extend,blockMap,mem]
    · simpa [extend,blockMap,mem] using hg ⟨i,mem⟩ hi
  have liftFix {D : Set Row} {a : X} (h : PointSupport (P := P) ((fun i : I => i.val) ⁻¹' D) a) :
      Holds (P := P) (E∪D) a.val := by
    intro g hg
    let k (i : I) := g i.val
    have e : extend k = g := by
      funext i; by_cases hi : i∈E
      · simp [extend,blockMap,hi,hg i (Or.inl hi)]
      · simp [extend,blockMap,hi,k]
    have fixed := congrArg Subtype.val (h k (fun i hi => hg i.val (Or.inr hi)))
    rw [act,e] at fixed
    exact fixed
  rcases comparison_of_perfect (fun i : I => i.val) perfect sub with ⟨f,D,small,fix⟩ | ⟨f,D,small,fix⟩
  · exact Or.inl ⟨f,E∪D,small_union smallE small,fun a ha => liftFix (a := ⟨a,ha⟩)
      (fun g hg => f.injective (fix g hg _))⟩
  · exact Or.inr ⟨f,E∪D,small_union smallE small,fun i => liftFix (fix i)⟩

theorem five_comparison {Y : Type v} [MulAction (Row→FiveGroup) Y] (X : Set Y)
    (setSym : SymmetricSet (P := FiveGroup) X) (points : SymmetricPoints (P := FiveGroup) X) :
    SetComparison (P := FiveGroup) X := set_comparison five_perfect X setSym points

end ChoiceOmegaOne

namespace ChoiceOmegaOne

open Set Cardinal Ordinal Order

private theorem countable_predecessors (i : Row) : Countable (Iio i) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt i (show (#Row).ord = typeLT Row by simp [Row])
  simpa [Row] using h

/-- The well-ordered Erdős-Dushnik-Miller partition theorem on the first
uncountable ordinal. An uncountable set with countable blue neighborhoods
yields an ω₁-long red clique by recursion. In the other case a nested
sequence of uncountable blue neighborhoods yields a countable blue clique. -/
theorem edm_on_rows (G : SimpleGraph Row) :
    (∃ e : ℕ ↪ Row, ∀ i j, i ≠ j → ¬ G.Adj (e i) (e j)) ∨
    (∃ e : Row ↪ Row, ∀ i j, i ≠ j → G.Adj (e i) (e j)) := by
  classical
  let blue (a b : Row) := a ≠ b ∧ ¬ G.Adj a b
  by_cases thin : ∃ Y : Set Row, ¬Y.Countable ∧ ∀ a ∈ Y, {b ∈ Y | blue a b}.Countable
  · obtain ⟨Y,big,allowed⟩ := thin
    have fresh (i : Row) (prev : ∀ j : Row, j < i → Y) :
        ∃ z : Y, ∀ j (h : j < i), (prev j h).val ≠ z.val ∧ G.Adj (prev j h).val z.val := by
      let _ := countable_predecessors i
      let bad (j : Iio i) : Set Row := {b ∈ Y | blue (prev j j.property).val b} ∪ {(prev j j.property).val}
      have count (j : Iio i) : (bad j).Countable :=
        (allowed _ (prev j j.property).property).union (countable_singleton _)
      have outside : ∃ z ∈ Y, z ∉ ⋃ j,bad j := by
        by_contra! all
        exact big ((Set.countable_iUnion count).mono all)
      obtain ⟨z,hz,good⟩ := outside
      refine ⟨⟨z,hz⟩,fun j hj => ?_⟩
      have no : z ∉ bad ⟨j,hj⟩ := fun h => good (mem_iUnion.2 ⟨⟨j,hj⟩,h⟩)
      have ne : (prev j hj).val ≠ z := fun e => no (Or.inr e.symm)
      exact ⟨ne,by by_contra miss; exact no (Or.inl ⟨hz,ne,miss⟩)⟩
    choose step ok using fresh
    let e : Row → Y := wellFounded_lt.fix step
    have forward {i j : Row} (ij : i<j) : (e i).val ≠ (e j).val ∧ G.Adj (e i).val (e j).val := by
      have recurrence : e j = step j (fun k _ => e k) := WellFounded.fix_eq .. 
      rw [recurrence]; exact ok j (fun k _ => e k) i ij
    have inj : Function.Injective (fun j => (e j).val) := by
      intro i j eq
      rcases lt_trichotomy i j with lt | h | gt
      · exact (False.elim ((forward lt).1 eq))
      · exact h
      · exact (False.elim ((forward gt).1 eq.symm))
    exact Or.inr ⟨⟨_,inj⟩,fun i j ne => (lt_or_gt_of_ne ne).elim (fun h => (forward h).2) (fun h => (forward h).2.symm)⟩
  · let State := {Y : Set Row // ¬ Y.Countable}
    have find (Y : State) : ∃ a ∈ Y.val, ¬{b ∈ Y.val | blue a b}.Countable := by
      by_contra! all
      exact thin ⟨Y.val,Y.property,all⟩
    choose pick mem big using find
    let initial : State := ⟨univ,cofinal_uncountable IsCofinal.univ⟩
    let next (Y : State) : State := ⟨{b ∈ Y.val | blue (pick Y) b},big Y⟩
    let states : ℕ → State := Nat.rec initial (fun _ y => next y)
    let e (n : ℕ) := pick (states n)
    have down (n : ℕ) : (states (n+1)).val ⊆ (states n).val := fun _ h => h.1
    have nested {i j : ℕ} (le : i≤j) : (states j).val ⊆ (states i).val := by
      induction le with
      | refl => exact Subset.rfl
      | step _ ih => exact (down _).trans ih
    have forward {i j : ℕ} (lt : i<j) : blue (e i) (e j) :=
      (show e j ∈ (states (i+1)).val from nested lt (mem (states j))).2
    have inj : Function.Injective e := by
      intro i j eq
      rcases lt_trichotomy i j with lt | h | gt
      · exact (False.elim ((forward lt).1 eq))
      · exact h
      · exact (False.elim ((forward gt).1 eq.symm))
    exact Or.inl ⟨⟨e,inj⟩,fun i j ne => (lt_or_gt_of_ne ne).elim (fun h => (forward h).2)
      (fun h => fun edge => (forward h).2 edge.symm)⟩

variable {P : Type u} [Group P] {A : Type v} [MulAction (Row→P) A]

/-- A countable independent sequence or an ω₁-clique with one common support,
as required for their injections to belong to the permutation model. -/
def SupportedEDM (X : Set A) (G : SimpleGraph X) : Prop :=
  (∃ (e : ℕ ↪ X) (D : Set Row), Small D ∧ (∀ i, Holds (P := P) D (e i).val) ∧
    ∀ i j, i≠j → ¬ G.Adj (e i) (e j)) ∨
  (∃ (e : Row ↪ X) (D : Set Row), Small D ∧ (∀ i, Holds (P := P) D (e i).val) ∧
    ∀ i j, i≠j → G.Adj (e i) (e j))

theorem edm_from_comparison (X : Set A) (G : SimpleGraph X) (compare : SetComparison (P := P) X)
    (large : ¬∃ (_ : X ↪ ℕ) (D : Set Row), Small D ∧ ∀ a ∈ X, Holds (P := P) D a) :
    SupportedEDM (P := P) X G := by
  obtain ⟨e,D,small,fixed⟩ := compare.resolve_left large
  rcases edm_on_rows (G.comap e) with ⟨f,h⟩ | ⟨f,h⟩
  · exact Or.inl ⟨f.trans e,D,small,fun i => fixed (f i),h⟩
  · exact Or.inr ⟨f.trans e,D,small,fun i => fixed (f i),h⟩

/-- The graph principle on all internally uncountable supported carriers in
the same five-letter model in which the indexed row families lack selectors. -/
theorem five_edm {Y : Type v} [MulAction (Row→FiveGroup) Y] (X : Set Y) (G : SimpleGraph X)
    (setSym : SymmetricSet (P := FiveGroup) X) (points : SymmetricPoints (P := FiveGroup) X)
    (large : ¬∃ (_ : X ↪ ℕ) (D : Set Row), Small D ∧ ∀ a ∈ X, Holds (P := FiveGroup) D a) :
    SupportedEDM (P := FiveGroup) X G := edm_from_comparison X G (five_comparison X setSym points) large

end ChoiceOmegaOne
