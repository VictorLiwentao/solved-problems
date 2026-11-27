module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Push
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace ColourProbe

open SimpleGraph

/-- A single recoloring with changed coordinate `i`. -/
def OneAt {V C : Type*} (i : V) (p q : V → C) : Prop :=
  p i ≠ q i ∧ ∀ j, j ≠ i → p j = q j

theorem OneAt.symm {V C : Type*} {i : V} {p q : V → C} (h : OneAt i p q) : OneAt i q p :=
  ⟨h.1.symm,fun j hj => (h.2 j hj).symm⟩

def hamming (V C : Type*) : SimpleGraph (V → C) where
  Adj p q := ∃ i, OneAt i p q
  symm := ⟨by rintro _ _ ⟨i,hi⟩; exact ⟨i,hi.symm⟩⟩
  loopless := ⟨fun _ ⟨_,h⟩ => h.1 rfl⟩

def Proper {V C : Type*} (G : SimpleGraph V) (p : V → C) : Prop :=
  ∀ ⦃i j⦄, G.Adj i j → p i ≠ p j

abbrev Coloring {V : Type*} (G : SimpleGraph V) (C : Type*) := {p : V → C // Proper G p}

noncomputable instance {V C : Type*} [Fintype V] [Fintype C] (G : SimpleGraph V) : Fintype (Coloring G C) := by
  classical unfold Coloring; infer_instance

def coloringGraph {V : Type*} (G : SimpleGraph V) (C : Type*) : SimpleGraph (Coloring G C) :=
  (hamming V C).comap Subtype.val

theorem neighbor_directions {V C : Type*} {i j : V} {p q r : V → C}
    (hq : OneAt i p q) (hr : OneAt j p r) (hne : q ≠ r) : (hamming V C).Adj q r ↔ i=j := by
  constructor
  · rintro ⟨k,hk⟩
    by_contra hij
    have hi : q i ≠ r i := fun h => hq.1 ((hr.2 i hij).trans h.symm)
    have hj : q j ≠ r j := fun h => hr.1 ((hq.2 j (Ne.symm hij)).trans h)
    have ik : i=k := by by_contra h; exact hi (hk.2 i h)
    have jk : j=k := by by_contra h; exact hj (hk.2 j h)
    exact hij (ik.trans jk.symm)
  · rintro rfl
    have other (a : V) (ha : a ≠ i) : q a = r a := (hq.2 a ha).symm.trans (hr.2 a ha)
    refine ⟨i,?_,other⟩
    intro h
    exact hne (funext fun a => by by_cases ha : a=i; exact ha ▸ h; exact other a ha)

/-- The two common neighbors of opposite endpoints of a two-coordinate
diagonal are its two rectangular corners. -/
theorem opposite_corner {V C : Type*} {i j : V} (hij : i ≠ j) {p q r t : V → C}
    (hq : OneAt i p q) (hr : OneAt j p r) (htq : (hamming V C).Adj q t)
    (htr : (hamming V C).Adj r t) (ht : t ≠ p) : t i = q i ∧ t j = r j := by
  obtain ⟨a,ha⟩ := htq
  obtain ⟨b,hb⟩ := htr
  have prove {i j a b} {p q r t : V → C} (hij : i ≠ j) (hq : OneAt i p q) (hr : OneAt j p r)
      (ha : OneAt a q t) (hb : OneAt b r t) (ht : t ≠ p) : t i = q i := by
    by_contra hne
    have ia : i=a := by by_contra h; exact hne (ha.2 i h).symm
    subst a
    have tj : t j = p j := (ha.2 j hij.symm).symm.trans (hq.2 j (Ne.symm hij)).symm
    have jb : j=b := by
      by_contra h
      exact hr.1 (tj.symm.trans (hb.2 j h).symm)
    subst b
    apply ht
    funext x
    by_cases hx : x=i
    · subst x
      exact (hb.2 i hij).symm.trans (hr.2 i hij).symm
    · exact (ha.2 x hx).symm.trans (hq.2 x hx).symm
  exact ⟨prove hij hq hr ha hb ht,prove hij.symm hr hq hb ha ht⟩

end ColourProbe

namespace ColourProbe

open SimpleGraph

abbrev Palette (V : Type*) := V ⊕ Option V

/-- The support consists of at most two changed coordinates. They are required
to be nonadjacent so that their fresh colors may coincide. -/
def Allowed {V : Type*} (G : SimpleGraph V) := {S : Finset V // S.card ≤ 2 ∧ ∀ i ∈ S, ∀ j ∈ S, ¬G.Adj i j}

def Row {V : Type*} (G : SimpleGraph V) := (S : Allowed G) × (S.val → Option V)

noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype (Allowed G) := by
  classical unfold Allowed; infer_instance

noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype (Row G) := by
  classical unfold Row; infer_instance

noncomputable def word {V : Type*} {G : SimpleGraph V} (r : Row G) (i : V) : Palette V := by
  classical exact if h : i ∈ r.1.val then Sum.inr (r.2 ⟨i,h⟩) else Sum.inl i

theorem word_in {V : Type*} {G : SimpleGraph V} (r : Row G) (i : V) (h : i ∈ r.1.val) :
    word r i = Sum.inr (r.2 ⟨i,h⟩) := by classical simp [word,h]

theorem word_out {V : Type*} {G : SimpleGraph V} (r : Row G) (i : V) (h : i ∉ r.1.val) :
    word r i = Sum.inl i := by classical simp [word,h]

theorem word_injective {V : Type*} (G : SimpleGraph V) : Function.Injective (word (G := G)) := by
  rintro ⟨⟨S,hs⟩,v⟩ ⟨⟨T,ht⟩,w⟩ h
  classical
  have st : S = T := by
    ext i
    have hi := congrFun h i
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all [word]
  subst T
  congr 1
  funext i
  have hi := congrFun h i.val
  simpa [word,i.property] using hi

theorem proper_word {V : Type*} {G : SimpleGraph V} (r : Row G) : Proper G (word r) := by
  intro i j hij
  classical
  by_cases hi : i ∈ r.1.val <;> by_cases hj : j ∈ r.1.val
  · exact False.elim (r.1.property.2 i hi j hj hij)
  · simp [word,hi,hj]
  · simp [word,hi,hj]
  · simpa [word,hi,hj] using hij.ne

noncomputable def probe {V : Type*} (G : SimpleGraph V) : SimpleGraph (Row G) :=
  (hamming V (Palette V)).comap word

noncomputable def rainbow {V : Type*} (G : SimpleGraph V) : Row G :=
  ⟨⟨∅,by simp⟩,fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

@[simp] theorem word_rainbow {V : Type*} (G : SimpleGraph V) (i : V) : word (rainbow G) i = Sum.inl i := by
  apply word_out
  simp [rainbow]

noncomputable def single {V : Type*} (G : SimpleGraph V) (i : V) (a : Option V) : Row G := by
  classical exact ⟨⟨{i},by simp⟩,fun _ => a⟩

@[simp] theorem word_single_at {V : Type*} (G : SimpleGraph V) (i : V) (a : Option V) :
    word (single G i a) i = Sum.inr a := by classical simp [word,single]

theorem word_single_other {V : Type*} (G : SimpleGraph V) (i j : V) (a : Option V) (h : j ≠ i) :
    word (single G i a) j = Sum.inl j := by classical simp [word,single,h]

theorem single_change {V : Type*} (G : SimpleGraph V) (i : V) (a : Option V) :
    OneAt i (word (rainbow G)) (word (single G i a)) :=
  ⟨by simp,fun j hj => by simp [word_single_other G i j a hj]⟩

theorem single_injective {V : Type*} (G : SimpleGraph V) (i : V) : Function.Injective (single G i) := by
  intro a b h
  have eq := congrArg (fun r => word r i) h
  simpa using eq

theorem single_distinct {V : Type*} (G : SimpleGraph V) {i j : V} (hij : i ≠ j) (a b : Option V) :
    single G i a ≠ single G j b := by
  intro h
  have eq := congrArg (fun r => word r i) h
  simp [word_single_other G j i b hij] at eq

noncomputable def double {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : Row G := by
  classical
  refine ⟨⟨{i,j},?_,?_⟩,fun k => if k.val=i then a else b⟩
  · simp [hij]
  · intro x hx y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | exact G.loopless.irrefl _ | exact hn | exact fun h => hn h.symm

theorem double_left {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : OneAt j (word (single G i a)) (word (double G i j hij hn a b)) := by
  classical
  refine ⟨by simp [word,single,double,hij.symm],?_⟩
  intro x hx
  by_cases h : x=i <;> simp [word,single,double,h,hx]

theorem double_right {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : OneAt i (word (single G j b)) (word (double G i j hij hn a b)) := by
  classical
  refine ⟨by simp [word,single,double,hij],?_⟩
  intro x hx
  by_cases h : x=j <;> simp [word,single,double,h,hx,hij.symm]

theorem double_ne_rainbow {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : double G i j hij hn a b ≠ rainbow G := by
  intro h
  have hi := congrArg (fun r => word r i) h
  classical simp [word,double,rainbow] at hi

noncomputable def ownEmbedding {V : Type*} (G : SimpleGraph V) :
    probe G ↪g coloringGraph G (Palette V) where
  toFun r := ⟨word r,proper_word r⟩
  inj' _ _ h := word_injective G (congrArg Subtype.val h)
  map_rel_iff' := Iff.rfl

end ColourProbe

namespace ColourProbe

open SimpleGraph

noncomputable def relabel {V C D : Type*} (G : SimpleGraph V) (f : C ↪ D) :
    coloringGraph G C ↪g coloringGraph G D where
  toFun p := ⟨f ∘ p.val,fun _ _ h => f.injective.ne (p.property h)⟩
  inj' p q h := Subtype.ext (funext fun i => f.injective (congrFun (congrArg Subtype.val h) i))
  map_rel_iff' := by
    intro p q
    constructor <;> rintro ⟨i,hi,hrest⟩
    · exact ⟨i,fun h => hi (congrArg f h),fun j hj => f.injective (hrest j hj)⟩
    · exact ⟨i,f.injective.ne hi,fun j hj => congrArg f (hrest j hj)⟩

variable {V W C : Type*} {G : SimpleGraph V} {K : SimpleGraph W} (e : probe G ↪g coloringGraph K C)

theorem edge_direction (i : V) (a : Option V) : ∃ j : W, OneAt j (e (rainbow G)).val (e (single G i a)).val :=
  e.map_adj_iff.mpr ⟨i,single_change G i a⟩

noncomputable def direction (i : V) : W := (edge_direction e i none).choose

theorem anchor_direction (i : V) : OneAt (direction e i) (e (rainbow G)).val (e (single G i none)).val :=
  (edge_direction e i none).choose_spec

theorem all_directions (i : V) (a : Option V) :
    OneAt (direction e i) (e (rainbow G)).val (e (single G i a)).val := by
  by_cases h : none = a
  · subst a
    exact anchor_direction e i
  obtain ⟨j,hj⟩ := edge_direction e i a
  have hne := (single_injective G i).ne h
  have hwords := (word_injective G).ne hne
  have hadj : (probe G).Adj (single G i none) (single G i a) :=
    (neighbor_directions (single_change G i none) (single_change G i a) hwords).mpr rfl
  have outNe : (e (single G i none)).val ≠ (e (single G i a)).val := fun h => hne (e.injective (Subtype.ext h))
  have hj' := (neighbor_directions (anchor_direction e i) hj outNe).mp (e.map_adj_iff.mpr hadj)
  rwa [hj']

theorem direction_injective : Function.Injective (direction e) := by
  intro i j h
  by_contra hne
  have hrs := single_distinct G hne none none
  have outNe : (e (single G i none)).val ≠ (e (single G j none)).val := fun h => hrs (e.injective (Subtype.ext h))
  have hadj := (neighbor_directions (anchor_direction e i) (anchor_direction e j) outNe).mpr h
  exact hne ((neighbor_directions (single_change G i none) (single_change G j none) ((word_injective G).ne hrs)).mp
    (e.map_adj_iff.mp hadj))

noncomputable def changedColor (i : V) (a : Option V) : C := (e (single G i a)).val (direction e i)

theorem changed_injective (i : V) : Function.Injective (changedColor e i) := by
  intro a b h
  apply single_injective G i
  apply e.injective
  apply Subtype.ext
  funext j
  by_cases hji : j = direction e i
  · subst j
    exact h
  · exact ((all_directions e i a).2 j hji).symm.trans ((all_directions e i b).2 j hji)

theorem shared_color [Fintype V] [Fintype C] (hc : Fintype.card C < 2 * Fintype.card (Option V)) (i j : V) :
    ∃ a b, changedColor e i a = changedColor e j b := by
  classical
  by_contra! no
  let f : Option V ⊕ Option V → C := Sum.elim (changedColor e i) (changedColor e j)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (changed_injective e i h)
    · exact False.elim (no a b h)
    · exact False.elim (no b a h.symm)
    · exact congrArg Sum.inr (changed_injective e j h)
  have h := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_sum] at h
  omega

/-- Every nonedge of the target remains a nonedge on the recovered host
coordinates, because the two rows can be made to share a fresh output color. -/
theorem reflect_edges [Fintype V] [Fintype C] (hc : Fintype.card C < 2 * Fintype.card (Option V))
    {i j : V} (hK : K.Adj (direction e i) (direction e j)) : G.Adj i j := by
  classical
  have hij : i ≠ j := fun h => hK.ne (congrArg _ h)
  by_contra hG
  obtain ⟨a,b,hab⟩ := shared_color e hc i j
  let d := double G i j hij hG a b
  have dbase : (e d).val ≠ (e (rainbow G)).val := fun h => double_ne_rainbow G i j hij hG a b (e.injective (Subtype.ext h))
  have hdq : (coloringGraph K C).Adj (e (single G i a)) (e d) := e.map_adj_iff.mpr ⟨j,double_left ..⟩
  have hdr : (coloringGraph K C).Adj (e (single G j b)) (e d) := e.map_adj_iff.mpr ⟨i,double_right ..⟩
  obtain ⟨hi,hj⟩ := opposite_corner ((direction_injective e).ne hij) (all_directions e i a)
    (all_directions e j b) hdq hdr dbase
  exact (e d).property hK (hi.trans (hab.trans hj.symm))

end ColourProbe

namespace ColourProbe

open SimpleGraph

/-- Copies are the actual vertex subsets inducing a graph isomorphic to the
probe, without an ordering of their vertices. -/
def Copies {U W : Type*} (H : SimpleGraph U) (G : SimpleGraph W) :=
  {S : Set W // Nonempty (H ≃g G.induce S)}

noncomputable def inducedCount {U W : Type*} (H : SimpleGraph U) (G : SimpleGraph W) := Nat.card (Copies H G)

noncomputable def copyRange {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W} (e : H ↪g G) : Copies H G :=
  ⟨Set.range e,⟨e.isoInduceRange⟩⟩

private noncomputable def intoSubset {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W} (S : Copies H G)
    (e : {e : H ↪g G // copyRange e = S}) : H ≃g G.induce S.val := by
  have range_eq : Set.range e.val = S.val := congrArg Subtype.val e.2
  let f (x : U) : S.val := ⟨e.val x,range_eq ▸ Set.mem_range_self x⟩
  have inj : Function.Injective f := fun _ _ h => e.val.injective (congrArg Subtype.val h)
  have sur : Function.Surjective f := by
    intro y
    have hy : y.val ∈ Set.range e.val := by rw [range_eq]; exact y.property
    obtain ⟨x,hx⟩ := hy
    exact ⟨x,Subtype.ext hx⟩
  exact ⟨Equiv.ofBijective f ⟨inj,sur⟩,e.val.map_rel_iff⟩

private noncomputable def fiberEquiv {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W} (S : Copies H G) :
    {e : H ↪g G // copyRange e = S} ≃ (H ≃g G.induce S.val) where
  toFun := intoSubset S
  invFun e := ⟨(SimpleGraph.Embedding.induce S.val).comp e.toEmbedding,by
    apply Subtype.ext
    ext y
    change (∃ x, (e x).val=y) ↔ y ∈ S.val
    constructor
    · rintro ⟨x,rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩⟩
  left_inv _ := by apply Subtype.ext; ext; rfl
  right_inv _ := by ext; rfl

private noncomputable def autEquiv {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W}
    (S : Copies H G) : (H ≃g G.induce S.val) ≃ (H ≃g H) where
  toFun f := f.trans S.property.some.symm
  invFun f := f.trans S.property.some
  left_inv f := by ext; simp
  right_inv f := by ext; simp

theorem embeddings_count {U W : Type*} [Fintype U] [Fintype W] (H : SimpleGraph U) (G : SimpleGraph W) :
    Nat.card (H ↪g G) = inducedCount H G * Nat.card (H ≃g H) := by
  classical
  let _ : Fintype (Copies H G) := by unfold Copies; infer_instance
  let _ := Fintype.ofFinite (H ↪g G)
  have _ : Finite (H ≃g H) := Finite.of_injective (fun e : H ≃g H => (e : U → U)) DFunLike.coe_injective
  let _ := Fintype.ofFinite (H ≃g H)
  let _ (s : Copies H G) := Fintype.ofFinite {e : H ↪g G // copyRange e = s}
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (@copyRange _ _ H G)),Nat.card_eq_fintype_card,Fintype.card_sigma]
  have h (s : Copies H G) : Fintype.card {e : H ↪g G // copyRange e = s} = Nat.card (H ≃g H) :=
    (Fintype.card_congr ((fiberEquiv s).trans (autEquiv s))).trans Nat.card_eq_fintype_card.symm
  simp [h,inducedCount,Nat.card_eq_fintype_card]

theorem nonempty_of_count_pos {U W : Type*} [Fintype U] [Fintype W] {H : SimpleGraph U} {G : SimpleGraph W}
    (h : 0 < inducedCount H G) : Nonempty (H ↪g G) := by
  classical
  let _ : Fintype (Copies H G) := by unfold Copies; infer_instance
  obtain ⟨S⟩ := Nat.card_pos_iff.mp h |>.1
  exact ⟨(SimpleGraph.Embedding.induce S.val).comp S.property.some.toEmbedding⟩

theorem count_pos_of_embedding {U W : Type*} [Fintype W] {H : SimpleGraph U} {G : SimpleGraph W}
    (e : H ↪g G) : 0 < inducedCount H G := by
  classical
  let _ : Fintype (Copies H G) := by unfold Copies; infer_instance
  exact Nat.card_pos_iff.mpr ⟨⟨copyRange e⟩,inferInstance⟩

end ColourProbe

namespace ColourProbe

open SimpleGraph

noncomputable def extendWord {V W C : Type*} (d : V ↪ W) (p : V → C) (s : W → C) (w : W) : C := by
  classical exact if h : w ∈ Set.range d then p h.choose else s w

theorem extend_at {V W C : Type*} (d : V ↪ W) (p : V → C) (s : W → C) (v : V) :
    extendWord d p s (d v) = p v := by
  classical
  have hr : d v ∈ Set.range d := Set.mem_range_self _
  simp only [extendWord,dite_eq_left hr]
  exact congrArg p (d.injective hr.choose_spec)

theorem extend_off {V W C : Type*} (d : V ↪ W) (p : V → C) (s : W → C) {w : W} (hw : w ∉ Set.range d) :
    extendWord d p s w = s w := by classical simp [extendWord,hw]

theorem extend_adj_iff {V W C : Type*} (d : V ↪ W) (p q : V → C) (s : W → C) :
    (hamming W C).Adj (extendWord d p s) (extendWord d q s) ↔ (hamming V C).Adj p q := by
  classical
  constructor
  · rintro ⟨w,hw,ho⟩
    by_cases hmem : w ∈ Set.range d
    · obtain ⟨i,rfl⟩ := hmem
      refine ⟨i,by simpa only [extend_at] using hw,fun j hj => ?_⟩
      simpa only [extend_at] using ho (d j) (d.injective.ne hj)
    · exact False.elim (hw (by rw [extend_off d p s hmem,extend_off d q s hmem]))
  · rintro ⟨i,hi,ho⟩
    refine ⟨d i,by simpa only [extend_at] using hi,fun w hw => ?_⟩
    by_cases hmem : w ∈ Set.range d
    · obtain ⟨j,rfl⟩ := hmem
      simpa only [extend_at] using ho j (fun h => hw (congrArg d h))
    · rw [extend_off d p s hmem,extend_off d q s hmem]

theorem extend_proper {V W C : Type*} {G : SimpleGraph V} {K : SimpleGraph W} (d : V ↪ W)
    (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) {p : V → C} (hp : Proper G p)
    (s : W ↪ C) (free : ∀ i w, p i ≠ s w) : Proper K (extendWord d p s) := by
  classical
  intro w w' he
  by_cases h : w ∈ Set.range d <;> by_cases h' : w' ∈ Set.range d
  · obtain ⟨i,rfl⟩ := h
    obtain ⟨j,rfl⟩ := h'
    rw [extend_at,extend_at]
    exact hp (href i j he)
  · obtain ⟨i,rfl⟩ := h
    rw [extend_at,extend_off _ _ _ h']
    exact free i _
  · obtain ⟨j,rfl⟩ := h'
    rw [extend_off _ _ _ h,extend_at]
    exact (free j _).symm
  · rw [extend_off _ _ _ h,extend_off _ _ _ h']
    exact s.injective.ne he.ne

noncomputable def liftEmbedding {U V W C : Type*} {H : SimpleGraph U} {G : SimpleGraph V} {K : SimpleGraph W}
    (d : V ↪ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) (e : H ↪g coloringGraph G C)
    (s : W ↪ C) (free : ∀ u i w, (e u).val i ≠ s w) : H ↪g coloringGraph K C where
  toFun u := ⟨extendWord d (e u).val s,extend_proper d href (e u).property s (free u)⟩
  inj' x y h := by
    apply e.injective
    apply Subtype.ext
    funext i
    simpa only [extend_at] using congrFun (congrArg Subtype.val h) (d i)
  map_rel_iff' := (extend_adj_iff ..).trans e.map_adj_iff

noncomputable def used {U V C : Type*} [Fintype U] [Fintype V] {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g coloringGraph G C) : Finset C := by
  classical exact Finset.univ.image fun p : U × V => (e p.1).val p.2

theorem used_mem {U V C : Type*} [Fintype U] [Fintype V] {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g coloringGraph G C) (u : U) (i : V) : (e u).val i ∈ used e := by
  classical exact Finset.mem_image.mpr ⟨(u,i),Finset.mem_univ _,rfl⟩

noncomputable def reserve {U V W C : Type*} [Fintype U] [Fintype V] [Fintype W] [Fintype C]
    {H : SimpleGraph U} {G : SimpleGraph V} (e : H ↪g coloringGraph G C)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C) :
    (W × Bool) ↪ {c : C // c ∉ used e} := by
  classical
  apply Classical.choice
  apply (Function.Embedding.nonempty_iff_card_le).mpr
  have bound : (used e).card ≤ Fintype.card U * Fintype.card V := by
    unfold used
    exact Finset.card_image_le.trans (by simp)
  rw [Fintype.card_prod,Fintype.card_bool,Fintype.card_subtype_compl]
  simpa using (show Fintype.card W * 2 ≤ Fintype.card C - (used e).card by omega)

end ColourProbe

namespace ColourProbe

open SimpleGraph

variable {U V W C : Type*} [Fintype U] [Fintype V] [Fintype W] [Fintype C]
  {H : SimpleGraph U} {G : SimpleGraph V} {K : SimpleGraph W}

noncomputable def tag (e : H ↪g coloringGraph G C)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C) (b : Bool) : W ↪ C where
  toFun w := (reserve e hc (w,b)).val
  inj' _ _ h := congrArg Prod.fst ((reserve e hc).injective (Subtype.ext h))

theorem unused (e : H ↪g coloringGraph G C)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C) (b : Bool)
    (u : U) (i : V) (w : W) : (e u).val i ≠ tag e hc b w := by
  intro h
  change (e u).val i = (reserve e hc (w,b)).val at h
  apply (reserve e hc (w,b)).property
  rw [← h]
  exact used_mem e u i

/-- An additional host coordinate strictly increases the number of labeled
embeddings at a sufficiently large palette. Restriction to the old coordinates
recovers the entire embedding, and at the additional coordinate a bit is stored
using colors absent from all its rows. -/
theorem extra_coordinate (d : V ↪ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j)
    (w : W) (hw : w ∉ Set.range d) (u : U)
    (hc : Fintype.card U * Fintype.card V + Fintype.card W * 2 ≤ Fintype.card C)
    (existsEmbedding : Nonempty (H ↪g coloringGraph G C)) :
    Nat.card (H ↪g coloringGraph G C) < Nat.card (H ↪g coloringGraph K C) := by
  classical
  let _ := Fintype.ofFinite (H ↪g coloringGraph G C)
  let _ := Fintype.ofFinite (H ↪g coloringGraph K C)
  let F (p : (H ↪g coloringGraph G C) × Bool) := liftEmbedding d href p.1 (tag p.1 hc p.2) (unused p.1 hc p.2)
  have hinj : Function.Injective F := by
    rintro ⟨f,b⟩ ⟨g,c⟩ he
    have eqAt (u' : U) (w' : W) : extendWord d (f u').val (tag f hc b) w' =
        extendWord d (g u').val (tag g hc c) w' :=
      congrArg (fun (E : H ↪g coloringGraph K C) => (E u').val w') he
    have hfg : f=g := by
      ext u' i
      simpa only [extend_at] using eqAt u' (d i)
    subst g
    have hb : (reserve f hc (w,b)).val = (reserve f hc (w,c)).val := by
      change tag f hc b w = tag f hc c w
      simpa only [extend_off _ _ _ hw] using eqAt u w
    exact Prod.ext rfl (congrArg (fun p : W × Bool => p.2) ((reserve f hc).injective (Subtype.ext hb)))
  have bound := Fintype.card_le_of_injective F hinj
  have pos := Fintype.card_pos (α := H ↪g coloringGraph G C)
  rw [Fintype.card_prod,Fintype.card_bool] at bound
  simp only [Nat.card_eq_fintype_card]
  omega

theorem order_surjective {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (K : SimpleGraph W)
    (d : V ↪ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j)
    (counts : ∀ k, inducedCount (probe G) (coloringGraph G (Fin k)) = inducedCount (probe G) (coloringGraph K (Fin k))) :
    Function.Surjective d := by
  classical
  change ∀ w, ∃ i, d i = w
  by_contra! h
  obtain ⟨w,hw⟩ := h
  let k := Fintype.card (Row G) * Fintype.card V + Fintype.card W * 2 + Fintype.card (Palette V)
  have hc : Fintype.card (Row G)*Fintype.card V + Fintype.card W*2 ≤ Fintype.card (Fin k) := by simp [k]
  have bounds : Fintype.card (Palette V) ≤ Fintype.card (Fin k) := by simp [k]
  let emb := (Function.Embedding.nonempty_iff_card_le.mpr bounds).some
  let own := (relabel G emb).comp (ownEmbedding G)
  have strict := extra_coordinate d href w (fun ⟨i,hi⟩ => hw i hi) (rainbow G) hc ⟨own⟩
  rw [embeddings_count,embeddings_count,counts k] at strict
  exact strict.false

end ColourProbe

namespace ColourProbe

open SimpleGraph

def transportWord {V W C D : Type*} (d : V ≃ W) (f : V → C ↪ D) (p : V → C) (w : W) : D :=
  f (d.symm w) (p (d.symm w))

@[simp] theorem transport_word_at {V W C D : Type*} (d : V ≃ W) (f : V → C ↪ D) (p : V → C) (i : V) :
    transportWord d f p (d i) = f i (p i) := by simp [transportWord]

def transportGraph {V W C D : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W) (f : V → C ↪ D)
    (legal : ∀ p : Coloring G C, Proper K (transportWord d f p.val)) :
    coloringGraph G C ↪g coloringGraph K D where
  toFun p := ⟨transportWord d f p.val,legal p⟩
  inj' p q h := by
    apply Subtype.ext
    funext i
    apply (f i).injective
    simpa only [transport_word_at] using congrFun (congrArg Subtype.val h) (d i)
  map_rel_iff' := by
    intro p q
    change (hamming W D).Adj (transportWord d f p.val) (transportWord d f q.val) ↔ (hamming V C).Adj p.val q.val
    constructor
    · rintro ⟨w,hw,ho⟩
      obtain ⟨i,rfl⟩ := d.surjective w
      refine ⟨i,?_,fun j hj => (f j).injective ?_⟩
      · intro h
        exact hw (by simp [transport_word_at,h])
      · simpa only [transport_word_at] using ho (d j) (d.injective.ne hj)
    · rintro ⟨i,hi,ho⟩
      refine ⟨d i,?_,?_⟩
      · simpa only [transport_word_at] using (f i).injective.ne hi
      · intro w hw
        obtain ⟨j,rfl⟩ := d.surjective w
        simpa only [transport_word_at] using congrArg (f j) (ho j (fun h => hw (congrArg d h)))

def keepGraph {V W C : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W)
    (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) :
    coloringGraph G C ↪g coloringGraph K C := by
  apply transportGraph G K d (fun _ => Function.Embedding.refl C)
  intro p w w' h
  obtain ⟨i,rfl⟩ := d.surjective w
  obtain ⟨j,rfl⟩ := d.surjective w'
  rw [transport_word_at,transport_word_at]
  exact p.property (href i j h)

@[simp] theorem keep_at {V W C : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W)
    (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) (p : Coloring G C) (i : V) :
    (keepGraph G K d href p).val (d i) = p.val i := by
  exact transport_word_at d (fun _ => Function.Embedding.refl C) p.val i

def Token (V : Type*) := Option (V × Palette V)

noncomputable instance {V : Type*} [Fintype V] : Fintype (Token V) := by unfold Token; infer_instance

/-- Each coordinate has a disjoint palette except for the two base-color
entries deliberately merged into the common symbol `none`. -/
noncomputable def encode {V : Type*} (x y i : V) : Palette V ↪ Token V := by
  classical
  let pred (a : Palette V) := (i=x ∨ i=y) ∧ a=Sum.inl i
  refine ⟨fun a => if pred a then none else some (i,a),?_⟩
  intro a b h
  change (if pred a then none else some (i,a)) = (if pred b then none else some (i,b)) at h
  split_ifs at h with ha hb hb <;> first | exact ha.2.trans hb.2.symm | exact congrArg Prod.snd (Option.some.inj h)

theorem encoding_proper {V W : Type*} (K : SimpleGraph W) (d : V ≃ W) (x y : V) (hxy : ¬K.Adj (d x) (d y))
    (p : V → Palette V) : Proper K (transportWord d (encode x y) p) := by
  classical
  intro w w' he
  obtain ⟨i,rfl⟩ := d.surjective w
  obtain ⟨j,rfl⟩ := d.surjective w'
  have hne : i ≠ j := fun h => he.ne (congrArg d h)
  rw [transport_word_at,transport_word_at]
  change (if (i=x ∨ i=y) ∧ p i=Sum.inl i then none else some (i,p i)) ≠
    (if (j=x ∨ j=y) ∧ p j=Sum.inl j then none else some (j,p j))
  split_ifs with hi hj hj
  · rcases hi.1 with rfl | rfl <;> rcases hj.1 with rfl | rfl <;>
      first | exact False.elim (hne rfl) | exact False.elim (hxy he) | exact False.elim (hxy he.symm)
  · simp
  · simp
  · exact fun h => hne (congrArg Prod.fst (Option.some.inj h))

noncomputable def merged {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W) (x y : V)
    (hxy : ¬K.Adj (d x) (d y)) : probe G ↪g coloringGraph K (Token V) :=
  (transportGraph G K d (encode x y) (fun p => encoding_proper K d x y hxy p.val)).comp (ownEmbedding G)

theorem merged_at {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W) (x y : V)
    (hxy : ¬K.Adj (d x) (d y)) :
    (merged G K d x y hxy (rainbow G)).val (d x) = (merged G K d x y hxy (rainbow G)).val (d y) := by
  change transportWord d (encode x y) (word (rainbow G)) (d x) = transportWord d (encode x y) (word (rainbow G)) (d y)
  rw [transport_word_at,transport_word_at,word_rainbow,word_rainbow]
  classical simp [encode,Function.Embedding.coeFn_mk]
  rfl

end ColourProbe

namespace ColourProbe

open SimpleGraph

private theorem reach_rainbow {V : Type*} (G : SimpleGraph V) (r : Row G) : (probe G).Reachable r (rainbow G) := by
  classical
  by_cases hs : r.1.val.Nonempty
  · obtain ⟨i,hi⟩ := hs
    let T := r.1.val.erase i
    have hsub : T ⊆ r.1.val := Finset.erase_subset ..
    let q : Row G := ⟨⟨T,(Finset.card_le_card hsub).trans r.1.property.1,
      fun x hx y hy => r.1.property.2 x (hsub hx) y (hsub hy)⟩,fun x => r.2 ⟨x.val,hsub x.property⟩⟩
    have adj : (probe G).Adj r q := by
      refine ⟨i,?_,?_⟩
      · rw [word_in r i hi,word_out q i (by simp [q,T])]
        simp
      · intro j hji
        by_cases hj : j ∈ r.1.val
        · rw [word_in r j hj,word_in q j (by simp [q,T,hj,hji])]
        · rw [word_out r j hj,word_out q j (fun h => hj (hsub h))]
    exact adj.reachable.trans (reach_rainbow G q)
  · have empty := Finset.not_nonempty_iff_eq_empty.mp hs
    have h : r = rainbow G := word_injective G (funext (fun i => by rw [word_out r i (by simp [empty]),word_rainbow]))
    subst r
    exact Reachable.refl _
termination_by r.1.val.card
decreasing_by classical exact Finset.card_erase_lt_of_mem hi

theorem connected {V : Type*} (G : SimpleGraph V) : (probe G).Connected := by
  have _ : Nonempty (Row G) := ⟨rainbow G⟩
  exact ⟨fun v w => (reach_rainbow G v).trans (reach_rainbow G w).symm⟩

private theorem fixed_support_count {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Fintype.card {S : Allowed G // S.val.card = k} ≤ (Fintype.card V).choose k := by
  classical
  let f : {S : Allowed G // S.val.card = k} → ↥((Finset.univ : Finset V).powersetCard k) :=
    fun S => ⟨S.val.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,S.property⟩⟩
  have inj : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥((Finset.univ : Finset V).powersetCard k) => x.val) h))
  simpa [Finset.card_powersetCard] using Fintype.card_le_of_injective f inj

theorem card_bound {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype.card (Row G) ≤ 1 + Fintype.card V * (Fintype.card V+1) +
      (Fintype.card V).choose 2 * (Fintype.card V+1)^2 := by
  classical
  let n := Fintype.card V
  have count (k : ℕ) : ∑ S ∈ (Finset.univ : Finset (Allowed G)).filter (fun S => S.val.card = k),
      (n+1)^S.val.card ≤ n.choose k * (n+1)^k := by
    calc
      _ = Fintype.card {S : Allowed G // S.val.card = k} * (n+1)^k := by
        rw [Fintype.card_subtype]
        exact Finset.sum_const_nat fun S h => by rw [(Finset.mem_filter.mp h).2]
      _ ≤ _ := Nat.mul_le_mul_right _ (fixed_support_count G k)
  change Fintype.card ((S : Allowed G) × (S.val → Option V)) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun,Fintype.card_coe,Fintype.card_option]
  change ∑ S : Allowed G, (n+1)^S.val.card ≤ 1+n*(n+1)+n.choose 2*(n+1)^2
  have h₁ := count 0
  have h₂ := count 1
  have h₃ := count 2
  have hsum := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Allowed G))) (t := Finset.range 3)
    (g := fun S => S.val.card) (fun S _ => Finset.mem_range.mpr (by have := S.property.1; omega))
    (fun S => (n+1)^S.val.card)
  simp [Finset.sum_range_succ] at hsum h₁ h₂ h₃
  omega

end ColourProbe

namespace ColourProbe

open SimpleGraph

private theorem preserve_edges {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (K : SimpleGraph W)
    (d : V ≃ W) (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j)
    (counts : ∀ k, inducedCount (probe G) (coloringGraph G (Fin k)) = inducedCount (probe G) (coloringGraph K (Fin k)))
    (i j : V) (hij : G.Adj i j) : K.Adj (d i) (d j) := by
  classical
  by_contra hK
  let k := Fintype.card (Token V)
  let π := (Fintype.equivFin (Token V)).toEmbedding
  let _ := Fintype.ofFinite (probe G ↪g coloringGraph G (Fin k))
  let _ := Fintype.ofFinite (probe G ↪g coloringGraph K (Fin k))
  let F (f : probe G ↪g coloringGraph G (Fin k)) := (keepGraph G K d href).comp f
  have inj : Function.Injective F := by
    intro f g h
    exact DFunLike.ext _ _ fun a => (keepGraph G K d href).injective (congrArg (fun E : probe G ↪g coloringGraph K (Fin k) => E a) h)
  let extra := (relabel K π).comp (merged G K d i j hK)
  have hne (f) : F f ≠ extra := by
    intro same
    have hcol : (extra (rainbow G)).val (d i) = (extra (rainbow G)).val (d j) := congrArg π (merged_at G K d i j hK)
    rw [← same] at hcol
    change (keepGraph G K d href (f (rainbow G))).val (d i) = (keepGraph G K d href (f (rainbow G))).val (d j) at hcol
    exact (f (rainbow G)).property hij (by simpa only [keep_at] using hcol)
  have strict := Fintype.card_lt_of_injective_of_notMem F inj (b := extra) (fun ⟨f,h⟩ => hne f h)
  simp only [← Nat.card_eq_fintype_card,embeddings_count,counts k] at strict
  exact strict.false

/-- A single target-dependent induced-copy count distinguishes a graph from
every nonisomorphic finite simple graph, including hosts of different orders. -/
theorem reconstruct {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (K : SimpleGraph W)
    (counts : ∀ k, inducedCount (probe G) (coloringGraph G (Fin k)) =
      inducedCount (probe G) (coloringGraph K (Fin k))) : Nonempty (G ≃g K) := by
  classical
  let q := Fintype.card (Palette V)
  let π := (Fintype.equivFin (Palette V)).toEmbedding
  let own := (relabel G π).comp (ownEmbedding G)
  have pos := count_pos_of_embedding own
  rw [counts q] at pos
  obtain ⟨e⟩ := nonempty_of_count_pos pos
  have small : Fintype.card (Fin q) < 2 * Fintype.card (Option V) := by
    simp [q,Fintype.card_option,Fintype.card_sum]
    omega
  let d : V ↪ W := ⟨direction e,direction_injective e⟩
  have href (i j) (h : K.Adj (d i) (d j)) := reflect_edges e small h
  let iso := Equiv.ofBijective d ⟨d.injective,order_surjective G K d href counts⟩
  exact ⟨⟨iso,fun {i j} => ⟨href i j,preserve_edges G K iso href counts i j⟩⟩⟩

/-- The connected probe is one specific graph for each target. Its stated size
bound also covers the one-vertex probe for the empty target. -/
theorem one_colouring_probe {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ (U : Type) (_ : Fintype U) (H : SimpleGraph U), H.Connected ∧
      Fintype.card U ≤ 1 + Fintype.card V*(Fintype.card V+1) + (Fintype.card V).choose 2*(Fintype.card V+1)^2 ∧
      ∀ (W : Type) [Fintype W] (K : SimpleGraph W),
        (∀ k, inducedCount H (coloringGraph G (Fin k)) = inducedCount H (coloringGraph K (Fin k))) →
        Nonempty (G ≃g K) := by
  exact ⟨Row G,inferInstance,probe G,connected G,card_bound G,fun _ _ K => reconstruct G K⟩

end ColourProbe

namespace ColourProbe

open SimpleGraph

def UsesAll {U V C : Type*} {H : SimpleGraph U} {G : SimpleGraph V} (e : H ↪g coloringGraph G C) : Prop :=
  ∀ c : C, ∃ u i, (e u).val i = c

def Full {U V : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (C : Type*) :=
  {e : H ↪g coloringGraph G C // UsesAll e}

private theorem adj_coe {V C : Type*} (S : Finset C) (p q : V → S) :
    (hamming V S).Adj p q ↔ (hamming V C).Adj (Subtype.val ∘ p) (Subtype.val ∘ q) := by
  constructor <;> rintro ⟨i,h,rest⟩
  · exact ⟨i,fun he => h (Subtype.ext he),fun j hj => congrArg Subtype.val (rest j hj)⟩
  · exact ⟨i,fun he => h (congrArg Subtype.val he),fun j hj => Subtype.ext (rest j hj)⟩

noncomputable def restrictColors {U V C : Type*} {H : SimpleGraph U} {G : SimpleGraph V} (S : Finset C)
    (e : H ↪g coloringGraph G C) (h : ∀u i, (e u).val i ∈ S) : H ↪g coloringGraph G S where
  toFun u := ⟨fun i => ⟨(e u).val i,h u i⟩,fun i j hj eq => (e u).property hj (congrArg Subtype.val eq)⟩
  inj' u v eq := e.injective (Subtype.ext (funext fun i => congrArg (fun p : Coloring G S => (p.val i).val) eq))
  map_rel_iff' := by
    intro u v
    exact (adj_coe ..).trans e.map_adj_iff

noncomputable def includeColors {U V C : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (S : Finset C) (e : H ↪g coloringGraph G S) : H ↪g coloringGraph G C :=
  (relabel G ⟨Subtype.val,Subtype.val_injective⟩).comp e

theorem membership_used {U V C : Type*} [Fintype U] [Fintype V] {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g coloringGraph G C) (c : C) : c ∈ used e ↔ ∃ u i, (e u).val i = c := by
  classical simp [used]

noncomputable def usedFiber {U V C : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V)
    (S : Finset C) : {e : H ↪g coloringGraph G C // used e = S} ≃ Full H G S where
  toFun e := by
    have mem (u i) : (e.val u).val i ∈ S :=
      (congrArg (fun T : Finset C => (e.val u).val i ∈ T) e.property).mp (used_mem e.val u i)
    refine ⟨restrictColors S e.val mem,?_⟩
    intro c
    have hc : c.val ∈ used e.val := by rw [e.property]; exact c.property
    obtain ⟨u,i,hi⟩ := (membership_used _ _).mp hc
    exact ⟨u,i,Subtype.ext hi⟩
  invFun e := by
    refine ⟨includeColors S e.val,?_⟩
    ext c
    rw [membership_used]
    constructor
    · rintro ⟨u,i,h⟩
      change ((e.val u).val i).val = c at h
      exact h ▸ ((e.val u).val i).property
    · intro h
      obtain ⟨u,i,hi⟩ := e.property ⟨c,h⟩
      exact ⟨u,i,congrArg Subtype.val hi⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def fullEquiv {U V C D : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (π : C ≃ D) :
    Full H G C ≃ Full H G D where
  toFun e := ⟨(relabel G π.toEmbedding).comp e.val,fun d => by
    obtain ⟨u,i,hi⟩ := e.property (π.symm d)
    exact ⟨u,i,(congrArg π hi).trans (π.apply_symm_apply d)⟩⟩
  invFun e := ⟨(relabel G π.symm.toEmbedding).comp e.val,fun c => by
    obtain ⟨u,i,hi⟩ := e.property (π c)
    exact ⟨u,i,(congrArg π.symm hi).trans (π.symm_apply_apply c)⟩⟩
  left_inv e := by
    apply Subtype.ext
    exact DFunLike.ext _ _ fun u => Subtype.ext (funext (fun i => π.symm_apply_apply ((e.val u).val i)))
  right_inv e := by
    apply Subtype.ext
    exact DFunLike.ext _ _ fun u => Subtype.ext (funext (fun i => π.apply_symm_apply ((e.val u).val i)))

end ColourProbe

namespace ColourProbe

open SimpleGraph Polynomial

noncomputable def fullCount {U V : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (j : ℕ) :=
  Nat.card (Full H G (Fin j))

theorem no_full {U V : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V)
    {j : ℕ} (hj : Fintype.card U * Fintype.card V < j) : fullCount H G j = 0 := by
  have _ : IsEmpty (Full H G (Fin j)) := ⟨fun f => by
    let g (p : U × V) := (f.val p.1).val p.2
    have sur : Function.Surjective g := by
      intro c
      obtain ⟨u,i,h⟩ := f.property c
      exact ⟨(u,i),h⟩
    have bound := Fintype.card_le_of_surjective g sur
    simp at bound
    omega⟩
  simp [fullCount]

/-- Expansion in the binomial basis: first choose the set of colors actually
used, then a palette-surjective labeled embedding. No embedding uses more
colors than the number of entries in its matrix of colorings. -/
theorem labelled_binomial {U V : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V) (k : ℕ) :
    Nat.card (H ↪g coloringGraph G (Fin k)) =
      ∑ j ∈ Finset.range (Fintype.card U*Fintype.card V+1), k.choose j * fullCount H G j := by
  classical
  let n := Fintype.card U * Fintype.card V
  let _ := Fintype.ofFinite (H ↪g coloringGraph G (Fin k))
  let _ (S : Finset (Fin k)) := Fintype.ofFinite {e : H ↪g coloringGraph G (Fin k) // used e=S}
  have fibers (S : Finset (Fin k)) : Fintype.card {e : H ↪g coloringGraph G (Fin k) // used e=S} = fullCount H G S.card := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr ((usedFiber H G S).trans (fullEquiv H G (Fintype.equivFinOfCardEq (Fintype.card_coe S))))
  have base : Nat.card (H ↪g coloringGraph G (Fin k)) = ∑ S : Finset (Fin k), fullCount H G S.card := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun e : H ↪g coloringGraph G (Fin k) => used e)),
      Nat.card_eq_fintype_card,Fintype.card_sigma]
    exact Finset.sum_congr rfl fun S _ => fibers S
  let m := max k n+1
  have bound (S : Finset (Fin k)) : S.card ∈ Finset.range m :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.card_le_univ S).trans (by simp)))
  have card (j : ℕ) : ((Finset.univ : Finset (Finset (Fin k))).filter (fun S => S.card=j)).card = k.choose j := by
    have eq : (Finset.univ : Finset (Finset (Fin k))).filter (fun S => S.card=j) = Finset.univ.powersetCard j := by
      ext; simp
    simp [eq,Finset.card_powersetCard]
  rw [base,← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset (Fin k)))) (t := Finset.range m)
    (g := Finset.card) (fun S _ => bound S)]
  calc
    _ = ∑ j ∈ Finset.range m, k.choose j * fullCount H G j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← card j]
      exact Finset.sum_const_nat fun S h => by rw [(Finset.mem_filter.mp h).2]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (le_max_right k n)))
      intro j _ hj
      have gt : n < j := by simpa using hj
      simp [no_full H G gt]

/-- The induced-copy polynomial has rational coefficients because the labeled
binomial-basis count is divided by the finite automorphism count of the probe. -/
noncomputable def countPolynomial {U V : Type*} [Fintype U] [Fintype V]
    (H : SimpleGraph U) (G : SimpleGraph V) : ℚ[X] :=
  C (Nat.card (H ≃g H) : ℚ)⁻¹ * ∑ j ∈ Finset.range (Fintype.card U*Fintype.card V+1),
    C ((fullCount H G j : ℚ) / j.factorial) * descPochhammer ℚ j

theorem countPolynomial_eval {U V : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V) (k : ℕ) :
    (countPolynomial H G).eval (k : ℚ) = inducedCount H (coloringGraph G (Fin k)) := by
  classical
  have _ : Finite (H ≃g H) := Finite.of_injective (fun e : H ≃g H => (e : U → U)) DFunLike.coe_injective
  have _ : Nonempty (H ≃g H) := ⟨RelIso.refl _⟩
  have nz : (Nat.card (H ≃g H) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h := (labelled_binomial H G k).symm.trans (embeddings_count H (coloringGraph G (Fin k)))
  have hq := congrArg (fun n : ℕ => (n : ℚ)) h
  push_cast at hq
  simp only [countPolynomial,eval_mul,eval_C,eval_finsetSum]
  calc
    _ = (Nat.card (H ≃g H) : ℚ)⁻¹ * ∑ j ∈ Finset.range (Fintype.card U*Fintype.card V+1),
        (k.choose j : ℚ) * fullCount H G j := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.cast_choose_eq_descPochhammer_div]
      ring
    _ = _ := by rw [hq]; field_simp

/-- The conjecture stated using literal polynomial equality, for all finite
simple targets and hosts and with the explicit connected probe size bound. -/
theorem polynomial_reconstruction {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ (U : Type) (_ : Fintype U) (H : SimpleGraph U), H.Connected ∧
      Fintype.card U ≤ 1 + Fintype.card V*(Fintype.card V+1) + (Fintype.card V).choose 2*(Fintype.card V+1)^2 ∧
      ∀ (W : Type) [Fintype W] (K : SimpleGraph W), countPolynomial H G = countPolynomial H K → Nonempty (G ≃g K) := by
  obtain ⟨U,fin,H,con,bnd,h⟩ := one_colouring_probe G
  refine ⟨U,fin,H,con,bnd,fun W _ K hk => h W K fun k => ?_⟩
  have e := congrArg (Polynomial.eval (k : ℚ)) hk
  rw [countPolynomial_eval,countPolynomial_eval] at e
  exact_mod_cast e

end ColourProbe
