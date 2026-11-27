module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Order.Minimal

@[expose] public section

/-! Standalone reference for the quantitative bounds and the closed-neighborhood
reduction in the co-bipartite obstruction theorem. -/

namespace DominationVC

/-- Two vertices belong to each other's closed incomparability neighborhood
exactly when neither is strictly below the other. Equality is allowed. -/
def Visible {V : Type*} [PartialOrder V] (v w : V) : Prop := ¬v < w ∧ ¬w < v

def incomparability (V : Type*) [PartialOrder V] : SimpleGraph V where
  Adj v w := v ≠ w ∧ Visible v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The set family of the actual closed graph neighborhoods. -/
noncomputable def closedFamily {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.image fun v => Finset.univ.filter fun w => w = v ∨ G.Adj v w

/-- An arbitrary graph whose two labeled sides are cliques. The supplied relation
prescribes all cross-edges. -/
def twoCliques {a b : ℕ} (P : Fin a → Fin b → Prop) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj
    | .inl x, .inl y => x ≠ y
    | .inr x, .inr y => x ≠ y
    | .inl x, .inr y => P x y
    | .inr y, .inl x => P x y
  symm := ⟨fun x y => by
    cases x <;> cases y
    · exact Ne.symm
    · exact id
    · exact id
    · exact Ne.symm⟩
  loopless := ⟨fun x => by cases x <;> exact fun h => h rfl⟩

/-- Twice the number of locations required by the two blocks and the marker pairs. -/
def threshold (a b : ℕ) : ℕ := 2 * (2*a + 2*max 1 (Nat.clog 2 (b^2)))

end DominationVC

namespace DominationVC

variable {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V] {S : Finset V}

omit [Fintype V] in
theorem closed_iff_visible (w v : V) : v = w ∨ (incomparability V).Adj w v ↔ Visible w v := by
  constructor
  · rintro (rfl | h)
    · exact ⟨lt_irrefl _, lt_irrefl _⟩
    · exact h.2
  · intro h
    by_cases he : v = w
    · exact .inl he
    · exact .inr ⟨Ne.symm he, h⟩

/-- Realize any prescribed predicate on a shattered set by one closed neighborhood. -/
theorem realize (hs : (closedFamily (incomparability V)).Shatters S) (P : V → Prop) :
    ∃ w, ∀ v ∈ S, Visible w v ↔ P v := by
  classical
  obtain ⟨N, hN, h⟩ := hs (Finset.filter_subset P S)
  unfold closedFamily at hN
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hN
  refine ⟨w, fun v hv => ?_⟩
  have he := Finset.ext_iff.mp h v
  simpa only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hv,
    closed_iff_visible] using he

theorem no_three_chain (hs : (closedFamily (incomparability V)).Shatters S)
    {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x < y) (hyz : y < z) : False := by
  obtain ⟨w, hw⟩ := realize hs (fun q => q ≠ y)
  have hvx := (hw x hx).2 hxy.ne
  have hvz := (hw z hz).2 (Ne.symm hyz.ne)
  have hn : ¬Visible w y := fun hv => (hw y hy).1 hv rfl
  by_cases hwy : w < y
  · exact hvz.1 (hwy.trans hyz)
  · exact hn ⟨hwy, fun hyw => hvx.2 (hxy.trans hyw)⟩

/-- In height at most two, the minimal elements and their complement are antichains.
One side can therefore host any finite index type of at most half the shattered size. -/
theorem large_antichain {I : Type*} [Fintype I] (hs : (closedFamily (incomparability V)).Shatters S)
    (hsize : 2 * Fintype.card I ≤ S.card) :
    ∃ f : I ↪ V, (∀ i, f i ∈ S) ∧ ∀ i j, ¬f i < f j := by
  classical
  let minimal (v : V) := ¬ ∃ w ∈ S, w < v
  have sizes := Finset.card_filter_add_card_filter_not (s := S) minimal
  have side (T : Finset V) (hsub : T ⊆ S) (hc : Fintype.card I ≤ T.card)
      (hanti : ∀ v ∈ T, ∀ w ∈ T, ¬v < w) :
      ∃ f : I ↪ V, (∀ i, f i ∈ S) ∧ ∀ i j, ¬f i < f j := by
    obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hc
    have hx (i : I) : f i ∈ T := hf ⟨i, rfl⟩
    exact ⟨f, fun i => hsub (hx i), fun i j => hanti _ (hx i) _ (hx j)⟩
  by_cases h : Fintype.card I ≤ (S.filter minimal).card
  · apply side (S.filter minimal) (Finset.filter_subset ..) h
    intro x hx y hy hlt
    exact (Finset.mem_filter.mp hy).2 ⟨x, (Finset.mem_filter.mp hx).1, hlt⟩
  · apply side (S.filter fun v => ¬minimal v) (Finset.filter_subset ..) (by omega)
    intro x hx y hy hlt
    have hnm := (Finset.mem_filter.mp hx).2
    obtain ⟨w, hw, hlt'⟩ := not_not.mp hnm
    exact no_three_chain hs hw (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hlt' hlt

end DominationVC

namespace DominationVC

abbrev Slots (a m : ℕ) := Fin a ⊕ (Fin a ⊕ (Fin m × Bool))
abbrev Index (b : ℕ) := Fin b × Fin b

/-- Two data blocks record the row and column cross-neighborhoods. Exactly one
of each marker pair is selected, according to the address of the witness. -/
def trace {a b m : ℕ} (P : Fin a → Fin b → Prop) (code : Index b ↪ (Fin m → Bool))
    (i : Index b) : Slots a m → Prop
  | .inl x => P x i.1
  | .inr (.inl x) => P x i.2
  | .inr (.inr (k,bit)) => bit = code i k

structure WitnessArray (V : Type*) [PartialOrder V] {a b m : ℕ}
    (P : Fin a → Fin b → Prop) (code : Index b ↪ (Fin m → Bool)) where
  A : Slots a m ↪ V
  antichain : ∀ r s, ¬A r < A s
  w : Index b → V
  sees : ∀ i r, Visible (w i) (A r) ↔ trace P code i r

theorem array_exists {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b m : ℕ} {S : Finset V} (hs : (closedFamily (incomparability V)).Shatters S)
    (hsize : 2 * (2*a + 2*m) ≤ S.card) (P : Fin a → Fin b → Prop)
    (code : Index b ↪ (Fin m → Bool)) : Nonempty (WitnessArray V P code) := by
  classical
  have hc : Fintype.card (Slots a m) = 2*a + 2*m := by simp [Slots]; omega
  obtain ⟨A, ha, anti⟩ := large_antichain (I := Slots a m) hs (hc ▸ hsize)
  have ex (i : Index b) : ∃ w, ∀ r, Visible w (A r) ↔ trace P code i r := by
    obtain ⟨w, hw⟩ := realize hs (fun v => ∃ q, A q = v ∧ trace P code i q)
    refine ⟨w, fun r => (hw _ (ha r)).trans ?_⟩
    constructor
    · rintro ⟨q, he, hq⟩
      exact A.injective he ▸ hq
    · exact fun h => ⟨r, rfl, h⟩
  exact ⟨⟨A, anti, fun i => (ex i).choose, fun i => (ex i).choose_spec⟩⟩

namespace WitnessArray
variable {V : Type*} [PartialOrder V] {a b m : ℕ}
    {P : Fin a → Fin b → Prop} {code : Index b ↪ (Fin m → Bool)} (d : WitnessArray V P code)

theorem distinguishes {i j : Index b} (hn : i ≠ j) :
    ∃ r, Visible (d.w i) (d.A r) ∧ ¬Visible (d.w j) (d.A r) := by
  classical
  obtain ⟨k,hk⟩ : ∃ k, code i k ≠ code j k := by
    by_contra! he
    exact hn (code.injective (funext he))
  refine ⟨.inr (.inr (k, code i k)), (d.sees _ _).2 rfl, ?_⟩
  exact fun h => hk ((d.sees _ _).1 h)

theorem w_injective : Function.Injective d.w := by
  intro i j h
  by_contra hn
  obtain ⟨r, hi, hj⟩ := d.distinguishes hn
  exact hj (h ▸ hi)

theorem outside (hm : 0 < m) (i : Index b) (r : Slots a m) : d.w i ≠ d.A r := by
  intro he
  let k : Fin m := ⟨0, hm⟩
  let s : Slots a m := .inr (.inr (k, !(code i k)))
  have h : Visible (d.w i) (d.A s) := he ▸ ⟨d.antichain r s, d.antichain s r⟩
  have hv : (!(code i k)) = code i k := (d.sees i s).1 h
  cases c : code i k <;> simp [c] at hv

/-- A positive witness lies strictly below some member of the antichain. -/
def positive (i : Index b) : Prop := ∃ r, d.w i < d.A r

theorem same_orientation {i j : Index b} (hne : i ≠ j) (hc : d.positive i ↔ d.positive j) :
    ¬d.w i < d.w j := by
  intro hlt
  by_cases hpos : d.positive j
  · obtain ⟨r,hi,hj⟩ := d.distinguishes hne
    obtain ⟨s,hs⟩ := hpos
    have hbefore : d.w j < d.A r := by
      by_contra h
      exact hj ⟨h, fun h' => d.antichain r s (h'.trans hs)⟩
    exact hi.1 (hlt.trans hbefore)
  · obtain ⟨r,hj,hi⟩ := d.distinguishes hne.symm
    have hi' : ¬d.positive i := fun h => hpos (hc.1 h)
    have hafter : d.A r < d.w i := by
      by_contra h
      exact hi ⟨fun h' => hi' ⟨r,h'⟩, h⟩
    exact hj.2 (hafter.trans hlt)

end WitnessArray
end DominationVC

namespace DominationVC.WitnessArray

variable {V : Type*} [PartialOrder V] {a b m : ℕ}
    {P : Fin a → Fin b → Prop} {code : Index b ↪ (Fin m → Bool)} (d : WitnessArray V P code)

/-- Combine one data block with an injective set of same-orientation witnesses.
The embedding reflects every nonedge as well as preserving every edge. -/
theorem assemble (hm : 0 < m) (block : Fin a → Slots a m) (hb : Function.Injective block)
    (pick : Fin b → Index b) (hp : Function.Injective pick)
    (orient : ∀ i j, d.positive (pick i) ↔ d.positive (pick j))
    (data : ∀ x i, trace P code (pick i) (block x) ↔ P x i) :
    Nonempty (twoCliques P ↪g incomparability V) := by
  let left := fun x => d.A (block x)
  let right := fun i => d.w (pick i)
  have hl : Function.Injective left := d.A.injective.comp hb
  have hr : Function.Injective right := d.w_injective.comp hp
  have hsep (x i) : left x ≠ right i := (d.outside hm _ _).symm
  have cross (x i) : (incomparability V).Adj (left x) (right i) ↔ P x i := by
    constructor
    · exact fun h => (data x i).1 ((d.sees _ _).1 ⟨h.2.2,h.2.1⟩)
    · intro h
      have hv := (d.sees _ _).2 ((data x i).2 h)
      exact ⟨hsep x i, hv.2, hv.1⟩
  refine ⟨{ toFun := Sum.elim left right, inj' := hl.sumElim hr hsep, map_rel_iff' := ?_ }⟩
  intro x y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      change (left x ≠ left y ∧ Visible (left x) (left y)) ↔ x ≠ y
      exact ⟨fun h => fun e => h.1 (congrArg _ e),
        fun h => ⟨hl.ne h, d.antichain _ _, d.antichain _ _⟩⟩
    | inr y => exact cross x y
  | inr x =>
    cases y with
    | inl y => exact ((incomparability V).adj_comm _ _).trans (cross y x)
    | inr y =>
      change (right x ≠ right y ∧ Visible (right x) (right y)) ↔ x ≠ y
      exact ⟨fun h => fun e => h.1 (congrArg _ e), fun h => ⟨hr.ne h,
        d.same_orientation (hp.ne h) (orient _ _), d.same_orientation (hp.ne h.symm) (orient _ _)⟩⟩

include d in
/-- Either every row supplies a positive witness, or a single row supplies all
negative witnesses. The two separate data blocks handle these two choices. -/
theorem induced_copy (hm : 0 < m) : Nonempty (twoCliques P ↪g incomparability V) := by
  classical
  by_cases hrows : ∀ i : Fin b, ∃ j : Fin b, d.positive (i,j)
  · let j (i : Fin b) := (hrows i).choose
    have hpos (i) : d.positive (i,j i) := (hrows i).choose_spec
    apply d.assemble hm Sum.inl Sum.inl_injective (fun i => (i,j i))
    · exact fun _ _ h => congrArg Prod.fst h
    · exact fun i k => ⟨fun _ => hpos k, fun _ => hpos i⟩
    · exact fun _ _ => Iff.rfl
  · push Not at hrows
    obtain ⟨i, hi⟩ := hrows
    apply d.assemble hm (fun x => Sum.inr (Sum.inl x))
      (Sum.inr_injective.comp Sum.inl_injective) (fun j => (i,j))
    · exact fun _ _ h => congrArg Prod.snd h
    · exact fun j k => ⟨fun h => False.elim (hi j h), fun h => False.elim (hi k h)⟩
    · exact fun _ _ => Iff.rfl

end DominationVC.WitnessArray

namespace DominationVC

/-- A shattered set with at least twice the two-block/two-marker budget forces
an induced copy of every prescribed co-bipartite graph of the given side sizes. -/
theorem shattering {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b : ℕ} (P : Fin a → Fin b → Prop) (S : Finset V)
    (hs : (closedFamily (incomparability V)).Shatters S) (hsize : threshold a b ≤ S.card) :
    Nonempty (twoCliques P ↪g incomparability V) := by
  classical
  let m := max 1 (Nat.clog 2 (b^2))
  have hbits : Fintype.card (Index b) ≤ Fintype.card (Fin m → Bool) := by
    simpa only [Index, Fintype.card_prod, Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool,
      ← sq] using (Nat.clog_le_iff_le_pow (b := 2) (by decide)).1 (le_max_right 1 (Nat.clog 2 (b^2)))
  obtain ⟨code⟩ := Function.Embedding.nonempty_of_card_le hbits
  obtain ⟨array⟩ := array_exists hs (m := m) hsize P code
  exact array.induced_copy (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..))

/-- The VC dimension of closed neighborhoods is below the explicit threshold
in every finite incomparability graph avoiding a fixed induced co-bipartite graph. -/
theorem vc_bound {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b : ℕ} (P : Fin a → Fin b → Prop) (avoids : ¬ Nonempty (twoCliques P ↪g incomparability V)) :
    (closedFamily (incomparability V)).vcDim < threshold a b := by
  classical
  have pos : 0 < threshold a b := by unfold threshold; omega
  apply lt_of_le_of_lt (b := threshold a b - 1) _ (by omega)
  apply Finset.sup_le
  intro s hs
  have hsmall : ¬threshold a b ≤ s.card := fun h => avoids (shattering P s (Finset.mem_shatterer.mp hs) h)
  omega

end DominationVC

namespace DominationVC

/-- The membership example has one side of points and one side of subsets. -/
inductive Host (d : ℕ) where
  | point (x : Fin d)
  | subset (s : Finset (Fin d))
  deriving DecidableEq, Fintype

namespace Host

variable {d : ℕ}

/-- The only strict comparisons go from a point to a set omitting it. -/
def below : Host d → Host d → Prop
  | .point x, .subset s => x ∉ s
  | _, _ => False

instance : PartialOrder (Host d) where
  le x y := x = y ∨ below x y
  le_refl _ := .inl rfl
  le_trans x y z h₁ h₂ := by
    rcases h₁ with rfl | h₁
    · exact h₂
    rcases h₂ with rfl | h₂
    · exact .inr h₁
    cases x <;> cases y <;> cases z <;> simp_all [below]
  le_antisymm x y h₁ h₂ := by
    rcases h₁ with rfl | h₁
    · rfl
    rcases h₂ with he | h₂
    · exact he.symm
    cases x <;> cases y <;> simp_all [below]

theorem lt_iff_below (x y : Host d) : x < y ↔ below x y := by
  change ((_ ∨ _) ∧ ¬(_ ∨ _)) ↔ _
  cases x <;> cases y <;> simp [below] <;> grind

def pointSide (d : ℕ) : Finset (Host d) := Finset.univ.image point

theorem point_card (d : ℕ) : (pointSide d).card = d := by
  rw [pointSide, Finset.card_image_of_injective _ (fun _ _ => Host.point.inj)]
  simp

theorem adjacency_point_subset (x : Fin d) (s : Finset (Fin d)) :
    (incomparability (Host d)).Adj (.point x) (.subset s) ↔ x ∈ s := by
  change (_ ≠ _ ∧ ¬_ < _ ∧ ¬_ < _) ↔ _
  simp [lt_iff_below, below]

/-- Every subset of the point side is exactly its trace on the neighborhood of
the corresponding subset vertex, including the empty trace. -/
theorem points_shattered (d : ℕ) :
    (closedFamily (incomparability (Host d))).Shatters (pointSide d) := by
  classical
  intro t ht
  let s : Finset (Fin d) := Finset.univ.filter fun x => point x ∈ t
  unfold closedFamily
  apply Exists.intro (Finset.univ.filter fun v => v = subset s ∨ (incomparability (Host d)).Adj (subset s) v)
  constructor
  · exact Finset.mem_image.mpr ⟨subset s, Finset.mem_univ _, rfl⟩
  · ext v
    cases v with
    | point x =>
      rw [Finset.mem_inter]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hin : point x ∈ pointSide d := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
      rw [((incomparability (Host d)).adj_comm (subset s) _), adjacency_point_subset]
      simp [hin, s]
    | subset u =>
      have hn : subset u ∉ pointSide d := by simp [pointSide]
      have ht' : subset u ∉ t := fun h => hn (ht h)
      simp [hn,ht']

def isPoint : Host d → Bool
  | .point _ => true
  | .subset _ => false

theorem same_side_adj {x y : Host d} (h : isPoint x = isPoint y) (hne : x ≠ y) :
    (incomparability (Host d)).Adj x y := by
  refine ⟨hne, ?_, ?_⟩ <;> cases x <;> cases y <;> simp_all [isPoint, lt_iff_below, below]

/-- A connected target clique forced into the point side has at most d vertices. -/
theorem point_capacity {n : ℕ} (f : Fin n → Host d) (hf : Function.Injective f)
    (hp : ∀ i, isPoint (f i) = true) : n ≤ d := by
  classical
  have hv (i : Fin n) : ∃ q, f i = point q := by
    cases h : f i with
    | point x => exact ⟨x,rfl⟩
    | subset s => simpa [h,isPoint] using hp i
  have hinj : Function.Injective (fun i => (hv i).choose) := by
    intro x y h
    apply hf
    rw [(hv x).choose_spec, (hv y).choose_spec]
    exact congrArg point h
  simpa using Fintype.card_le_of_injective _ hinj

theorem card_host (d : ℕ) : Fintype.card (Host d) = d + 2^d := by
  let e : Host d ≃ Fin d ⊕ Finset (Fin d) :=
    ⟨(fun x => match x with | point p => .inl p | subset s => .inr s), Sum.elim point subset,
     (fun x => by cases x <;> rfl), (fun x => by cases x <;> rfl)⟩
  simp [Fintype.card_congr e]

end Host
end DominationVC

namespace DominationVC

/-- The disjoint union of two cliques cannot embed if each of the cliques is
too large for the point side: opposite target parts must have opposite tags. -/
theorem avoids_by_point_side {a b d : ℕ} (ha : d < a) (hb : d < b) :
    ¬Nonempty (twoCliques (fun (_ : Fin a) (_ : Fin b) => False) ↪g incomparability (Host d)) := by
  classical
  rintro ⟨e⟩
  have htag (x : Fin a) (y : Fin b) : (e (.inl x)).isPoint ≠ (e (.inr y)).isPoint := by
    intro h
    have hne : e (.inl x) ≠ e (.inr y) := e.injective.ne (by simp)
    exact e.map_rel_iff.mp (Host.same_side_adj h hne)
  by_cases all : ∀ x : Fin a, (e (.inl x)).isPoint = true
  · have h := Host.point_capacity (fun i : Fin a => e (.inl i))
      (e.injective.comp Sum.inl_injective) all
    omega
  · obtain ⟨x,hx⟩ := not_forall.mp all
    have all' (y : Fin b) : (e (.inr y)).isPoint = true := by
      have := htag x y
      cases he : (e (.inl x)).isPoint <;> cases he' : (e (.inr y)).isPoint <;> simp_all
    have h := Host.point_capacity (fun i : Fin b => e (.inr i)) (e.injective.comp Sum.inr_injective) all'
    omega

theorem avoids_by_size {a b d : ℕ} (h : d + 2^d < a+b) :
    ¬Nonempty (twoCliques (fun (_ : Fin a) (_ : Fin b) => False) ↪g incomparability (Host d)) := by
  rintro ⟨e⟩
  have hc := Fintype.card_le_of_embedding e.toEmbedding
  simp only [Fintype.card_sum, Fintype.card_fin, Host.card_host] at hc
  omega

def lowerSize (a b : ℕ) : ℕ := max (a-1) (Nat.log 2 (b+1) - 2)

theorem host_lower (d : ℕ) : d ≤ (closedFamily (incomparability (Host d))).vcDim := by
  have h := Finset.Shatters.card_le_vcDim (Host.points_shattered d)
  rw [Host.point_card] at h
  exact h

/-- A single explicit forbidden graph K_a ⊔ K_b and a height-two membership
host give the matching-order lower bound, with the stated finite additive constants. -/
theorem vc_lower {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (¬Nonempty (twoCliques (fun (_ : Fin a) (_ : Fin b) => False) ↪g incomparability (Host (lowerSize a b)))) ∧
    lowerSize a b ≤ (closedFamily (incomparability (Host (lowerSize a b)))).vcDim := by
  constructor
  · unfold lowerSize
    by_cases h : Nat.log 2 (b+1) - 2 ≤ a-1
    · rw [max_eq_left h]
      exact avoids_by_point_side (by omega) (by omega)
    · rw [max_eq_right (by omega)]
      apply avoids_by_size
      let n := Nat.log 2 (b+1) - 2
      have hn : n + 2 = Nat.log 2 (b+1) := by dsimp [n]; omega
      have hpow := Nat.pow_log_le_self 2 (Nat.succ_ne_zero b)
      rw [← hn, pow_add] at hpow
      have hl : n < 2^n := Nat.lt_two_pow_self
      change n + 2^n < a+b
      omega
  · exact host_lower _

end DominationVC

namespace DominationVC

/-- A dominating set covers each vertex by equality or adjacency. -/
def Dominates {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, v = w ∨ G.Adj v w

/-- A hypergraph transversal hits every hyperedge. -/
def Hits {V : Type*} (edges : Finset (Finset V)) (D : Finset V) : Prop :=
  ∀ E ∈ edges, ∃ w ∈ D, w ∈ E

/-- Keep only inclusion-minimal hyperedges. -/
noncomputable def clean {V : Type*} (edges : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact edges.filter (Minimal (· ∈ edges))

theorem hits_clean {V : Type*} (edges : Finset (Finset V)) (D : Finset V) :
    Hits (clean edges) D ↔ Hits edges D := by
  classical
  constructor
  · intro h E he
    obtain ⟨F, hsub, hmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ edges) E he
    obtain ⟨v,hv,hF⟩ := h F (Finset.mem_filter.mpr ⟨hmin.1,hmin⟩)
    exact ⟨v,hv,hsub hF⟩
  · exact fun h E he => h E (Finset.mem_filter.mp he).1

theorem dominates_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V) :
    Dominates G D ↔ Hits (closedFamily G) D := by
  classical
  constructor
  · intro h E hE
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨w, hw, hvis⟩ := h v
    exact ⟨w, hw, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvis.elim (fun he => Or.inl he.symm) Or.inr⟩⟩
  · intro h v
    let E := Finset.univ.filter fun w => w = v ∨ G.Adj v w
    have he : E ∈ closedFamily G := Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
    obtain ⟨w, hw, hv⟩ := h E he
    exact ⟨w,hw,(Finset.mem_filter.mp hv).2.elim (fun e => Or.inl e.symm) Or.inr⟩

/-- The reduction used by the enumeration theorem. It needs no orientation as
input, outputs at most n hyperedges and preserves the actual inclusion-minimal
solutions. On the promised class its output has the explicit dimension bound. -/
theorem domination_reduction {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b : ℕ} (P : Fin a → Fin b → Prop) (avoids : ¬Nonempty (twoCliques P ↪g incomparability V)) :
    let H := clean (closedFamily (incomparability V))
    H.card ≤ Fintype.card V ∧ H.vcDim < threshold a b ∧
      ∀ D : Finset V, Minimal (Dominates (incomparability V)) D ↔ Minimal (Hits H) D := by
  classical
  dsimp only
  have sub : clean (closedFamily (incomparability V)) ⊆ closedFamily (incomparability V) := Finset.filter_subset ..
  refine ⟨(Finset.card_le_card sub).trans ?_, (Finset.vcDim_mono sub).trans_lt (vc_bound P avoids), ?_⟩
  · exact (Finset.card_image_le.trans (Finset.card_univ.le))
  · intro D
    have he : Dominates (incomparability V) = Hits (clean (closedFamily (incomparability V))) := by
      funext X
      exact propext ((dominates_iff _ _).trans (hits_clean _ _).symm)
    rw [he]

end DominationVC
