module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Function.Iterate
public import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Set.Finite.Range
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Ring

/-!
# Finite/cofinite codes in a symmetric block model

The protected declarations are `ProjectiveBlocks.blockOrbitBound`,
`ProjectiveBlocks.equivariantSurjection`, `ProjectiveTransfer.transferGraph`, and
`ProjectiveTransfer.obstructionOfBlockModel`. The last theorem relates the map
on the original carrier to its first-order coding on a countable block model.
-/

@[expose] public section

namespace ProjectiveBlocks

/-- A finite core and countably many blocks, each with `d` labelled positions. -/
abbrev Point (c d : ℕ) := Fin c ⊕ (ℕ × Fin d)

/-- Each of the `k` coordinates stores its finite/cofinite flag and its finite part. -/
abbrev Code (c d k : ℕ) := Fin k → Bool × Finset (Point c d)

/-- A block permutation fixes the core and preserves the position inside each block. -/
def relabel {c d : ℕ} (σ : Equiv.Perm ℕ) : Equiv.Perm (Point c d) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr σ (Equiv.refl _))

/-- Transport the actual finite subsets by the positionwise action. -/
def rename {c d k : ℕ} (σ : Equiv.Perm ℕ) (x : Code c d k) : Code c d k :=
  fun j => ((x j).1, (x j).2.map (relabel σ).toEmbedding)

/-- The self-map commutes with every block permutation. -/
def Equivariant {c d k : ℕ} (g : Code c d k → Code c d k) : Prop :=
  ∀ σ x, g (rename σ x) = rename σ (g x)

/-- The core and flags have `2^(k(1+c))` states, and there are `q` possible
patterns of a block, giving `q^q` output tables on input patterns. -/
def orbitBound (c d k : ℕ) : ℕ :=
  let q := 2 ^ (d * k)
  2 ^ (k * (1 + c)) * q ^ q

end ProjectiveBlocks

public section

namespace ProjectiveBlocks

open Function Set

private abbrev Pattern (d k : ℕ) := Fin d × Fin k → Bool
private abbrev Table (c d k : ℕ) :=
  (Fin k → Bool) × (Fin c × Fin k → Bool) × (Pattern d k → Pattern d k)

private def pattern {c d k} (x : Code c d k) (i : ℕ) : Pattern d k :=
  fun p => decide (Sum.inr (i, p.1) ∈ (x p.2).2)

private def core {c d k} (x : Code c d k) : Fin c × Fin k → Bool :=
  fun p => decide (Sum.inl p.1 ∈ (x p.2).2)

private theorem ext_code {c d k} {x y : Code c d k}
    (hflag : ∀ j, (x j).1 = (y j).1) (hcore : core x = core y)
    (hblocks : ∀ i, pattern x i = pattern y i) : x = y := by
  funext j
  apply Prod.ext (hflag j)
  apply Finset.ext
  intro a
  obtain a | ⟨i,t⟩ := a
  · simpa [core] using congrFun hcore (a,j)
  · simpa [pattern] using congrFun (hblocks i) (t,j)

private theorem pattern_rename {c d k} (σ : Equiv.Perm ℕ) (x : Code c d k) (i : ℕ) :
    pattern (rename σ x) i = pattern x (σ.symm i) := by
  funext j
  simp only [pattern, rename, Finset.mem_map_equiv]
  rfl

private theorem core_rename {c d k} (σ : Equiv.Perm ℕ) (x : Code c d k) :
    core (rename σ x) = core x := by
  funext j
  simp only [core, rename, Finset.mem_map_equiv]
  rfl

private theorem iter_const {c d k} {g : Code c d k → Code c d k} (hg : Equivariant g)
    (s : Code c d k) {a b : ℕ} (hab : pattern s a = pattern s b) (n : ℕ) :
    pattern (g^[n] s) a = pattern (g^[n] s) b := by
  let σ := Equiv.swap a b
  have fixed : rename σ s = s := by
    apply ext_code (x := rename σ s) (y := s) (fun _ => rfl) (core_rename σ s)
    intro i
    rw [pattern_rename]
    change pattern s (Equiv.swap a b i) = pattern s i
    by_cases ha : i = a
    · simpa [ha] using hab.symm
    by_cases hb : i = b
    · simpa [hb] using hab
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  have stabilizes : rename σ (g^[n] s) = g^[n] s := by
    induction n with
    | zero => exact fixed
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← hg σ, ih]
  have hb := congrArg (fun x => pattern x b) stabilizes
  simpa only [pattern_rename, σ, Equiv.symm_swap, Equiv.swap_apply_right] using hb

private noncomputable def representative {c d k} (s : Code c d k) (p : Pattern d k) : ℕ :=
  open Classical in if h : ∃ i, pattern s i = p then Nat.find h else 0

private theorem rep_pattern {c d k} (s : Code c d k) (i : ℕ) :
    pattern s (representative s (pattern s i)) = pattern s i := by
  classical
  have h : ∃ j, pattern s j = pattern s i := ⟨i,rfl⟩
  simpa only [representative, dite_eq_left h] using Nat.find_spec h

private noncomputable def encode {c d k} (s x : Code c d k) : Table c d k :=
  (fun j => (x j).1, core x, fun p => pattern x (representative s p))

private theorem encode_inj {c d k} {g : Code c d k → Code c d k} (hg : Equivariant g)
    (s : Code c d k) : Set.InjOn (encode s) (Set.range (fun n => g^[n] s)) := by
  rintro _ ⟨n,rfl⟩ _ ⟨m,rfl⟩ h
  apply ext_code (congrFun (congrArg Prod.fst h)) (congrArg (fun t => t.2.1) h)
  intro i
  have hi := rep_pattern s i
  exact (iter_const hg s hi n).symm.trans <|
    (congrFun (congrArg (fun t => t.2.2) h) (pattern s i)).trans (iter_const hg s hi m)

private theorem table_card (c d k : ℕ) : Fintype.card (Table c d k) = orbitBound c d k := by
  simp only [Table, Pattern, orbitBound, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  rw [← Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  ring

/-- The explicit uniform bound in the manuscript counts all forward iterates of
any finite/cofinite code, including the finite parts on the fixed core. -/
theorem blockOrbitBound {c d k : ℕ} (g : Code c d k → Code c d k) (hg : Equivariant g)
    (s : Code c d k) :
    (Set.range fun n : ℕ => g^[n] s).Finite ∧
    (Set.range fun n : ℕ => g^[n] s).ncard ≤ orbitBound c d k := by
  classical
  let O := Set.range fun n : ℕ => g^[n] s
  have inj := encode_inj hg s
  have finite : O.Finite := Set.Finite.of_injOn (f := encode s) (t := Set.univ)
    (fun _ _ => trivial) inj (Set.finite_univ)
  refine ⟨finite, ?_⟩
  have le := O.ncard_le_ncard_of_injOn (encode s) (t := Set.univ) (fun _ _ => trivial) inj
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, table_card] using le

private theorem eventual_period {X : Type*} (f : X → X) (x : X) (B : ℕ)
    {a b : Fin (B+1)} (hab : a < b) (heq : f^[a.val] x = f^[b.val] x) :
    Function.IsPeriodicPt f B.factorial (f^[B] x) := by
  have hper : Function.IsPeriodicPt f (b.val - a.val) (f^[a.val] x) := by
    change f^[b.val-a.val] (f^[a.val] x) = f^[a.val] x
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le, heq]
  have ale : a.val ≤ B := by omega
  have pos : 0 < b.val-a.val := by omega
  have le : b.val-a.val ≤ B := by omega
  have period := (hper.trans_dvd (Nat.dvd_factorial pos le)).apply_iterate (B-a.val)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel ale] at period

/-- A surjective equivariant map has a single finite exponent working on all
codes. In particular it cannot be the noninjective surjection transferred to
this countable block model in the degenerate case of the paper. -/
theorem equivariantSurjection {c d k : ℕ} (g : Code c d k → Code c d k)
    (hg : Equivariant g) (hs : Function.Surjective g) :
    g^[(orbitBound c d k).factorial] = id ∧ Function.Injective g := by
  let B := orbitBound c d k
  have all (s : Code c d k) : Function.IsPeriodicPt g B.factorial s := by
    obtain ⟨x,rfl⟩ := hs.iterate B s
    let tags (n : Fin (B+1)) := encode x (g^[n.val] x)
    have count : Fintype.card (Table c d k) < Fintype.card (Fin (B+1)) := by
      rw [table_card, Fintype.card_fin]
      exact Nat.lt_succ_self B
    obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt tags count
    have same := encode_inj hg x ⟨i.val,rfl⟩ ⟨j.val,rfl⟩ he
    rcases lt_or_gt_of_ne hne with h | h
    · exact eventual_period g x B h same
    · exact eventual_period g x B h same.symm
  exact ⟨funext (fun s => (all s).eq),
    fun {_ _} h => (all _).eq_of_apply_eq_same (all _) (Nat.factorial_pos B) h⟩

end ProjectiveBlocks

@[expose] public section

namespace ProjectiveTypes

open FirstOrder FirstOrder.Language Set

variable (L : Language) {ι κ M N : Type*} [L.Structure M] [L.Structure N]

/-- The full first-order type of a tuple over the empty set. -/
def tupleType (x : ι → M) : Set (L.Formula ι) := {φ | φ.Realize x}

/-- Types of the given arity actually realized in a structure. -/
def typesIn (M : Type*) [L.Structure M] (ι : Type*) : Set (Set (L.Formula ι)) :=
  Set.range (tupleType L : (ι → M) → Set (L.Formula ι))

private theorem distinguish (x : ι → M) (y : ι → N) (h : tupleType L x ≠ tupleType L y) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ¬φ.Realize y := by
  by_contra! no
  apply h
  ext φ
  change φ.Realize x ↔ φ.Realize y
  refine ⟨no φ, fun hy => ?_⟩
  by_contra hx
  exact (Formula.realize_not.mp (no φ.not (Formula.realize_not.mpr hx))) hy

/-- A single formula separates a tuple from any finite collection of other realized types. -/
private theorem separate (x : ι → M) (S : Set (Set (L.Formula ι))) (hs : S.Finite)
    (realized : S ⊆ typesIn L N ι) (avoids : tupleType L x ∉ S) :
    ∃ φ : L.Formula ι, φ.Realize x ∧ ∀ y : ι → N, tupleType L y ∈ S → ¬φ.Realize y := by
  induction S, hs using Set.Finite.induction_on with
  | empty => exact ⟨⊤, Formula.realize_top.mpr trivial, by simp⟩
  | @insert q S hq hs ih =>
    have nq : tupleType L x ≠ q := fun h => avoids (h ▸ Set.mem_insert q S)
    obtain ⟨y,hy⟩ := realized (Set.mem_insert q S)
    obtain ⟨φ,hφ,hφy⟩ := distinguish L x y (hy ▸ nq)
    obtain ⟨θ,hθ,hθy⟩ := ih ((Set.subset_insert q S).trans realized)
      (fun h => avoids (Set.mem_insert_of_mem q h))
    refine ⟨φ ⊓ θ, Formula.realize_inf.mpr ⟨hφ,hθ⟩, ?_⟩
    intro z hz h
    obtain ⟨hp,ht⟩ := Formula.realize_inf.mp h
    rcases Set.mem_insert_iff.mp hz with eq | hz
    · exact hφy ((show φ ∈ tupleType L y from (eq.trans hy.symm) ▸ hp))
    · exact hθy z hz ht

private theorem exists_transfer [Finite ι] (h : M ≅[L] N) (φ : L.Formula ι) :
    (∃ x : ι → M, φ.Realize x) ↔ (∃ y : ι → N, φ.Realize y) := by
  let ψ : L.Sentence := (φ.relabel (Sum.inr : ι → Empty ⊕ ι)).iExs ι
  have transfer := elementarilyEquivalent_iff.mp h ψ
  simpa only [ψ, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
    Sum.elim_comp_inr] using transfer

private theorem types_subset [Finite ι] (h : M ≅[L] N) (hN : (typesIn L N ι).Finite) :
    typesIn L M ι ⊆ typesIn L N ι := by
  rintro _ ⟨x,rfl⟩
  by_contra missing
  obtain ⟨φ,hx,hn⟩ := separate L x _ hN Set.Subset.rfl missing
  obtain ⟨y,hy⟩ := (exists_transfer L h φ).mp ⟨x,hx⟩
  exact hn y ⟨y,rfl⟩ hy

/-- Each finite-arity type is realized in both elementarily equivalent structures
when one of them realizes only finitely many types of that arity. -/
theorem realizedTypes_eq [Finite ι] (h : M ≅[L] N) (hM : (typesIn L M ι).Finite) :
    typesIn L M ι = typesIn L N ι := by
  have sub := types_subset L (M := N) (N := M) (ι := ι) (Eq.symm h) hM
  exact Set.Subset.antisymm (types_subset L h (hM.subset sub)) sub

/-- Tuples of a fixed type in the two models can be extended on the second
side to match arbitrarily many additional prescribed elements on the first.
The isolation formula is obtained from finitely many realized joint types. -/
theorem extendTuple [Finite κ] [Finite ι] (h : M ≅[L] N)
    (finite : (typesIn L M (ι ⊕ κ)).Finite) {x : ι → M} {y : ι → N}
    (same : tupleType L x = tupleType L y) (z : κ → M) :
    ∃ w : κ → N, tupleType L (Sum.elim x z) = tupleType L (Sum.elim y w) := by
  let p := tupleType L (Sum.elim x z)
  let S := typesIn L N (ι ⊕ κ) \ {p}
  have eq := realizedTypes_eq L h finite
  have hs : S.Finite := (eq ▸ finite : (typesIn L N (ι ⊕ κ)).Finite).subset Set.sdiff_subset
  have avoids : p ∉ S := fun h => h.2 rfl
  obtain ⟨φ,hp,other⟩ := separate L (Sum.elim x z) S hs Set.sdiff_subset avoids
  have hx : φ.iExs κ ∈ tupleType L x := Formula.realize_iExs.mpr ⟨z,hp⟩
  have hy : φ.iExs κ ∈ tupleType L y := same ▸ hx
  obtain ⟨w,hw⟩ := Formula.realize_iExs.mp hy
  refine ⟨w, ?_⟩
  by_contra diff
  exact other _ ⟨⟨_,rfl⟩, fun eq => diff eq.symm⟩ hw

end ProjectiveTypes

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes

/-- A tuple of `k` coded finite/cofinite sets over an arbitrary structure. -/
abbrev Codes (A : Type*) (k : ℕ) := Fin k → Bool × Finset A

/-- Replace each position in a finite mask by the element at that position in the tuple. -/
noncomputable def decode {A B : Type*} {k : ℕ} (v : A → B) (p : Codes A k) : Codes B k :=
  open Classical in fun j => ((p j).1, (p j).2.image v)

/-- A relation symbol on `n` entries specifies two finite/cofinite codes on these
positions. Repeated positions between coordinates and empty masks are allowed. -/
def graphLanguage (k : ℕ) : Language where
  Functions _ := Empty
  Relations n := Codes (Fin n) k × Codes (Fin n) k

/-- Use every such relation to record the graph of a single self-map. -/
@[instance_reducible] noncomputable def graphStructure {A : Type*} {k : ℕ} (f : Codes A k → Codes A k) :
    (graphLanguage k).Structure A where
  funMap := fun {_} e => nomatch e
  RelMap := fun {_} r v => f (decode v r.1) = decode v r.2

/-- The relation on codes interpreted in the second model. The number of entries
and the two masks range freely; no bound on unknown output lengths is imposed. -/
def recorded {A : Type*} {k : ℕ} [(graphLanguage k).Structure A] (x y : Codes A k) : Prop :=
  ∃ (n : ℕ) (p q : Codes (Fin n) k) (v : Fin n → A),
    decode v p = x ∧ decode v q = y ∧ Structure.RelMap (L := graphLanguage k) (p,q) v

/-- Finitely many full first-order types at each finite arity. -/
def FiniteTypes (L : Language) (A : Type*) [L.Structure A] : Prop :=
  ∀ (ι : Type) [Finite ι], (typesIn L A ι).Finite

end ProjectiveTransfer

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ}

@[simp] theorem decode_comp {U V W : Type*} (f : U → V) (g : V → W) (p : Codes U k) :
    decode g (decode f p) = decode (g ∘ f) p := by
  classical
  funext j
  simp [decode, Finset.image_image, Function.comp_def]

/-- All finitely many finite parts fit on one finite tuple. -/
theorem present {A : Type*} (x : Codes A k) :
    ∃ (n : ℕ) (p : Codes (Fin n) k) (v : Fin n → A), decode v p = x := by
  classical
  let s := Finset.univ.biUnion fun j => (x j).2
  let u : Codes s k := fun j => ((x j).1, Finset.univ.filter fun a => a.val ∈ (x j).2)
  let e := s.equivFin
  refine ⟨s.card,decode e u, (fun i => (e.symm i).val), ?_⟩
  rw [decode_comp]
  funext j
  refine Prod.ext ?_ ?_
  · rfl
  apply Finset.ext
  intro a
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    simpa [e] using (Finset.mem_filter.mp hz).2
  · intro h
    have ha : a ∈ s := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _, h⟩
    exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,by simp⟩

variable {L : Language} {A B ι κ : Type*} [L.Structure A] [L.Structure B]

/-- Restriction/reordering retains equality of complete types. -/
theorem match_subtuple {a : ι → A} {b : ι → B}
    (m : tupleType L a = tupleType L b) (f : κ → ι) : tupleType L (a ∘ f) = tupleType L (b ∘ f) := by
  ext φ
  have h := Set.ext_iff.mp m (φ.relabel f)
  simpa only [tupleType,Set.mem_ofPred_eq,Formula.realize_relabel] using h

private theorem match_eq {a : ι → A} {b : ι → B} (m : tupleType L a = tupleType L b) (i j : ι) :
    a i = a j ↔ b i = b j := by
  have h := Set.ext_iff.mp m ((Term.var i).equal (Term.var j))
  simpa [tupleType] using h

private theorem image_eq_of_match {a : ι → A} {b : ι → B}
    (m : tupleType L a = tupleType L b) (p q : Finset ι) :
    letI := Classical.decEq A
    letI := Classical.decEq B
    p.image a = q.image a → p.image b = q.image b := by
  classical
  intro h
  apply Finset.Subset.antisymm
  · rintro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have mem : a i ∈ q.image a := h ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j,hj,(match_eq m j i).mp he⟩
  · rintro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have mem : a i ∈ p.image a := h.symm ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j,hj,(match_eq m j i).mp he⟩

private theorem match_codes_one {x : ι → A} {y : ι → B}
    (same : tupleType L x = tupleType L y) (p q : Codes ι k)
    (h : decode x p = decode x q) : decode y p = decode y q := by
  funext j
  have flag := congrArg (fun a : Bool × Finset A => a.1) (congrFun h j)
  exact Prod.ext flag (image_eq_of_match same _ _ (congrArg Prod.snd (congrFun h j)))

/-- Equality of two decoded tuples of finite parts depends only on equality of entries. -/
theorem match_codes {a : ι → A} {b : ι → B} (m : tupleType L a = tupleType L b)
    (p q : Codes ι k) : decode a p = decode a q ↔ decode b p = decode b q :=
  ⟨match_codes_one m p q,match_codes_one m.symm p q⟩

/-- Different masks may be given on the two different parts of a joint tuple. -/
theorem match_cross {a : ι → A} {b : ι → B} {u : κ → A} {v : κ → B}
    (m : tupleType L (Sum.elim a u) = tupleType L (Sum.elim b v))
    (p : Codes ι k) (q : Codes κ k) : decode a p = decode u q ↔ decode b p = decode v q := by
  have h := match_codes m (decode Sum.inl p) (decode Sum.inr q)
  simpa only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] using h

/-- Atomic graph predicates in matched tuples have identical truth values. -/
theorem match_relation {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]
    {n : ℕ} {a : Fin n → A} {b : Fin n → B} (m : tupleType (graphLanguage k) a = tupleType _ b)
    (p q : Codes (Fin n) k) :
    Structure.RelMap (L := graphLanguage k) (p,q) a ↔ Structure.RelMap (L := graphLanguage k) (p,q) b := by
  let r : (graphLanguage k).Relations n := (p,q)
  have h := Set.ext_iff.mp m (r.formula fun i => Term.var i)
  change (r.formula fun i => Term.var i).Realize a ↔ (r.formula fun i => Term.var i).Realize b at h
  simpa only [Formula.realize_rel,Term.realize] using h

end ProjectiveTransfer

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ} {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]

/-- The source structure's predicates record exactly the given map, even when the
coordinate masks overlap. This property holds by definition in `graphStructure f`. -/
def Records (f : Codes A k → Codes A k) : Prop :=
  ∀ {n : ℕ} (p q : Codes (Fin n) k) (v : Fin n → A),
    Structure.RelMap (L := graphLanguage k) (p,q) v ↔ f (decode v p) = decode v q

private theorem record_of_match {ι : Type} [Finite ι] {f : Codes A k → Codes A k}
    (hf : Records f) {a : ι → A} {b : ι → B}
    (m : tupleType (graphLanguage k) a = tupleType _ b) (p q : Codes ι k)
    (h : f (decode a p) = decode a q) : recorded (decode b p) (decode b q) := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have ma := match_subtuple m e.symm
  refine ⟨_, decode e p, decode e q, b ∘ e.symm, ?_, ?_, ?_⟩
  · simp [Function.comp_assoc]
  · simp [Function.comp_assoc]
  apply (match_relation ma _ _).mp
  apply (hf _ _ _).mpr
  simpa [Function.comp_assoc] using h

/-- Moving the enumeration of the finite parts, or its shape, preserves the
value of the recorded graph. Matching a larger tuple on the first side verifies
all potential other presentations without assuming a fixed output size. -/
theorem compareGraph {ι : Type} [Finite ι] {f : Codes A k → Codes A k}
    (hf : Records f) (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    {a : ι → A} {b : ι → B} (m : tupleType (graphLanguage k) a = tupleType _ b) (p q : Codes ι k) :
    f (decode a p) = decode a q ↔ recorded (decode b p) (decode b q) := by
  refine ⟨record_of_match hf m p q, ?_⟩
  rintro ⟨n,u,v,b',hu,hv,r⟩
  have sameTypes := realizedTypes_eq (graphLanguage k) eq (fin (ι ⊕ Fin n))
  obtain ⟨a',joint⟩ := extendTuple (graphLanguage k) (Eq.symm eq) (sameTypes ▸ fin _) m.symm b'
  have sub := match_subtuple joint (Sum.inr : Fin n → ι ⊕ Fin n)
  simp only [Sum.elim_comp_inr] at sub
  have rel := (hf u v a').mp ((match_relation sub u v).mp r)
  have h₁ := (match_cross joint p u).mp hu.symm
  have h₂ := (match_cross joint q v).mp hv.symm
  rwa [h₁,h₂]

/-- Interpret a pair whose masks use disjoint lists of entries. -/
theorem comparePair {ι κ : Type} [Finite ι] [Finite κ] {f : Codes A k → Codes A k}
    (hf : Records f) (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    {a : ι → A} {b : ι → B} {u : κ → A} {v : κ → B}
    (m : tupleType (graphLanguage k) (Sum.elim a u) = tupleType _ (Sum.elim b v))
    (p : Codes ι k) (q : Codes κ k) : f (decode a p) = decode u q ↔ recorded (decode b p) (decode v q) := by
  have h := compareGraph hf eq fin m (decode Sum.inl p) (decode Sum.inr q)
  simpa only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] using h

/-- Every tuple on the second side can first be matched on the first. -/
theorem match_from_right {ι : Type} [Finite ι] (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) (b : ι → B) :
    ∃ a : ι → A, tupleType (graphLanguage k) a = tupleType _ b := by
  have hs := realizedTypes_eq (graphLanguage k) eq (fin ι)
  change tupleType (graphLanguage k) b ∈ typesIn (graphLanguage k) A ι
  rw [hs]
  exact ⟨b,rfl⟩

/-- The graph interpreted on the second side is total. -/
theorem graph_total {f : Codes A k → Codes A k} (hf : Records f) (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) (x : Codes B k) : ∃ y, recorded x y := by
  obtain ⟨n,p,b,rfl⟩ := present x
  obtain ⟨a,m⟩ := match_from_right eq fin b
  obtain ⟨l,q,z,hz⟩ := present (f (decode a p))
  obtain ⟨w,joint⟩ := extendTuple (graphLanguage k) eq (fin (Fin n ⊕ Fin l)) m z
  exact ⟨_,(comparePair hf eq fin joint p q).mp hz.symm⟩

/-- The graph interpreted on the second side is single-valued. -/
theorem graph_functional {f : Codes A k → Codes A k} (hf : Records f) (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) {x y z : Codes B k} (hy : recorded x y)
    (hz : recorded x z) : y = z := by
  obtain ⟨n,p,q,b,rfl,rfl,r⟩ := hy
  obtain ⟨l,u,v,w,hu,rfl,t⟩ := hz
  obtain ⟨ab,m⟩ := match_from_right eq fin (Sum.elim b w)
  let a := ab ∘ Sum.inl
  let z := ab ∘ Sum.inr
  have joint : tupleType (graphLanguage k) (Sum.elim a z) = tupleType _ (Sum.elim b w) := by
    simpa [a,z] using m
  have m₁ := match_subtuple m (Sum.inl : Fin n → Fin n ⊕ Fin l)
  have m₂ := match_subtuple m (Sum.inr : Fin l → Fin n ⊕ Fin l)
  simp only [Sum.elim_comp_inl,Sum.elim_comp_inr] at m₁ m₂
  have h₁ := (hf p q a).mp ((match_relation m₁ p q).mpr r)
  have h₂ := (hf u v z).mp ((match_relation m₂ u v).mpr t)
  have h : decode a p = decode z u := (match_cross joint p u).mpr hu.symm
  exact (match_cross joint q v).mp (h₁.symm.trans ((congrArg f h).trans h₂))

end ProjectiveTransfer

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ} {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]

private def MatchesMaps (f : Codes A k → Codes A k) (g : Codes B k → Codes B k) : Prop :=
  ∀ {ι : Type} [Finite ι] {a : ι → A} {b : ι → B},
    tupleType (graphLanguage k) a = tupleType _ b → ∀ p q : Codes ι k,
      f (decode a p) = decode a q ↔ g (decode b p) = decode b q

private theorem lift_surjective {f : Codes A k → Codes A k} {g : Codes B k → Codes B k}
    (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    (graphs : MatchesMaps f g) (surj : Surjective f) : Surjective g := by
  intro x
  obtain ⟨n,p,b,rfl⟩ := present x
  obtain ⟨a,m⟩ := match_from_right eq fin b
  obtain ⟨pre,hpre⟩ := surj (decode a p)
  obtain ⟨l,q,z,rfl⟩ := present pre
  obtain ⟨w,joint⟩ := extendTuple (graphLanguage k) eq (fin (Fin n ⊕ Fin l)) m z
  have t := graphs joint (decode Sum.inr q) (decode Sum.inl p)
  simp only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] at t
  exact ⟨_,t.mp hpre⟩

private theorem lift_injective {f : Codes A k → Codes A k} {g : Codes B k → Codes B k}
    (eq : A ≅[graphLanguage k] B) (finB : FiniteTypes (graphLanguage k) B)
    (graphs : MatchesMaps f g) (inj : Injective g) : Injective f := by
  intro x y h
  obtain ⟨n,p,a,rfl⟩ := present x
  obtain ⟨m,q,b,rfl⟩ := present y
  obtain ⟨l,r,z,hz⟩ := present (f (decode a p))
  let v := Sum.elim a (Sum.elim b z)
  let X := decode (Sum.inl : Fin n → Fin n ⊕ (Fin m ⊕ Fin l)) p
  let Y := decode (fun j : Fin m => Sum.inr (Sum.inl j) : Fin m → Fin n ⊕ (Fin m ⊕ Fin l)) q
  let Z := decode (fun j : Fin l => Sum.inr (Sum.inr j) : Fin l → Fin n ⊕ (Fin m ⊕ Fin l)) r
  have ex : decode v X = decode a p := by simp only [X,decode_comp]; rfl
  have ey : decode v Y = decode b q := by simp only [Y,decode_comp]; rfl
  have ez : decode v Z = decode z r := by simp only [Z,decode_comp]; rfl
  obtain ⟨w,mw⟩ := match_from_right (Eq.symm eq) finB v
  have hx := (graphs mw.symm X Z).mp (by rw [ex,ez,hz])
  have hy := (graphs mw.symm Y Z).mp (by rw [ey,ez,hz,h])
  exact ex.symm.trans (((match_codes mw X Y).mp (inj (hx.trans hy.symm))).trans ey)

/-- In any elementarily equivalent structure, the graph predicates of a map on
coded finite/cofinite sets define a unique self-map. Surjectivity and injectivity
are both preserved and reflected. Finite type spectra are only required of the
source structure, and there is no uniform bound assumption on output lengths. -/
theorem transferGraph (k : ℕ) {M N : Type*} (f : Codes M k → Codes M k)
    [(graphLanguage k).Structure N] :
    letI := graphStructure f
    M ≅[graphLanguage k] N → FiniteTypes (graphLanguage k) M →
      ∃ g : Codes N k → Codes N k,
        (∀ x y, g x = y ↔ recorded x y) ∧
        (Surjective f ↔ Surjective g) ∧ (Injective f ↔ Injective g) := by
  let := graphStructure f
  intro eq fin
  have src : Records f := by intro n p q t; rfl
  have fin' : FiniteTypes (graphLanguage k) N := fun ι _ =>
    (realizedTypes_eq _ eq (fin ι)) ▸ fin ι
  let g (x : Codes N k) := Classical.choose (graph_total src eq fin x)
  have prop (x y : Codes N k) : g x = y ↔ recorded x y := by
    have chosen := Classical.choose_spec (graph_total src eq fin x)
    exact ⟨fun h => h ▸ chosen, graph_functional src eq fin chosen⟩
  have graphs : MatchesMaps f g := fun {_ _ _ _} h p q =>
    (compareGraph src eq fin h p q).trans (prop _ _).symm
  have reverse : MatchesMaps g f := fun {_ _ _ _} h p q => (graphs h.symm p q).symm
  exact ⟨g,prop,⟨lift_surjective eq fin graphs, lift_surjective (Eq.symm eq) fin' reverse⟩,
    ⟨lift_injective (Eq.symm eq) fin reverse, lift_injective eq fin' graphs⟩⟩

end ProjectiveTransfer

@[expose] public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes ProjectiveBlocks Function

/-- Permuting the blocks positionwise in the second structure preserves every
named first-order graph predicate. The core is pointwise fixed. -/
def BlockModel (c d k : ℕ) [(graphLanguage k).Structure (Point c d)] : Prop :=
  ∀ (σ : _root_.Equiv.Perm ℕ) {n : ℕ} (r : (graphLanguage k).Relations n) (v : Fin n → Point c d),
    Structure.RelMap r (relabel σ ∘ v) ↔ Structure.RelMap r v

private def blockAut {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k)
    (σ : _root_.Equiv.Perm ℕ) : Point c d ≃[graphLanguage k] Point c d where
  toEquiv := relabel σ
  map_fun' := fun f => nomatch f
  map_rel' := s σ

private def small {c d n : ℕ} : Fin c ⊕ (Fin n × Fin d) → Point c d :=
  Sum.map id fun a => (a.1.val, a.2)

/-- Every finite tuple lies in the permutation orbit of one using only as many
block indices as the length of the tuple. -/
private theorem normalize {c d : ℕ} {ι : Type} [Fintype ι] (v : ι → Point c d) :
    ∃ (σ : _root_.Equiv.Perm ℕ) (w : ι → Fin c ⊕ (Fin (Fintype.card ι) × Fin d)),
      relabel σ ∘ v = small ∘ w := by
  classical
  let tag (x : Point c d) : ℕ := Sum.elim (fun _ => 0) Prod.fst x
  let U := Finset.univ.image (tag ∘ v)
  have card : U.card ≤ Fintype.card ι := by simpa [U] using (Finset.card_image_le (f := tag ∘ v) (s := Finset.univ))
  let e := U.equivFin
  obtain ⟨σ,hσ⟩ := _root_.Equiv.Perm.exists_extending_pair (fun a : U => a.val)
    (fun a : U => (e a).val) Subtype.val_injective (Fin.val_injective.comp e.injective)
  have bound (i : ι) : σ (tag (v i)) < Fintype.card ι := by
    let a : U := ⟨_,Finset.mem_image_of_mem (tag ∘ v) (Finset.mem_univ i)⟩
    exact (hσ a).symm ▸ Nat.lt_of_lt_of_le (e a).isLt card
  have position (i : ι) : ∃ w, relabel σ (v i) = small (n := Fintype.card ι) w := by
    cases hx : v i with
    | inl t => exact ⟨.inl t,rfl⟩
    | inr t =>
      have h := bound i
      rw [hx] at h
      exact ⟨.inr (⟨σ t.1,h⟩,t.2),rfl⟩
  exact ⟨σ,fun i => (position i).choose, funext fun i => (position i).choose_spec⟩

private theorem blockTypes {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k) :
    FiniteTypes (graphLanguage k) (Point c d) := by
  intro ι _
  classical
  let := Fintype.ofFinite ι
  let T := Fin c ⊕ (Fin (Fintype.card ι) × Fin d)
  let ts (w : ι → T) := tupleType (graphLanguage k) (small ∘ w)
  apply (Set.finite_range ts).subset
  rintro _ ⟨v,rfl⟩
  obtain ⟨σ,w,hσ⟩ := normalize v
  refine ⟨w,?_⟩
  change tupleType _ (small ∘ w) = tupleType _ v
  rw [← hσ]
  ext φ
  exact StrongHomClass.realize_formula (blockAut s σ) φ

private theorem rename_decode {c d k : ℕ} (σ : _root_.Equiv.Perm ℕ) (x : Code c d k) :
    rename σ x = decode (relabel σ) x := by
  funext j
  apply Prod.ext
  · rfl
  · ext a
    simp only [rename,decode,Finset.mem_map,Finset.mem_image]
    rfl

private theorem rel_invariant {c d k : ℕ} [(graphLanguage k).Structure (Point c d)] (s : BlockModel c d k)
    (σ : _root_.Equiv.Perm ℕ) {x y : Code c d k} (h : recorded x y) : recorded (rename σ x) (rename σ y) := by
  obtain ⟨n,p,q,v,rfl,rfl,r⟩ := h
  exact ⟨n,p,q,relabel σ ∘ v, (rename_decode σ _ ▸ decode_comp _ _ _).symm,
    (rename_decode σ _ ▸ decode_comp _ _ _).symm, (s σ _ _).mpr r⟩

/-- The obstruction after passing to a countable symmetric block model. If a
surjection's graph structure is elementarily equivalent to such a model, the
original map is injective. No check on the number of tuple types or on the
lengths of the finite parts is assumed. -/
theorem obstructionOfBlockModel {M : Type*} (c d k : ℕ) (f : Codes M k → Codes M k)
    [(graphLanguage k).Structure (Point c d)] (model : BlockModel c d k) :
    letI := graphStructure f
    M ≅[graphLanguage k] (Point c d) → Surjective f → Injective f := by
  let := graphStructure f
  intro eq surj
  have finB := blockTypes model
  have fin : FiniteTypes (graphLanguage k) M := fun ι _ =>
    (realizedTypes_eq _ (Eq.symm eq) (finB ι)) ▸ finB ι
  obtain ⟨g,isGraph,sg,ig⟩ := transferGraph k f eq fin
  have equiv : Equivariant g := by
    intro σ x
    exact (isGraph _ _).mpr (rel_invariant model σ ((isGraph x _).mp rfl))
  exact ig.mpr <| (equivariantSurjection g equiv (sg.mp surj)).2

end ProjectiveTransfer
