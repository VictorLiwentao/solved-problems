module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

open scoped Matrix

namespace ResistanceLifts

/-- Kirchhoff's equations for one unit of current injected at `a` and removed at `b`
with a unit conductance on each edge. -/
noncomputable def UnitPotential {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V) (u : V → ℝ) : Prop := by
  classical
  exact G.lapMatrix ℝ *ᵥ u = fun i => (if i = a then 1 else 0) - (if i = b then 1 else 0)

/-- Effective resistance is the voltage drop under a unit current. The fallback is
only relevant if Kirchhoff's equations are insoluble, e.g. in disconnected graphs. -/
noncomputable def resistance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V) : ℝ := by
  classical
  exact if h : ∃ u, UnitPotential G a b u then h.choose a - h.choose b else 0

/-- Any solution to the unit current equations gives the same terminal drop. -/
theorem resistance_of_potential {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Reachable a b) {u : V → ℝ}
    (hu : UnitPotential G a b u) : resistance G a b = u a - u b := by
  classical
  have ex : ∃ v, UnitPotential G a b v := ⟨u, hu⟩
  rw [resistance, dite_eq_left ex]
  have he : G.lapMatrix ℝ *ᵥ ex.choose = G.lapMatrix ℝ *ᵥ u := ex.choose_spec.trans hu.symm
  have hz : G.lapMatrix ℝ *ᵥ (ex.choose - u) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
  have hv := (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hz) a b hab
  simp only [Pi.sub_apply] at hv
  linarith

end ResistanceLifts

open Finset
open scoped Matrix Classical

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete the two-element orbits of an involution from the complete graph.
Its fixed vertices retain all edges. -/
def minusMatching (σ : Equiv.Perm V) (hσ : Function.Involutive σ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ y ≠ σ x
  symm := ⟨fun x y h ↦ ⟨h.1.symm, fun he ↦ h.2 (by rw [he,hσ])⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

noncomputable def current (a b : V) (x : V) : ℝ :=
  (if x = a then 1 else 0) - (if x = b then 1 else 0)

noncomputable def matchingPotential (σ : Equiv.Perm V) (a b : V) (x : V) : ℝ :=
  let n : ℝ := Fintype.card V
  current a b x / n + (current a b x - current a b (σ x)) / (n*(n-2))

private theorem lap_minus (σ : Equiv.Perm V) (hσ : Function.Involutive σ) (f : V → ℝ) (x : V) :
    ((minusMatching σ hσ).lapMatrix ℝ *ᵥ f) x =
      (Fintype.card V : ℝ) * f x - (∑ y, f y) - (f x - f (σ x)) := by
  classical
  let G := minusMatching σ hσ
  change (G.lapMatrix ℝ *ᵥ f) x = _
  rw [G.lapMatrix_mulVec_apply']
  have part : G.neighborFinset x ⊆ univ.erase (σ x) := by
    intro y hy
    have adj := (G.mem_neighborFinset x y).mp hy
    exact mem_erase.mpr ⟨adj.2, mem_univ _⟩
  rw [Finset.sum_subset part (by
    intro y hy hn
    have he : x = y := by
      by_contra hne
      exact hn ((G.mem_neighborFinset x y).mpr ⟨hne,(mem_erase.mp hy).1⟩)
    rw [he, sub_self])]
  have all := Finset.sum_erase_add univ (f := fun y ↦ f x - f y) (mem_univ (σ x))
  rw [show (∑ y : V, (f x - f y)) = (Fintype.card V : ℝ) * f x - ∑ y, f y by
    rw [Finset.sum_sub_distrib]; simp] at all
  linarith

/-- An explicit solution of all Kirchhoff equations after deleting a matching,
with no choice of matrix inverse or numerical tolerance. -/
theorem matching_potential (σ : Equiv.Perm V) (hσ : Function.Involutive σ)
    (nlarge : 2 < Fintype.card V) (a b : V) :
    ResistanceLifts.UnitPotential (minusMatching σ hσ) a b (matchingPotential σ a b) := by
  classical
  let n : ℝ := Fintype.card V
  let d := current a b
  have hn : (2:ℝ) < n := by dsimp [n]; exact_mod_cast nlarge
  have hn0 : n ≠ 0 := by linarith
  have hn2 : n - 2 ≠ 0 := by linarith
  have hd : ∑ y, d y = 0 := by simp [d, current, Finset.sum_sub_distrib]
  have he : ∑ y, d (σ y) = ∑ y, d y := Equiv.sum_comp σ d
  have zero : ∑ y, matchingPotential σ a b y = 0 := by
    change (∑ y, (d y/n + (d y-d (σ y))/(n*(n-2)))) = 0
    simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, he, hd]
    simp
  ext x
  rw [lap_minus, zero]
  change n * (d x/n + (d x-d (σ x))/(n*(n-2))) - 0 -
    (d x/n + (d x-d (σ x))/(n*(n-2)) - (d (σ x)/n + (d (σ x)-d (σ (σ x)))/(n*(n-2)))) = d x
  rw [hσ]
  field_simp
  ring

end ResistanceRecovery

namespace ResistanceRecovery

/-- Four marked vertices and k other labeled vertices, for every n = k+4. -/
abbrev Vertex (k : ℕ) := (Bool × Bool) ⊕ Fin k
abbrev Query := Bool × Bool

def partner {k : ℕ} (t : Bool) : Vertex k → Vertex k
  | .inl (i,j) => .inl (if t then (!i,j) else (i,!j))
  | .inr x => .inr x

theorem twice {k : ℕ} (t : Bool) : Function.Involutive (@partner k t) := by
  rintro (⟨i,j⟩ | x)
  · cases t <;> simp [partner]
  · rfl

def swapPartner {k : ℕ} (t : Bool) : Equiv.Perm (Vertex k) :=
  ⟨partner t, partner t, twice t, twice t⟩

@[simp] theorem swapPartner_apply {k : ℕ} (t : Bool) (x : Vertex k) :
    swapPartner t x = partner t x := rfl

def witness (k : ℕ) (t : Bool) : SimpleGraph (Vertex k) := minusMatching (swapPartner t) (twice t)

def endpoints {k : ℕ} : Query → Vertex k × Vertex k
  | (false,j) => (.inl (j,false), .inl (j,true))
  | (true,j) => (.inl (false,j), .inl (true,j))

instance {k : ℕ} (t : Bool) : DecidableRel (witness k t).Adj :=
  fun x y ↦ inferInstanceAs (Decidable (x ≠ y ∧ y ≠ partner t x))

private theorem connected (k : ℕ) (t : Bool) : (witness k t).Connected := by
  let root : Vertex k := .inl (false,false)
  let diag : Vertex k := .inl (true,true)
  apply ((witness k t).connected_iff_exists_forall_reachable).mpr
  refine ⟨root, fun w ↦ ?_⟩
  cases w with
  | inr x =>
    apply SimpleGraph.Adj.reachable
    change root ≠ Sum.inr x ∧ Sum.inr x ≠ partner t root
    cases t <;> simp [root,partner]
  | inl p =>
    obtain ⟨i,j⟩ := p
    have rd : (witness k t).Adj root diag := by
      cases t <;> simp [witness, minusMatching, partner, root, diag]
    by_cases eq : root = Sum.inl (i,j)
    · rw [← eq]
    by_cases adj : (witness k t).Adj root (Sum.inl (i,j))
    · exact adj.reachable
    apply rd.reachable.trans
    apply SimpleGraph.Adj.reachable
    cases t <;> cases i <;> cases j <;>
      simp_all [witness, minusMatching, partner, root, diag]

private theorem special {k : ℕ} {x y : Vertex k} (t : Bool) (hne : x ≠ y) (hy : y = partner t x) :
    ∃ q : Query, endpoints q = (x,y) ∨ endpoints q = (y,x) := by
  subst y
  cases x with
  | inr _ => exact False.elim (hne rfl)
  | inl p =>
    obtain ⟨i,j⟩ := p
    cases t
    · refine ⟨(false,i), ?_⟩
      cases j <;> simp [partner,endpoints]
    · refine ⟨(true,j), ?_⟩
      cases i <;> simp [partner,endpoints]

private theorem same_elsewhere (k : ℕ) (x y : Vertex k)
    (away : ∀ q : Query, endpoints q ≠ (x,y) ∧ endpoints q ≠ (y,x)) :
    (witness k false).Adj x y ↔ (witness k true).Adj x y := by
  have keep (hne : x ≠ y) (t : Bool) : y ≠ partner t x := by
    intro he
    obtain ⟨q, h | h⟩ := special t hne he
    · exact (away q).1 h
    · exact (away q).2 h
  exact ⟨fun h ↦ ⟨h.1,keep h.1 _⟩, fun h ↦ ⟨h.1,keep h.1 _⟩⟩

private theorem different (k : ℕ) : witness k false ≠ witness k true := by
  let u : Vertex k := .inl (false,false)
  let v : Vertex k := .inl (false,true)
  have ja : (witness k true).Adj u v := by simp [u,v,witness,minusMatching,partner]
  have no : ¬(witness k false).Adj u v := by simp [u,v,witness,minusMatching,partner]
  exact fun h ↦ no (h ▸ ja)

noncomputable def radius (k : ℕ) : ℝ := 1 / (((k:ℝ)+(4:ℕ)) * ((k:ℝ)+(2:ℕ)))

/-- The four readings are exact voltage drops on connected unit-conductance
graphs. Their variation is precisely twice the obstruction radius. -/
theorem reading (k : ℕ) (t : Bool) (q : Query) :
    let (a,b) := @endpoints k q
    ResistanceLifts.resistance (witness k t) a b =
      2 / ((k:ℝ)+4) + (if t = q.1 then 4 else 2) * radius k := by
  have card : Fintype.card (Vertex k) = k + 4 := by simp [Vertex]; omega
  have size : 2 < Fintype.card (Vertex k) := by omega
  obtain ⟨i,j⟩ := q
  cases t <;> cases i <;> cases j
  all_goals
    dsimp only [endpoints, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
    rw [ResistanceLifts.resistance_of_potential (connected k _ _ _)
      (matching_potential (swapPartner _) (twice _) size _ _)]
    have sub : (k:ℝ) + 4 - 2 = (k:ℝ) + 2 := by ring
    simp [matchingPotential, current, partner, radius, card, sub, div_eq_mul_inv]
    ring

/-- At the claimed error radius the same rational readings and the same known
adjacencies are compatible with two distinct labeled connected graphs. -/
theorem four_unknown_pairs (k : ℕ) :
    ∃ G H : SimpleGraph (Vertex k), G.Connected ∧ H.Connected ∧ G ≠ H ∧
      (∀ x y, (∀ q : Query, endpoints q ≠ (x,y) ∧ endpoints q ≠ (y,x)) →
        (G.Adj x y ↔ H.Adj x y)) ∧
      ∃ y : Query → ℚ, ∀ q,
        let (a,b) := endpoints q
        |(y q : ℝ) - ResistanceLifts.resistance G a b| = radius k ∧
        |(y q : ℝ) - ResistanceLifts.resistance H a b| = radius k := by
  refine ⟨witness k false,witness k true,connected k false,connected k true,different k,
    same_elsewhere k, fun _ ↦ 2/((k:ℚ)+4) + 3/(((k:ℚ)+4)*((k:ℚ)+2)), ?_⟩
  intro q
  have h0 : 0 ≤ radius k := by unfold radius; positivity
  have r0 := reading k false q
  have r1 := reading k true q
  have hm : (3:ℝ) / (((k:ℝ)+4)*((k:ℝ)+2)) = 3 * radius k := by unfold radius; ring
  have low (c r : ℝ) : c + 3*r - (c + 2*r) = r := by ring
  have high (c r : ℝ) : c + 3*r - (c + 4*r) = -r := by ring
  obtain ⟨i,j⟩ := q
  cases i <;> dsimp only [endpoints, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at r0 r1 ⊢
  all_goals
    rw [r0,r1]
    push_cast
    simp [hm, low, high, abs_of_nonneg h0]

/-- The decoder sees all adjacencies except the four specified unordered pairs. -/
noncomputable def knownView {k : ℕ} (G : SimpleGraph (Vertex k)) (x y : Vertex k) : Option Bool := by
  classical
  exact if ∃ q : Query, endpoints q = (x,y) ∨ endpoints q = (y,x)
    then none else some (decide (G.Adj x y))

/-- Even unrestricted decoders cannot always recover the graph from its known
entries and four rational answers with this much allowed adversarial error. -/
theorem no_decoder (k : ℕ) :
    ¬ ∃ D : (Vertex k → Vertex k → Option Bool) → (Query → ℚ) → SimpleGraph (Vertex k),
      ∀ G : SimpleGraph (Vertex k), G.Connected → ∀ z : Query → ℚ,
        (∀ q, |(z q : ℝ) - ResistanceLifts.resistance G (endpoints q).1 (endpoints q).2| ≤ radius k) →
        D (knownView G) z = G := by
  classical
  rintro ⟨D, works⟩
  obtain ⟨G,H,hG,hH,diff,known,z,hz⟩ := four_unknown_pairs k
  have same : knownView G = knownView H := by
    funext x y
    unfold knownView
    split
    · rfl
    · rename_i away
      push Not at away
      rw [propext (known x y away)]
  have atG := works G hG z (fun q ↦ ((hz q).1).le)
  have atH := works H hH z (fun q ↦ ((hz q).2).le)
  exact diff (atG.symm.trans ((congrArg (fun view ↦ D view z) same).trans atH))

end ResistanceRecovery

end

section

open Matrix
open scoped MatrixOrder

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

private theorem trace_product_nonneg {A B : Mat} (ha : A.PosSemidef) (hb : B.PosSemidef) :
    0 ≤ (A*B).trace := by
  obtain ⟨X, hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha.nonneg
  rw [hx, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle B]
  simpa only [mul_assoc] using (hb.mul_mul_conjTranspose_same X).trace_nonneg

private theorem inverse_lower {A : Mat} (ha : A.PosDef) {m : ℝ} (hm : 0 < m)
    (h : A ≤ m • (1 : Mat)) : (m⁻¹ • (1 : Mat)) ≤ A⁻¹ := by
  have hu := ha.isUnit
  have hl : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ (A.isUnit_iff_isUnit_det.mp hu)
  have hr : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (A.isUnit_iff_isUnit_det.mp hu)
  have hd := (Matrix.le_iff.mp h).nonneg
  have hc : Commute A⁻¹ (m • (1 : Mat) - A) := by
    show _ * _ = _ * _
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul, hl, hr]
  have hp := Commute.mul_nonneg ha.posSemidef.inv.nonneg hd hc
  rw [mul_sub, Matrix.mul_smul, mul_one, hl] at hp
  have hps := (Matrix.nonneg_iff_posSemidef.mp hp).smul (inv_nonneg.mpr hm.le)
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hm.ne', one_smul] at hps
  exact Matrix.le_iff.mpr hps

/-- Strong monotonicity for the inverse of two positive definite regularized
Laplacians bounded above by the same scalar multiple of the identity. -/
theorem inverse_trace_bound (A C : Mat) (ha : A.PosDef) (hc : C.PosDef)
    {m : ℝ} (hm : 0 < m) (hA : A ≤ m • (1 : Mat)) (hC : C ≤ m • (1 : Mat)) :
    m⁻¹ ^ 2 * ((A-C)*(A-C)).trace ≤ ((A-C)*(C⁻¹-A⁻¹)).trace := by
  let B := A-C
  let r := m⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr hm.le
  have hb : Bᴴ = B := (ha.isHermitian.sub hc.isHermitian).eq
  have hs := Matrix.le_iff.mp (inverse_lower ha hm hA)
  have ht := Matrix.le_iff.mp (inverse_lower hc hm hC)
  have hba : (B*A⁻¹*B).PosSemidef := by
    simpa only [hb] using ha.posSemidef.inv.mul_mul_conjTranspose_same B
  have h₁ := trace_product_nonneg hba ht
  have h₂ := (hs.mul_mul_conjTranspose_same B).trace_nonneg
  rw [hb, mul_sub B A⁻¹, sub_mul (B*A⁻¹), Matrix.mul_smul, mul_one, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h₂
  rw [mul_sub (B*A⁻¹*B) C⁻¹, Matrix.mul_smul, mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h₁
  have hi : C⁻¹ - A⁻¹ = A⁻¹*B*C⁻¹ := by
    dsimp [B]
    rw [mul_sub, sub_mul, Matrix.nonsing_inv_mul _ (A.isUnit_iff_isUnit_det.mp ha.isUnit),
      one_mul, mul_assoc, Matrix.mul_nonsing_inv _ (C.isUnit_iff_isUnit_det.mp hc.isUnit), mul_one]
  rw [hi]
  change r^2 * (B*B).trace ≤ (B*(A⁻¹*B*C⁻¹)).trace
  rw [← mul_assoc B, ← mul_assoc B]
  dsimp [r] at *
  nlinarith [mul_nonneg hr h₂]

end ResistanceRecovery

end

section

open Finset Matrix
open scoped MatrixOrder

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

noncomputable def weightedLap (w : Mat) : Mat := diagonal (fun i => ∑ j, w i j) - w

/-- Ground the constant eigenspace by assigning the constant matrix value W.
Its quadratic form vanishes on every difference of two coordinate vectors. -/
noncomputable def grounded (w : Mat) (W : ℝ) : Mat := weightedLap w + Matrix.of (fun _ _ => W)

private theorem lap_sub (u v : Mat) : weightedLap (u-v) = weightedLap u - weightedLap v := by
  ext i j
  by_cases h : i=j <;> simp [weightedLap, h, Finset.sum_sub_distrib] <;> ring

theorem grounded_sub (u v : Mat) (W : ℝ) : grounded u W - grounded v W = weightedLap (u-v) := by
  rw [grounded, grounded, lap_sub, add_sub_add_right_eq_sub]

private theorem lap_symm (w : Mat) (h : ∀ i j, w i j = w j i) : (weightedLap w).IsHermitian := by
  ext i j
  by_cases e : i=j <;> simp [weightedLap, e, Ne.symm, h j i, Matrix.conjTranspose_apply]

private theorem quad_lap (w : Mat) (h : ∀ i j, w i j = w j i) (x : V → ℝ) :
    2 * (star x ⬝ᵥ (weightedLap w *ᵥ x)) = ∑ i, ∑ j, w i j * (x i-x j)^2 := by
  have swap : (∑ i, ∑ j, w i j * x j^2) = ∑ i, ∑ j, w i j * x i^2 := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [h j i]
  have row : star x ⬝ᵥ (weightedLap w *ᵥ x) =
      ∑ i, ∑ j, (w i j * x i^2 - w i j * x i * x j) := by
    rw [weightedLap, sub_mulVec]
    unfold dotProduct
    apply sum_congr rfl
    intro i _
    rw [Pi.sub_apply, Pi.star_apply, star_trivial, Matrix.mulVec_diagonal, mul_sub,
      Matrix.mulVec, dotProduct, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> apply sum_congr rfl <;> intro j _ <;> ring
  rw [row]
  have expand (i j : V) : w i j * (x i - x j)^2 =
      w i j*x i^2 - 2*(w i j*x i*x j) + w i j*x j^2 := by ring
  simp_rw [expand]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, swap]
  ring

omit [DecidableEq V] in
private theorem quad_const (W : ℝ) (x : V → ℝ) :
    star x ⬝ᵥ ((Matrix.of (fun _ _ : V => W)) *ᵥ x) = W*(∑ i, x i)^2 := by
  simp only [dotProduct, mulVec, of_apply, Pi.star_apply, star_trivial, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

theorem lap_psd (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j) :
    (weightedLap w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (lap_symm w h)
  intro x
  have H := quad_lap w h x
  have : 0 ≤ ∑ i, ∑ j, w i j * (x i-x j)^2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hn i j) (sq_nonneg _)
  linarith

/-- The complete graph of capacity W bounds the grounded Laplacian in Loewner order. -/
theorem grounded_le (w : Mat) (h : ∀ i j, w i j = w j i) {W : ℝ} (hw : ∀ i j, w i j ≤ W) :
    grounded w W ≤ ((Fintype.card V:ℝ)*W) • (1 : Mat) := by
  let c : Mat := Matrix.of (fun i j => W-w i j)
  have hc := lap_psd c (fun i j => by simp [c,h j i]) (fun i j => sub_nonneg.mpr (hw i j))
  apply Matrix.le_iff.mpr
  convert hc using 1
  ext i j
  by_cases hij : i=j <;> simp [grounded, weightedLap, c,
    hij, Finset.sum_sub_distrib] <;> ring

/-- The graph of positive conductances ignores diagonal entries, which cancel
in the Laplacian. -/
def supportGraph (w : Mat) (h : ∀ i j, w i j = w j i) : SimpleGraph V where
  Adj i j := i ≠ j ∧ 0 < w i j
  symm := ⟨fun i j e => ⟨e.1.symm, h i j ▸ e.2⟩⟩
  loopless := ⟨fun _ e => e.1 rfl⟩

theorem grounded_pos (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j)
    (conn : (supportGraph w h).Connected) {W : ℝ} (hW : 0 < W) : (grounded w W).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos ((lap_symm w h).add (by
    ext i j
    simp [conjTranspose_apply]))
  intro x hx
  change 0 < star x ⬝ᵥ ((weightedLap w + Matrix.of (fun _ _ => W)) *ᵥ x)
  rw [add_mulVec, dotProduct_add, quad_const]
  have lp := (lap_psd w h hn).dotProduct_mulVec_nonneg x
  by_contra! bad
  have zero : (∑ i, x i) = 0 := by
    by_contra nz
    have pos := mul_pos hW (sq_pos_of_ne_zero nz)
    linarith
  have lzero : star x ⬝ᵥ (weightedLap w *ᵥ x) = 0 := by rw [zero] at bad; linarith
  have sumzero := (quad_lap w h x).symm
  rw [lzero, mul_zero] at sumzero
  have nn (i j : V) := mul_nonneg (hn i j) (sq_nonneg (x i-x j))
  have same {i j : V} (e : (supportGraph w h).Adj i j) : x i = x j := by
    have row := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg (fun j _ => nn i j))).mp sumzero i (mem_univ _)
    have term := (sum_eq_zero_iff_of_nonneg (fun j _ => nn i j)).mp row j (mem_univ _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp term).resolve_left e.2.ne'))
  obtain ⟨i⟩ := conn.nonempty
  have all (j : V) : x i = x j := by
    obtain ⟨p⟩ := conn.preconnected i j
    induction p with
    | nil => rfl
    | cons e _ ih => exact (same e).trans ih
  have sum : (∑ j, x j) = (Fintype.card V:ℝ)*x i := by simp_rw [← all]; simp
  have : Nonempty V := ⟨i⟩
  have xi : x i = 0 := (mul_eq_zero.mp (sum.symm.trans zero)).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  exact hx (funext fun j => (all j).symm.trans xi)

end ResistanceRecovery

end

section

open Finset Matrix
open scoped MatrixOrder

namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

/-- The voltage drop between i and j for the Green matrix H and the
unit demand that injects current at i and extracts it at j. -/
def drop (H : Mat) (i j : V) : ℝ := H i i + H j j - H i j - H j i

noncomputable def weightedResistance (w : Mat) (W : ℝ) (i j : V) : ℝ :=
  drop (grounded w W)⁻¹ i j

private theorem trace_lap (d H : Mat) (hs : ∀ i j, d i j = d j i) :
    2*(weightedLap d*H).trace = ∑ i, ∑ j, d i j * drop H i j := by
  have swap (f : V → V → ℝ) :
      (∑ i, ∑ j, d i j*f j i) = ∑ i, ∑ j, d i j*f i j := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hs j i]
  have base : (weightedLap d*H).trace =
      (∑ i, ∑ j, d i j * H i i) - ∑ i, ∑ j, d i j * H j i := by
    rw [weightedLap, sub_mul, trace_sub]
    congr 1
    · unfold trace
      apply sum_congr rfl
      intro i _
      simp [diagonal_mul, Finset.sum_mul]
  have sdiag := swap (fun i _ => H i i)
  have soff := swap H
  rw [base]
  simp only [drop, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sdiag, soff]
  ring

private theorem frobenius (d : Mat) (hs : ∀ i j, d i j = d j i) (hz : ∀ i, d i i = 0) :
    (∑ i, ∑ j, (d i j)^2) ≤ (weightedLap d*weightedLap d).trace := by
  unfold Matrix.trace
  apply sum_le_sum
  intro i _
  change _ ≤ ∑ j, weightedLap d i j * weightedLap d j i
  apply sum_le_sum
  intro j _
  by_cases e : i=j
  · subst j
    simpa only [hz, zero_pow (by decide : 2 ≠ 0)] using
      (mul_self_nonneg (weightedLap d i i))
  · simp [weightedLap, e, Ne.symm e, ← hs i j, sq]

/-- Exact identifiability for arbitrary finite conductance levels separated by Δ.
Pairs outside the measurement set have the same known weight in both graphs. -/
theorem noisy_identifiability (u v : Mat) (W Δ η : ℝ) (U : V → V → Prop) (y : V → V → ℝ)
    (hu : ∀ i j, u i j = u j i) (hv : ∀ i j, v i j = v j i)
    (zu : ∀ i, u i i = 0) (zv : ∀ i, v i i = 0)
    (un : ∀ i j, 0 ≤ u i j) (vn : ∀ i j, 0 ≤ v i j)
    (ub : ∀ i j, u i j ≤ W) (vb : ∀ i j, v i j ≤ W)
    (cu : (supportGraph u hu).Connected) (cv : (supportGraph v hv).Connected)
    (hW : 0 < W) (gap : ∀ i j, u i j ≠ v i j → Δ ≤ |u i j - v i j|)
    (known : ∀ i j, ¬U i j → u i j = v i j)
    (yu : ∀ i j, U i j → |weightedResistance u W i j - y i j| ≤ η)
    (yv : ∀ i j, U i j → |weightedResistance v W i j - y i j| ≤ η)
    (hη : η < Δ/((Fintype.card V:ℝ)*W)^2) : u = v := by
  classical
  have : Nonempty V := cu.nonempty
  let m := (Fintype.card V:ℝ)*W
  have hm : 0 < m := mul_pos (by exact_mod_cast Fintype.card_pos) hW
  let d := u-v
  have ds (i j : V) : d i j = d j i := by dsimp [d]; rw [hu i j,hv i j]
  have dz (i : V) : d i i = 0 := by simp [d,zu,zv]
  let A := grounded u W
  let C := grounded v W
  have bd : A-C = weightedLap d := grounded_sub _ _ _
  have inv := inverse_trace_bound A C (grounded_pos _ hu un cu hW) (grounded_pos _ hv vn cv hW)
    hm (grounded_le _ hu ub) (grounded_le _ hv vb)
  rw [bd] at inv
  have core := (mul_le_mul_of_nonneg_left (frobenius d ds dz) (sq_nonneg m⁻¹)).trans inv
  have bound (i j : V) :
      d i j * drop (C⁻¹-A⁻¹) i j ≤ (2*η)*|d i j| := by
    by_cases eq : u i j = v i j
    · simp [d,eq]
    have unknown : U i j := by by_contra no; exact eq (known i j no)
    have yd := yu i j unknown
    have yc := yv i j unknown
    have hh : drop (C⁻¹-A⁻¹) i j = weightedResistance v W i j - weightedResistance u W i j := by
      simp only [drop, weightedResistance, C, A, Matrix.sub_apply]; ring
    rw [hh, mul_comm (2*η)]
    apply (le_abs_self _).trans
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hh := abs_sub_le (weightedResistance v W i j) (y i j) (weightedResistance u W i j)
    rw [abs_sub_comm (y i j)] at hh
    linarith
  have total := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun j _ => bound i j))
  rw [← trace_lap d _ ds] at total
  simp only [← Finset.mul_sum] at total
  have gapSum : Δ*(∑ i, ∑ j, |d i j|) ≤ ∑ i, ∑ j, (d i j)^2 := by
    simp only [Finset.mul_sum]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    by_cases eq : u i j = v i j
    · simp [d,eq]
    · have hg : Δ ≤ |d i j| := gap i j eq
      simpa only [← sq, sq_abs] using (mul_le_mul_of_nonneg_right hg (abs_nonneg (d i j)))
  by_contra neq
  have pos : 0 < ∑ i, ∑ j, |d i j| := by
    by_contra! no
    have nn (i : V) := sum_nonneg (s := univ) fun j _ => abs_nonneg (d i j)
    have z := le_antisymm no (sum_nonneg fun i _ => nn i)
    apply neq
    ext i j
    have row := (sum_eq_zero_iff_of_nonneg fun k _ => nn k).mp z i (mem_univ _)
    have val := (sum_eq_zero_iff_of_nonneg fun k _ => abs_nonneg (d i k)).mp row j (mem_univ _)
    exact sub_eq_zero.mp (abs_eq_zero.mp val)
  have hη' : η < m⁻¹^2*Δ := by simpa only [div_eq_inv_mul, inv_pow] using hη
  have strict := mul_lt_mul_of_pos_right hη' pos
  have lower := mul_le_mul_of_nonneg_left gapSum (sq_nonneg m⁻¹)
  linarith only [strict, total, core, lower]

end ResistanceRecovery

end

section

open Finset Matrix
namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Mat" => Matrix V V ℝ

/-- The source injects one unit of current and the sink extracts one. -/
noncomputable def demand (i j : V) : V → ℝ := Pi.single i 1 - Pi.single j 1

private theorem lap_const (w : Mat) (t : ℝ) : weightedLap w *ᵥ (fun _ => t) = 0 := by
  ext i
  rw [weightedLap, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
  simp [mulVec, dotProduct, ← sum_mul]

private theorem ground_apply (w : Mat) (W : ℝ) (x : V → ℝ) (i : V) :
    (grounded w W *ᵥ x) i = (weightedLap w *ᵥ x) i + W*(∑ j, x j) := by
  rw [grounded, add_mulVec, Pi.add_apply]
  simp [mulVec, dotProduct, Finset.mul_sum]

private theorem sum_lap (w : Mat) (h : ∀ i j, w i j = w j i) (x : V → ℝ) :
    ∑ i, (weightedLap w *ᵥ x) i = 0 := by
  rw [weightedLap, sub_mulVec]
  simp only [Pi.sub_apply, sum_sub_distrib, mulVec_diagonal]
  apply sub_eq_zero.mpr
  simp only [mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [h j i]

private theorem total_demand (i j : V) : ∑ k, demand i j k = 0 := by
  classical
  simp [demand, Finset.sum_sub_distrib, Pi.single_apply]

private theorem drop_apply (B : Mat) (i j : V) :
    drop B i j = (B *ᵥ demand i j) i - (B *ᵥ demand i j) j := by
  rw [demand, mulVec_sub, mulVec_single_one, mulVec_single_one]
  simp only [drop, Pi.sub_apply, col_apply]
  ring

/-- Every finite connected nonnegatively weighted graph admits a solution to
Kirchhoff's equations for one source and one sink. -/
theorem weighted_kirchhoff (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j)
    (conn : (supportGraph w h).Connected) {W : ℝ} (hw : 0 < W) (i j : V) :
    weightedLap w *ᵥ ((grounded w W)⁻¹ *ᵥ demand i j) = demand i j := by
  let A := grounded w W
  let x := A⁻¹ *ᵥ demand i j
  have pos := grounded_pos w h hn conn hw
  have hu : IsUnit A.det := A.isUnit_iff_isUnit_det.mp pos.isUnit
  have sol : A *ᵥ x = demand i j := by rw [show x = _ from rfl, mulVec_mulVec, A.mul_nonsing_inv hu, one_mulVec]
  have whole : ∑ k, (A *ᵥ x) k = 0 := sol ▸ total_demand i j
  change ∑ k, (grounded w W *ᵥ x) k = 0 at whole
  simp_rw [ground_apply] at whole
  rw [sum_add_distrib, sum_lap w h x, zero_add, sum_const, card_univ, nsmul_eq_mul] at whole
  have : Nonempty V := conn.nonempty
  have nz : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have z := (mul_eq_zero.mp ((mul_eq_zero.mp whole).resolve_left nz)).resolve_left hw.ne'
  ext k
  have s := congrFun sol k
  change (grounded w W *ᵥ x) k = _ at s
  rw [ground_apply,z,mul_zero,add_zero] at s
  exact s

/-- The inverse-matrix reading in the recovery theorem is the voltage drop
for every solution of the unit-current equations, for every positive grounding. -/
theorem weighted_voltage (w : Mat) (h : ∀ i j, w i j = w j i) (hn : ∀ i j, 0 ≤ w i j)
    (conn : (supportGraph w h).Connected) {W : ℝ} (hw : 0 < W) (i j : V) (p : V → ℝ)
    (sol : weightedLap w *ᵥ p = demand i j) : weightedResistance w W i j = p i - p j := by
  let A := grounded w W
  have hu : IsUnit A.det := A.isUnit_iff_isUnit_det.mp (grounded_pos w h hn conn hw).isUnit
  have : Nonempty V := conn.nonempty
  have cn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let t := (∑ k, p k)/(Fintype.card V:ℝ)
  let q : V → ℝ := p - fun _ => t
  have z : ∑ k, q k = 0 := by
    simp [q,t,Finset.sum_sub_distrib, mul_div_cancel₀,cn]
  have eq : A *ᵥ q = demand i j := by
    ext k
    rw [show A = grounded w W from rfl, ground_apply,z,mul_zero,add_zero,show q = _ from rfl,
      mulVec_sub, sol, lap_const, sub_zero]
  have qi : A⁻¹ *ᵥ demand i j = q := by rw [← eq, mulVec_mulVec, A.nonsing_inv_mul hu, one_mulVec]
  change drop A⁻¹ i j = _
  rw [drop_apply,qi]
  simp only [q, Pi.sub_apply]; ring

end ResistanceRecovery

end

section

open Matrix Finset
namespace ResistanceRecovery

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def binaryWeights (G : SimpleGraph V) : Matrix V V ℝ := by
  classical
  exact G.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
private theorem weights_apply (G : SimpleGraph V) (i j : V) [Decidable (G.Adj i j)] :
    binaryWeights G i j = if G.Adj i j then 1 else 0 := by classical simp [binaryWeights,SimpleGraph.adjMatrix_apply]

omit [Fintype V] [DecidableEq V] in
private theorem weights_symm (G : SimpleGraph V) (i j : V) : binaryWeights G i j = binaryWeights G j i := by
  classical
  simp [weights_apply,G.adj_comm]

private theorem weights_support (G : SimpleGraph V) : supportGraph (binaryWeights G) (weights_symm G) = G := by
  classical
  ext i j
  change (i ≠ j ∧ 0 < binaryWeights G i j) ↔ G.Adj i j
  by_cases a : G.Adj i j
  · simp [weights_apply, a, a.ne]
  · simp [weights_apply, a]

private theorem weights_lap (G : SimpleGraph V) [DecidableRel G.Adj] :
    weightedLap (binaryWeights G) = G.lapMatrix ℝ := by
  classical
  unfold weightedLap SimpleGraph.lapMatrix SimpleGraph.degMatrix
  congr 1
  · congr 1
    funext i
    simp_rw [weights_apply, G.degree_eq_sum_if_adj]
  · ext i j
    simp [weights_apply, SimpleGraph.adjMatrix_apply]

theorem unweighted_voltage (G : SimpleGraph V) (c : G.Connected) (i j : V) :
    weightedResistance (binaryWeights G) 1 i j = ResistanceLifts.resistance G i j := by
  classical
  let w := binaryWeights G
  have h := weights_symm G
  have hn (i j : V) : 0 ≤ w i j := by simp [w,weights_apply]; split <;> norm_num
  have hc : (supportGraph w h).Connected := weights_support G ▸ c
  let p := (grounded w 1)⁻¹ *ᵥ demand i j
  have eq : weightedLap w *ᵥ p = demand i j := weighted_kirchhoff w h hn hc one_pos i j
  rw [weighted_voltage w h hn hc one_pos i j p eq]
  apply Eq.symm
  apply ResistanceLifts.resistance_of_potential (c i j)
  change G.lapMatrix ℝ *ᵥ p = _
  rw [← weights_lap, eq]
  ext k
  simp [demand,Pi.single_apply,eq_comm]

private theorem symmetry (G : SimpleGraph V) (c : G.Connected) (i j : V) :
    ResistanceLifts.resistance G i j = ResistanceLifts.resistance G j i := by
  rw [← unweighted_voltage G c, ← unweighted_voltage G c]
  unfold weightedResistance drop
  ring

/-- All known adjacencies and the listed voltage measurements identify at most
one connected, labeled simple graph of the specified order. Pairs in the list
are unordered, and duplicate measurements are permitted. -/
def Identifiable (n : ℕ) (η : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) [Fintype I] (E : I → V × V)
    (y : I → ℝ) (G H : SimpleGraph V), Fintype.card V = n → G.Connected → H.Connected →
    (∀ i j, (∀ q, E q ≠ (i,j) ∧ E q ≠ (j,i)) → (G.Adj i j ↔ H.Adj i j)) →
    (∀ q, |y q - ResistanceLifts.resistance G (E q).1 (E q).2| ≤ η) →
    (∀ q, |y q - ResistanceLifts.resistance H (E q).1 (E q).2| ≤ η) → G = H

/-- Below 1/n² the missing-pair readings determine every missing adjacency. -/
theorem binary_identifiability (n : ℕ) (η : ℝ) (hη : η < 1/(n:ℝ)^2) : Identifiable n η := by
  classical
  intro V _ _ I _ E y G H card g h known gy hy
  let U (i j : V) := ∃ q, E q = (i,j) ∨ E q = (j,i)
  let a (i j : V) := if q : U i j then y q.choose else 0
  have noise (F : SimpleGraph V) (fc : F.Connected) (fy : ∀ q, |y q-ResistanceLifts.resistance F (E q).1 (E q).2| ≤ η)
      (i j : V) (u : U i j) : |weightedResistance (binaryWeights F) 1 i j - a i j| ≤ η := by
    rw [unweighted_voltage F fc, abs_sub_comm]
    change |(if q : U i j then y q.choose else 0) - _| ≤ _
    rw [dite_eq_left u]
    have good := fy u.choose
    rcases u.choose_spec with s|s <;> rw [s] at good
    · exact good
    · simpa only [symmetry F fc j i] using good
  have same := noisy_identifiability (binaryWeights G) (binaryWeights H) 1 1 η U a
    (weights_symm G) (weights_symm H) (by simp [weights_apply]) (by simp [weights_apply])
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by intro i j; rw [weights_apply]; split <;> norm_num)
    (by rwa [weights_support]) (by rwa [weights_support]) one_pos
    (by intro i j; rw [weights_apply,weights_apply]; split <;> split <;> norm_num)
    (by intro i j no; have e := known i j (fun q => ⟨fun eq => no ⟨q,Or.inl eq⟩,fun eq => no ⟨q,Or.inr eq⟩⟩)
        simp [weights_apply,e])
    (noise G g gy) (noise H h hy) (by simpa only [card,mul_one] using hη)
  ext i j
  have e := congrFun (congrFun same i) j
  simp only [weights_apply] at e
  by_cases a : G.Adj i j <;> by_cases b : H.Adj i j <;> simp_all

/-- Four ambiguous unknown pairs give the upper bound for every n=k+4. -/
theorem binary_obstruction (k : ℕ) (η : ℝ) (hη : radius k ≤ η) : ¬Identifiable (k+4) η := by
  intro id
  obtain ⟨G,H,g,h,diff,known,y,err⟩ := four_unknown_pairs k
  apply diff
  apply id (Vertex k) Query endpoints (fun q => (y q : ℝ)) G H (by simp [Vertex]; omega) g h known
  · intro q
    exact (err q).1.le.trans hη
  · intro q
    exact (err q).2.le.trans hη

end ResistanceRecovery

end

section

open Filter Set
open scoped Topology

namespace ResistanceRecovery

/-- The supremum of the adversarial error levels at which all compatible
connected graphs are uniquely identified by the specified measurements. -/
noncomputable def recoveryRadius (n : ℕ) : ℝ := sSup {η : ℝ | Identifiable n η}

theorem sharp_bounds (k : ℕ) :
    1/((k:ℝ)+4)^2 ≤ recoveryRadius (k+4) ∧ recoveryRadius (k+4) ≤ radius k := by
  let S := {η : ℝ | Identifiable (k+4) η}
  let a : ℝ := 1/((k:ℝ)+4)^2
  have small : Set.Iio a ⊆ S := by
    intro η h
    exact binary_identifiability _ _ (by simpa [a] using h)
  have cap : ∀ η ∈ S, η ≤ radius k := by
    intro η h
    by_contra! large
    exact binary_obstruction k η large.le h
  have finite : BddAbove S := ⟨_,cap⟩
  have nonempty : S.Nonempty := Set.nonempty_Iio.mono small
  change a ≤ sSup S ∧ sSup S ≤ radius k
  exact ⟨by simpa only [csSup_Iio] using csSup_le_csSup finite Set.nonempty_Iio small, csSup_le nonempty cap⟩

/-- The leading constant of the worst-case unweighted error threshold for
missing-pair measurements is exactly one. -/
theorem sharp_limit : Tendsto (fun k : ℕ => ((k:ℝ)+4)^2 * recoveryRadius (k+4)) atTop (𝓝 1) := by
  have hlow (k : ℕ) : 1 ≤ ((k:ℝ)+4)^2*recoveryRadius (k+4) := by
    have h := mul_le_mul_of_nonneg_left (sharp_bounds k).1 (sq_nonneg ((k:ℝ)+4))
    have denom : ((k:ℝ)+4)^2 ≠ 0 := by positivity
    simpa only [one_div, mul_inv_cancel₀ denom] using h
  have high (k : ℕ) : ((k:ℝ)+4)^2*recoveryRadius (k+4) ≤ 1+2/((k:ℝ)+2) := by
    apply (mul_le_mul_of_nonneg_left (sharp_bounds k).2 (sq_nonneg ((k:ℝ)+4))).trans_eq
    unfold radius
    have h₁ : (k:ℝ)+4 ≠ 0 := by positivity
    have h₂ : (k:ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring
  have den : Tendsto (fun k : ℕ => (k:ℝ)+2) atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have limit : Tendsto (fun k : ℕ => 1+2/((k:ℝ)+2)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_const_nhds.div_atTop den (a := (2:ℝ)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds limit hlow high

end ResistanceRecovery

end
