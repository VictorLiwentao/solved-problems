module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

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
