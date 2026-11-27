module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

open scoped Matrix

namespace ResistanceLifts

/-! A standalone, kernel-checked reference for the two questions in Section 6 of
Zhang, Luo, Wang and He. The statement `separation` is at the end. -/

/-- The two sheets over each vertex of the 39-vertex base graph. -/
abbrev Vertex := Fin 39 × Bool

/-- Literal signatures keep the old color and the multiset of labeled neighbors' colors.
Every vertex occurs in the multiset, including the vertex at distance zero. -/
def Color (D A : Type u) : ℕ → Type u
  | 0 => A
  | n + 1 => Color D A n × Multiset (D × Color D A n)

/-- The histogram of a vertex labeling, with one occurrence per vertex. -/
def histogram {V A : Type*} [Fintype V] (f : V → A) : Multiset A :=
  (Finset.univ : Finset V).val.map f

def refine {V : Type*} {D A : Type u} [Fintype V] (dist : V → V → D) (initial : V → A) :
    (n : ℕ) → V → Color D A n
  | 0, v => initial v
  | n + 1, v => (refine dist initial n v, histogram fun w => (dist v w, refine dist initial n w))

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

/-- The characteristic polynomial records the full ordinary Laplacian spectrum
with multiplicities. -/
noncomputable def laplacianPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial ℝ := by
  classical
  exact (G.lapMatrix ℝ).charpoly

/-- Number the three terminals first. Each side then contains four length-four
paths, with three fresh interior vertices on each path. -/
def base (n : ℕ) : Fin 39 := ⟨n % 39, Nat.mod_lt _ (by decide)⟩

def interior (s path pos : ℕ) : Fin 39 := base (3 + s * 12 + path * 3 + pos)

/-- The direct edge changes sheet on side zero exactly in the twisted graph. -/
def direct (twist : Bool) (s : ℕ) : Bool := twist && (s == 0)

/-- An explicit neighborhood list for the unweighted two-sheet lift. All sheet
changes on a long path are concentrated at its final edge. -/
def neighbors (t : Bool) (x : Vertex) : List Vertex :=
  let b := x.1.val
  let e := x.2
  if b < 3 then
    let prev := (b + 2) % 3
    [(base ((b+1)%3), xor e (direct t b)), (base prev, xor e (direct t prev))] ++
      (List.range 4).map (fun p => (interior b p 0, e)) ++
      (List.range 4).map (fun p => (interior prev p 2, xor e (!(direct t prev))))
  else
    let s := (b - 3) / 12
    let p := ((b - 3) / 3) % 4
    let k := (b - 3) % 3
    [(if k = 0 then base s else interior s p (k-1), e),
      if k = 2 then (base ((s+1)%3), xor e (!(direct t s))) else (interior s p (k+1), e)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem neighbors_valid : ∀ t : Bool, ∀ x : Vertex,
    (neighbors t x).Nodup ∧ x ∉ neighbors t x ∧
    ∀ y ∈ neighbors t x, x ∈ neighbors t y := by decide +kernel

def graph (t : Bool) : SimpleGraph Vertex where
  Adj x y := y ∈ neighbors t x
  symm := ⟨fun x y h => (neighbors_valid t x).2.2 y h⟩
  loopless := ⟨fun x => (neighbors_valid t x).2.1⟩

instance (t : Bool) : DecidableRel (graph t).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem neighborFinset_eq (t : Bool) (v : Vertex) :
    (graph t).neighborFinset v = (neighbors t v).toFinset := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, List.mem_toFinset]
  rfl

/-- The terminals met at either end of the long path containing `x`, and the
distance from its left end. A terminal has zero distance and both ends equal. -/
structure Ends where
  left : Vertex
  right : Vertex
  pos : ℕ

def ends (t : Bool) (x : Vertex) : Ends :=
  let b := x.1.val
  if b < 3 then ⟨x, x, 0⟩ else
    let s := (b-3)/12
    ⟨(base s, x.2), (base ((s+1)%3), xor x.2 (!(direct t s))), (b-3)%3 + 1⟩

def commonPath (x y : Vertex) : Bool :=
  3 ≤ x.1.val && 3 ≤ y.1.val && (x.1.val-3)/3 == (y.1.val-3)/3 && x.2 == y.2

/-- The terminal Schur complement is the Laplacian of the complete tripartite
K₂,₂,₂. Its inverse on zero-mean terminal loads, multiplied by 72. -/
def terminalGreen (x y : Vertex) : ℤ :=
  if x.1 != y.1 then -2 else if x.2 == y.2 then 13 else -5

/-- Green kernel multiplied by 1152. Linearly interpolate from each pair of
endpoints, then add the length-four Dirichlet kernel for a common path interior. -/
def green (t : Bool) (x y : Vertex) : ℤ :=
  let a := ends t x
  let b := ends t y
  let p : ℤ := a.pos
  let q : ℤ := b.pos
  (4-p)*((4-q)*terminalGreen a.left b.left + q*terminalGreen a.left b.right) +
    p*((4-q)*terminalGreen a.right b.left + q*terminalGreen a.right b.right) +
    (if commonPath x y then 288 * min p q * (4-max p q) else 0)

/-- Kirchhoff's equation with a source at `z` and one sixth of the return current
at each terminal, in the same integer scaling as `green`. -/
def columnHolds (t : Bool) (z x : Vertex) : Prop :=
  (neighbors t x).length * green t x z - ((neighbors t x).map fun y => green t y z).sum =
    (if x = z then 1152 else 0) - (if x.1.val < 3 then 192 else 0)

instance (t : Bool) (z x : Vertex) : Decidable (columnHolds t z x) :=
  inferInstanceAs (Decidable ((_ : ℤ) = _))

/-- Raw resistance numerator as the voltage drop of the difference of columns. -/
def numerator (t : Bool) (x y : Vertex) : ℤ :=
  (green t x x - green t x y) - (green t y x - green t y y)

section

set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Direct integer verification of all columns of the analytic Green kernel. -/
theorem green_columns : ∀ t z x, columnHolds t z x := by decide +kernel

/-- Kept as an integer comparison so that every pair of resistances is checked
exactly, without numerical linear algebra or floating point. -/
def samePair (t : Bool) (a b : Fin 39) (e : Bool) : Prop :=
  ∃ flip : Bool, ∀ sheet : Bool,
    numerator t (a,e) (b,sheet) = numerator false (a,false) (b,xor sheet flip)

instance (t : Bool) (a b : Fin 39) (e : Bool) : Decidable (samePair t a b e) :=
  inferInstanceAs (Decidable (∃ _ : Bool, ∀ _ : Bool, (_ : ℤ) = _))

theorem green_pairs : ∀ t a b e, samePair t a b e := by decide +kernel

end

/-- Relabeling a finite vertex set leaves its color histogram unchanged. -/
theorem histogram_perm {V A : Type*} [Fintype V] (e : V ≃ V) (f : V → A) :
    histogram (fun w => f (e w)) = histogram f := by
  change Finset.univ.val.map (f ∘ e) = _
  rw [← Multiset.map_map]
  change (Finset.univ.map e.toEmbedding).val.map f = _
  rw [Finset.map_univ_equiv]
  rfl

/-- Independently exchange the two sheets over any chosen set of base vertices. -/
def sheetPermutation (swap : Fin 39 → Bool) : Vertex ≃ Vertex where
  toFun x := (x.1, xor x.2 (swap x.1))
  invFun x := (x.1, xor x.2 (swap x.1))
  left_inv x := by rcases x with ⟨a,e⟩; cases e <;> cases h : swap a <;> simp [h]
  right_inv x := by rcases x with ⟨a,e⟩; cases e <;> cases h : swap a <;> simp [h]

/-- Paired distances suffice for every refinement depth, even starting with
arbitrary (and possibly all distinct) base-fiber colors. -/
theorem refine_of_fiber_pairs {D A : Type} (d : Bool → Vertex → Vertex → D)
    (pairs : ∀ t a b e, ∃ flip : Bool, ∀ s : Bool,
      d t (a,e) (b,s) = d false (a,false) (b,xor s flip))
    (f : Fin 39 → A) (n : ℕ) (t : Bool) (a : Fin 39) (e : Bool) :
    refine (d t) (fun x => f x.1) n (a,e) = refine (d false) (fun x => f x.1) n (a,false) := by
  classical
  induction n generalizing t a e with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext (ih _ _ _)
    let swap (b : Fin 39) := (pairs t a b e).choose
    let perm := sheetPermutation swap
    let label (w : Vertex) := (d false (a,false) w, refine (d false) (fun x => f x.1) n w)
    change histogram (fun w : Vertex => (d t (a,e) w, refine (d t) (fun x => f x.1) n w)) = histogram label
    rw [← histogram_perm perm label]
    apply congrArg histogram
    funext ⟨b,s⟩
    change (_, _) = (d false (a,false) (b,xor s (swap b)), refine _ _ n (b,xor s (swap b)))
    exact Prod.ext ((pairs t a b e).choose_spec s) ((ih t b s).trans (ih false b _).symm)

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

theorem degree_eq_length (t : Bool) (v : Vertex) :
    (graph t).degree v = (neighbors t v).length := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq,
    List.toFinset_card_of_nodup (neighbors_valid t v).1]

theorem column_real {t : Bool} {z : Vertex} (h : ∀ x, columnHolds t z x) (x : Vertex) :
    ((graph t).lapMatrix ℝ *ᵥ (fun v => (green t v z : ℝ))) x =
    (if x = z then (1152 : ℝ) else 0) - (if x.1.val < 3 then 192 else 0) := by
  have hz := h x
  unfold columnHolds at hz
  rw [← degree_eq_length, ← List.sum_toFinset _ (neighbors_valid t x).1, ← neighborFinset_eq] at hz
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  split_ifs at hz ⊢ <;> exact_mod_cast hz

/-- The explicit scaled integer kernel certifies the true real effective resistance. -/
theorem resistance_from_columns {t : Bool} (cols : ∀ z x, columnHolds t z x)
    (hc : (graph t).Connected) (a b : Vertex) :
    resistance (graph t) a b = (numerator t a b : ℝ) / 1152 := by
  let col (z : Vertex) := fun x => (green t x z : ℝ)
  let u : Vertex → ℝ := (1152 : ℝ)⁻¹ • (col a - col b)
  have hu : UnitPotential (graph t) a b u := by
    unfold UnitPotential
    rw [show (fun i j => Classical.propDecidable ((graph t).Adj i j)) =
      (inferInstance : DecidableRel (graph t).Adj) from Subsingleton.elim _ _]
    rw [show u = (1152 : ℝ)⁻¹ • (col a - col b) from rfl, Matrix.mulVec_smul, Matrix.mulVec_sub]
    ext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, col]
    rw [column_real (cols a), column_real (cols b)]
    split_ifs <;> norm_num
  rw [resistance_of_potential (hc a b) hu]
  simp only [u, col, numerator, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Int.cast_sub]
  ring

abbrev Terminal := Fin 3 × Bool

def terminal (z : Terminal) : Vertex := (base z.1.val, z.2)

/-- Direct terminals form two triangles or one hexagon. A long path between
opposite direct sheets has length four. -/
def terminalDistance (t : Bool) (x z : Vertex) : ℕ :=
  if x = z then 0 else if t then
    if x.1 = z.1 then 3 else
      let twist := (x.1.val == 0 && z.1.val == 1) || (x.1.val == 1 && z.1.val == 0)
      if xor x.2 z.2 == twist then 1 else 2
  else if x.2 == z.2 then 1 else if x.1 == z.1 then 5 else 4

/-- The two routes from an interior vertex to a specified terminal. -/
def distanceTo (t : Bool) (x : Vertex) (z : Terminal) : ℕ :=
  let a := ends t x
  if x.1.val < 3 then terminalDistance t x (terminal z) else
    min (a.pos + terminalDistance t a.left (terminal z))
      (4-a.pos + terminalDistance t a.right (terminal z))

/-- A shortest path potential has a unit descent step away from its zero and
changes by at most one across every edge. -/
def distanceCheck (t : Bool) (z : Terminal) (x : Vertex) : Prop :=
  let d := fun v => distanceTo t v z
  (d x = 0 ↔ x = terminal z) ∧
    (∀ y ∈ neighbors t x, d x ≤ d y + 1) ∧
    (x ≠ terminal z → ∃ y ∈ neighbors t x, d y + 1 = d x)

instance (t : Bool) (z : Terminal) (x : Vertex) : Decidable (distanceCheck t z x) := by
  unfold distanceCheck
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem distance_valid : ∀ t z x, distanceCheck t z x := by decide +kernel

theorem route (t : Bool) (z : Terminal) (x : Vertex) :
    ∃ p : (graph t).Walk x (terminal z), p.length = distanceTo t x z := by
  by_cases h : x = terminal z
  · subst x
    exact ⟨.nil, ((distance_valid t z _).1.mpr rfl).symm⟩
  · obtain ⟨y, hy, hd⟩ := (distance_valid t z x).2.2 h
    change distanceTo t y z + 1 = distanceTo t x z at hd
    have ha : (graph t).Adj x y := hy
    obtain ⟨p, hp⟩ := route t z y
    exact ⟨.cons ha p, by simpa only [SimpleGraph.Walk.length_cons, hp] using hd⟩
termination_by distanceTo t x z
decreasing_by omega

theorem connected (t : Bool) : (graph t).Connected := by
  apply ((graph t).connected_iff_exists_forall_reachable).mpr
  refine ⟨terminal (0,false), fun w => ?_⟩
  obtain ⟨p, _⟩ := route t (0,false) w
  exact p.reachable.symm

theorem distance_to_terminal (t : Bool) (x : Vertex) (z : Terminal) :
    (graph t).dist x (terminal z) = distanceTo t x z := by
  obtain ⟨p,hp⟩ := route t z x
  apply le_antisymm (hp ▸ SimpleGraph.dist_le p)
  obtain ⟨w,hw⟩ := (connected t).exists_walk_length_eq_dist x (terminal z)
  rw [← hw]
  have bound {a b : Vertex} (q : (graph t).Walk a b) :
      distanceTo t a z ≤ q.length + distanceTo t b z := by
    induction q with
    | nil => simp
    | cons h _ ih =>
      have hs := (distance_valid t z _).2.1 _ h
      dsimp only at hs
      simp only [SimpleGraph.Walk.length_cons]
      omega
  simpa only [(distance_valid t z _).1.mpr rfl, Nat.add_zero] using bound w

/-- With the twisted direct side, the terminal offsets 0,0,1 extend by alternating
parity along each of the even-length paths. -/
def bipartition (x : Vertex) : Fin 2 :=
  let a := ends true x
  if xor x.2 (xor (a.left.1.val == 2) (a.pos % 2 == 1)) then 1 else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem bipartition_valid : ∀ x : Vertex, ∀ y ∈ neighbors true x,
    bipartition x ≠ bipartition y := by decide +kernel

theorem twisted_bipartite : (graph true).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk bipartition fun h => bipartition_valid _ _ h⟩

theorem untwisted_triangle : ∃ a b c, (graph false).Adj a b ∧ (graph false).Adj b c ∧
    (graph false).Adj c a := by
  refine ⟨(base 0,false),(base 1,false),(base 2,false),?_⟩
  decide

/-- The first signature determines the degree by counting the distance-one entries. -/
def seenDegree (c : Color ℕ Unit 1) : ℕ := c.2.countP (fun k => k.1 = 1)

/-- The second signature counts nearby vertices that had terminal degree at round one. -/
def seenTerminals (c : Color ℕ Unit 2) : ℕ :=
  c.2.countP (fun k => k.1 ≤ 3 ∧ seenDegree k.2 = 10)

theorem count_histogram {V A : Type*} [Fintype V] (f : V → A) (p : A → Prop)
    [DecidablePred p] : (histogram f).countP p = (Finset.univ.filter (fun v => p (f v))).card := by
  rw [histogram, Multiset.countP_map]
  rfl

theorem seen_degree (G : SimpleGraph Vertex) [DecidableRel G.Adj] (x : Vertex) :
    seenDegree (refine G.dist (fun _ => ()) 1 x) = G.degree x := by
  unfold seenDegree
  change (histogram (V := Vertex) _).countP _ = _
  rw [count_histogram, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply congrArg Finset.card
  ext v
  simp [SimpleGraph.dist_eq_one_iff_adj]

def terminalIndex (v : Vertex) : Terminal := (Fin.ofNat 3 v.1.val, v.2)

def nearCount (t : Bool) (x : Vertex) : ℕ :=
  (Finset.univ.filter (fun y : Vertex => distanceTo t x (terminalIndex y) ≤ 3 ∧ y.1.val < 3)).card

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem terminal_checks :
    (∀ y : Vertex, y.1.val < 3 → terminal (terminalIndex y) = y) ∧
    (∀ t y, (neighbors t y).length = 10 ↔ y.1.val < 3) ∧
    (∀ t x, x.1.val < 3 → nearCount t x = if t then 6 else 3) := by decide +kernel

theorem seen_terminals (t : Bool) (x : Vertex) :
    seenTerminals (refine (graph t).dist (fun _ => ()) 2 x) = nearCount t x := by
  unfold seenTerminals
  change (histogram (V := Vertex) _).countP _ = _
  rw [count_histogram]
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, seen_degree, degree_eq_length,
    terminal_checks.2.1]
  by_cases h : y.1.val < 3
  · have hd := distance_to_terminal t x (terminalIndex y)
    rw [terminal_checks.1 y h] at hd
    simp [hd, h]
  · simp [h]

theorem shortest_paths_differ :
    histogram (refine (graph false).dist (fun _ => ()) 2) ≠
      histogram (refine (graph true).dist (fun _ => ()) 2) := by
  let x : Vertex := (base 0,false)
  have hx : x.1.val < 3 := by decide
  intro h
  have hm : refine (graph false).dist (fun _ => ()) 2 x ∈
      histogram (refine (graph true).dist (fun _ => ()) 2) := by
    rw [← h]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val x)
  obtain ⟨y, _, heq⟩ := Multiset.mem_map.mp hm
  have hdegrees := congrArg (fun c : Color ℕ Unit 2 => seenDegree c.1) heq
  change seenDegree (refine (graph true).dist _ 1 y) = seenDegree (refine (graph false).dist _ 1 x) at hdegrees
  rw [seen_degree, seen_degree, degree_eq_length, degree_eq_length] at hdegrees
  have hy : y.1.val < 3 := (terminal_checks.2.1 true y).mp
    (hdegrees.trans ((terminal_checks.2.1 false x).mpr hx))
  have hc := congrArg seenTerminals heq
  rw [seen_terminals, seen_terminals, terminal_checks.2.2 true y hy, terminal_checks.2.2 false x hx] at hc
  contradiction

/-- Apply the ordinary Laplacian using the displayed neighbor lists. -/
def lapStep (t : Bool) (f : Vertex → ℤ) (x : Vertex) : ℤ :=
  (neighbors t x).length * f x - ((neighbors t x).map f).sum

def diagonalCube (t : Bool) (x : Vertex) : ℤ :=
  lapStep t (lapStep t (lapStep t (fun i => if i = x then 1 else 0))) x

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem integer_traces : (∑ x, diagonalCube false x) = 9228 ∧
    (∑ x, diagonalCube true x) = 9240 := by decide +kernel

theorem lap_step_real (t : Bool) (f : Vertex → ℤ) :
    (graph t).lapMatrix ℝ *ᵥ (fun v => (f v : ℝ)) = fun x => (lapStep t f x : ℝ) := by
  ext x
  rw [SimpleGraph.lapMatrix_mulVec_apply, lapStep, ← degree_eq_length,
    ← List.sum_toFinset _ (neighbors_valid t x).1, ← neighborFinset_eq]
  push_cast
  rfl

theorem trace_cube (t : Bool) : ((graph t).lapMatrix ℝ ^ 3).trace =
    ((∑ x, diagonalCube t x : ℤ) : ℝ) := by
  rw [Matrix.trace, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  let L := (graph t).lapMatrix ℝ
  change (L^3).col x x = _
  rw [← Matrix.mulVec_single_one]
  have hs : Pi.single x (1:ℝ) = (fun i => ((if i = x then 1 else 0 : ℤ) : ℝ)) := by
    ext i
    by_cases h : i = x <;> simp [h]
  rw [show L^3 = L * (L * L) by simp [pow_succ, Matrix.mul_assoc], ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hs, lap_step_real, lap_step_real, lap_step_real]
  rfl

/-- For symmetric real matrices the cube trace is fixed by the characteristic
polynomial, since it is the sum of the cubes of the eigenvalues with multiplicity. -/
theorem trace_cube_characteristic {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℝ} (ha : A.IsHermitian) (hb : B.IsHermitian)
    (hp : A.charpoly = B.charpoly) : (A ^ 3).trace = (B ^ 3).trace := by
  have trace_diag {M : Matrix V V ℝ} (h : M.IsHermitian) :
      (M^3).trace = ((Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) : Matrix V V ℝ)^3).trace := by
    conv_lhs => rw [h.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  rw [trace_diag ha, trace_diag hb, (ha.eigenvalues_eq_eigenvalues_iff hb).mpr hp]

theorem spectra_differ : laplacianPolynomial (graph false) ≠ laplacianPolynomial (graph true) := by
  intro h
  unfold laplacianPolynomial at h
  rw [show (fun i j => Classical.propDecidable ((graph false).Adj i j)) =
    (inferInstance : DecidableRel (graph false).Adj) from Subsingleton.elim _ _,
    show (fun i j => Classical.propDecidable ((graph true).Adj i j)) =
    (inferInstance : DecidableRel (graph true).Adj) from Subsingleton.elim _ _] at h
  have ht := trace_cube_characteristic ((graph false).isHermitian_lapMatrix ℝ)
    ((graph true).isHermitian_lapMatrix ℝ) h
  rw [trace_cube, trace_cube, integer_traces.1, integer_traces.2] at ht
  norm_num at ht

/-- A counterexample to both implications in Zhang, Luo, Wang and He, Section 6.
The 78-vertex graphs are connected and simple. Starting with any fiber labeling,
all resistance-refinement colors agree, even between opposite sheets. With
constant starting features, round two of shortest-path refinement distinguishes
the graphs. Their ordinary Laplacian characteristic polynomials differ as well. -/
theorem separation : ∃ G H : SimpleGraph Vertex,
    G.Connected ∧ H.Connected ∧ H.IsBipartite ∧
    (∃ x y z, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x) ∧
    (∀ (A : Type) (features : Fin 39 → A) (depth : ℕ) (v : Fin 39) (e s : Bool),
      refine (resistance G) (fun x => features x.1) depth (v,e) =
      refine (resistance H) (fun x => features x.1) depth (v,s)) ∧
    histogram (refine G.dist (fun _ => ()) 2) ≠ histogram (refine H.dist (fun _ => ()) 2) ∧
    laplacianPolynomial G ≠ laplacianPolynomial H := by
  refine ⟨graph false, graph true, connected false, connected true, twisted_bipartite,
    untwisted_triangle, ?_, shortest_paths_differ, spectra_differ⟩
  intro A features depth v e s
  have pairs : ∀ t a b e, ∃ f : Bool, ∀ u : Bool,
      resistance (graph t) (a,e) (b,u) = resistance (graph false) (a,false) (b,xor u f) := by
    intro t a b e
    obtain ⟨f, hf⟩ := green_pairs t a b e
    refine ⟨f, fun u => ?_⟩
    rw [resistance_from_columns (green_columns t) (connected t),
      resistance_from_columns (green_columns false) (connected false), hf u]
  exact (refine_of_fiber_pairs _ pairs features depth false v e).trans
    (refine_of_fiber_pairs _ pairs features depth true v s).symm

end ResistanceLifts
