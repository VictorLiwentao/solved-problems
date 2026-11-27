module

public import SolvedProblems.JointForestSheets

@[expose] public section

namespace JointForest

open SimpleGraph

/-- Orient every side of the complete template using an external vertex order. -/
abbrev Side (T : Type*) [LT T] := {p : T × T // p.1 < p.2}

abbrev Interior (T : Type*) [LT T] (m r : ℕ) := Side T × Fin m × Fin r
abbrev Base (T : Type*) [LT T] (m r : ℕ) := Sum T (Interior T m r)

/-- Each side keeps its direct edge and receives `m` paths, each with `r`
interior vertices numbered from zero. The resulting path length is `r+1`. -/
def step {T : Type*} [LinearOrder T] {m r : ℕ} : Base T m r → Base T m r → Prop
  | .inl u, .inl v => u < v
  | .inl u, .inr (e,_,j) => (u = e.val.1 ∧ j.val = 0) ∨ (u = e.val.2 ∧ j.val+1 = r)
  | .inr _, .inl _ => False
  | .inr (e,i,j), .inr (d,k,z) => e = d ∧ i = k ∧ j.val+1 = z.val

def expanded (T : Type*) [LinearOrder T] (m r : ℕ) : SimpleGraph (Base T m r) :=
  SimpleGraph.fromRel step

/-- The negative edge is the right terminal edge of each long path. The twist
changes every right-terminal incidence on one side, including its direct edge. -/
def signBit {T : Type*} [LinearOrder T] {m r : ℕ} (twist : Bool) (d : Side T) :
    Base T m r → Base T m r → Bool
  | .inl u, .inl v => twist && decide (s(u,v) = s(d.val.1,d.val.2))
  | .inl u, .inr (e,_,_) | .inr (e,_,_), .inl u => decide (u = e.val.2) && !(twist && decide (e = d))
  | .inr _, .inr _ => false

def signing {T : Type*} [LinearOrder T] {m r : ℕ} (twist : Bool) (d : Side T) : Signing (Base T m r) where
  neg := signBit twist d
  symm u v := by
    cases u with
    | inl u =>
      cases v with
      | inl v => simp only [signBit, Sym2.eq_swap (a := u) (b := v)]
      | inr v => rfl
    | inr u => cases v <;> rfl

/-- A map from fewer than `r` vertices misses a vertex on each long path. -/
theorem missing_position {K T : Type*} [Fintype K] [LinearOrder T] {m r : ℕ}
    (h : Fintype.card K < r) (f : K → Base T m r) (e : Side T) (i : Fin m) :
    ∃ j : Fin r, ∀ x, f x ≠ .inr (e,i,j) := by
  classical
  by_contra! hn
  choose g hg using hn
  have hi : Function.Injective g := by
    intro j k he
    have hval := (hg j).symm.trans ((congrArg f he).trans (hg k))
    simpa using hval
  have hc := Fintype.card_le_of_injective g hi
  simp only [Fintype.card_fin] at hc
  omega

/-- Gauge across the missing interior position. All terminals have zero phase. -/
def phase {T : Type*} [LinearOrder T] {m r : ℕ} (cut : Side T → Fin m → Fin r) : Base T m r → Bool
  | .inl _ => false
  | .inr (e,i,j) => decide ((cut e i).val < j.val)

def avoids {T : Type*} [LinearOrder T] {m r : ℕ} (cut : Side T → Fin m → Fin r) : Base T m r → Prop
  | .inl _ => True
  | .inr (e,i,j) => j ≠ cut e i

theorem phase_step {T : Type*} [LinearOrder T] {m r : ℕ} (cut : Side T → Fin m → Fin r) (d : Side T)
    {u v : Base T m r} (hu : avoids cut u) (hv : avoids cut v) (he : step u v) :
    (phase cut u ^^ phase cut v) = signBit false d u v := by
  cases u with
  | inl u =>
    cases v with
    | inl v => rfl
    | inr v =>
      obtain ⟨e,i,j⟩ := v
      change j ≠ cut e i at hv
      obtain ⟨rfl, hj⟩ | ⟨rfl, hj⟩ := he
      · simp [phase, signBit, hj, ne_of_lt e.property]
      · have hne : j.val ≠ (cut e i).val := fun h => hv (Fin.ext h)
        have hc : (cut e i).val < j.val := by have := (cut e i).isLt; omega
        simp [phase, signBit, hc]
  | inr u =>
    obtain ⟨e,i,j⟩ := u
    cases v with
    | inl v => exact False.elim he
    | inr v =>
      obtain ⟨d',k,z⟩ := v
      rcases he with ⟨rfl, rfl, hz⟩
      have hn : z.val ≠ (cut e i).val := fun h => hv (Fin.ext h)
      have eq : (cut e i).val < j.val ↔ (cut e i).val < z.val := by
        have hn' : j.val ≠ (cut e i).val := fun h => hu (Fin.ext h)
        omega
      simp [phase, signBit, eq]

theorem positive_lift {K T : Type*} [Fintype K] [LinearOrder T] {m r : ℕ} {F : SimpleGraph K}
    (h : Fintype.card K < r) (d : Side T) (f : F →g expanded T m r) : Nonempty (Sheets (signing false d) f) := by
  classical
  choose cut hc using missing_position h f
  have ha (x : K) : avoids cut (f x) := by
    cases hf : f x with
    | inl _ => trivial
    | inr v =>
      obtain ⟨e,i,j⟩ := v
      change j ≠ cut e i
      rintro rfl
      exact hc e i x hf
  refine ⟨⟨fun x => phase cut (f x), fun i j he => ?_⟩⟩
  rcases (f.map_adj he).2 with hstep | hstep
  · exact phase_step cut d (ha i) (ha j) hstep
  · rw [Bool.xor_comm, (signing false d).symm]
    exact phase_step cut d (ha j) (ha i) hstep

/-- Direct template edges give a canonical homomorphism from the pattern. -/
def templateHom {T : Type*} [LinearOrder T] (F : SimpleGraph T) (m r : ℕ) : F →g expanded T m r where
  toFun := .inl
  map_rel' := fun h => ⟨fun e => h.ne (Sum.inl.inj e), lt_or_gt_of_ne h.ne⟩

/-- The direct copy of a cycle through the distinguished edge cannot lift. -/
theorem twisted_no_lift {T : Type*} [LinearOrder T] (F : SimpleGraph T) (m r : ℕ) (d : Side T)
    (hadj : F.Adj d.val.1 d.val.2) (hpath : (F.deleteEdges {s(d.val.1,d.val.2)}).Reachable d.val.1 d.val.2) :
    ¬ Nonempty (Sheets (signing true d) (templateHom F m r)) := by
  rintro ⟨c⟩
  have heq {i j : T} (he : (F.deleteEdges {s(d.val.1,d.val.2)}).Adj i j) : c.val i = c.val j := by
    obtain ⟨hh, hn⟩ := SimpleGraph.deleteEdges_adj.mp he
    have hin := c.property hh
    have hneq : s(i,j) ≠ s(d.val.1,d.val.2) := hn
    change (c.val i ^^ c.val j) = (true && decide (s(i,j) = s(d.val.1,d.val.2))) at hin
    have decode : ∀ a b : Bool, (a ^^ b) = false → a = b := by decide
    exact decode _ _ (by simpa only [decide_eq_false hneq, Bool.true_and] using hin)
  obtain ⟨w⟩ := hpath
  have hx := constant_on_walk (c := c.val) (fun _ _ h => heq h) w
  have ht := c.property hadj
  change (c.val d.val.1 ^^ c.val d.val.2) = (true && decide (s(d.val.1,d.val.2) = s(d.val.1,d.val.2))) at ht
  simp [hx] at ht

/-- Every cyclic pattern admits a choice of a twisted template side whose
endpoints remain connected after deleting that side. -/
theorem cyclic_side {T : Type*} [LinearOrder T] (F : SimpleGraph T) (h : ¬F.IsAcyclic) :
    ∃ d : Side T, F.Adj d.val.1 d.val.2 ∧
      (F.deleteEdges {s(d.val.1,d.val.2)}).Reachable d.val.1 d.val.2 := by
  classical
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at h
  push Not at h
  obtain ⟨i,j,he,hn⟩ := h
  have hw : (F.deleteEdges {s(i,j)}).Reachable i j := not_not.mp hn
  rcases lt_or_gt_of_ne he.ne with hij | hji
  · exact ⟨⟨(i,j),hij⟩, he, hw⟩
  · refine ⟨⟨(j,i),hji⟩, he.symm, ?_⟩
    simpa only [Sym2.eq_swap (a := j) (b := i)] using hw.symm

end JointForest
