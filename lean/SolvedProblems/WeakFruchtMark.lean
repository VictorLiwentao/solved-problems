module

public import SolvedProblems.WeakFruchtGraph
public import SolvedProblems.FiniteFruchtPaths

@[expose] public section

namespace WeakFrucht

variable {R : Type u} (A : SimpleGraph R)

/-- Connect two new points to one old point and to each other. When the original
graph is triangle-free the old marked point can be recovered intrinsically. -/
def addTriangle (m : R) : SimpleGraph (R ⊕ Bool) where
  Adj
    | .inl a,.inl b => A.Adj a b
    | .inl a,.inr _ => a = m
    | .inr _,.inl a => a = m
    | .inr a,.inr b => a ≠ b
  symm := ⟨by rintro (a|a) (b|b) h; exact h.symm; exact h; exact h; exact h.symm⟩
  loopless := ⟨by rintro (a|a); exact A.loopless.irrefl _; exact fun h => h rfl⟩

def Triangle {Y : Type u} (B : SimpleGraph Y) (v : Y) : Prop :=
  ∃ a b, B.Adj v a ∧ B.Adj a b ∧ B.Adj b v
private def Low {Y : Type u} (B : SimpleGraph Y) (v : Y) : Prop :=
  ∃ a b, ∀ c, B.Adj v c → c = a ∨ c = b

private theorem triangle_maps {Y Z} {B : SimpleGraph Y} {C : SimpleGraph Z} (f : Iso B.Adj C.Adj)
    {v} (h : Triangle B v) : Triangle C (f.toEquiv v) := by
  obtain ⟨a,b,va,ab,bv⟩ := h
  exact ⟨_,_,(f.edges _ _).mpr va,(f.edges _ _).mpr ab,(f.edges _ _).mpr bv⟩

private theorem low_maps {Y Z} {B : SimpleGraph Y} {C : SimpleGraph Z} (f : Iso B.Adj C.Adj)
    {v} (h : Low B v) : Low C (f.toEquiv v) := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨f.toEquiv a,f.toEquiv b,?_⟩
  intro c hc
  obtain ⟨t,rfl⟩ := f.toEquiv.surjective c
  exact (h t ((f.edges _ _).mp hc)).imp (congrArg _) (congrArg _)

private theorem old_triangle {m r : R} (free : ∀ x, ¬ Triangle A x) :
    Triangle (addTriangle A m) (.inl r) → r = m := by
  rintro ⟨(a|a),(b|b),ra,ab,br⟩
  · exact (free r ⟨a,b,ra,ab,br⟩).elim
  · exact br
  · exact ra
  · exact ra

private theorem extra_characterization {m : R} (free : ∀ x, ¬ Triangle A x) (neigh : ∃ r, A.Adj m r)
    (v : R ⊕ Bool) : Triangle (addTriangle A m) v ∧ Low (addTriangle A m) v ↔ v.isRight = true := by
  cases v with
  | inl r =>
    constructor
    · rintro ⟨h,a,b,low⟩
      obtain rfl := old_triangle A free h
      obtain ⟨s,ms⟩ := neigh
      have p := low (.inl s) ms
      have t := low (.inr true) rfl
      have f := low (.inr false) rfl
      rcases p with rfl|rfl <;> rcases t with t|t <;> rcases f with f|f <;> simp_all <;> exact Bool.noConfusion (Sum.inr.inj (t.trans f.symm))
    · intro h; cases h
  | inr v =>
    constructor
    · intro _; rfl
    · intro _
      have opposite : v ≠ !v := by cases v <;> decide
      refine ⟨⟨.inl m,.inr (!v),rfl,rfl,opposite.symm⟩,.inl m,.inr (!v),?_⟩
      rintro (r|b) h
      · exact Or.inl (congrArg Sum.inl h)
      · right; apply congrArg Sum.inr
        change v ≠ b at h
        cases v <;> cases b <;> simp_all

private def unmark (m : R) : R ⊕ Bool → R
  | .inl x => x
  | .inr _ => m

/-- An unpointed isomorphism between two marked graphs induces an automorphism
of the original triangle-free graph carrying the first mark to the second. -/
theorem recover_mark {m n : R} (free : ∀ x, ¬ Triangle A x) (hm : ∃ r, A.Adj m r) (hn : ∃ r, A.Adj n r)
    (iso : Iso (addTriangle A m).Adj (addTriangle A n).Adj) :
    ∃ f : Equiv.Perm R, FiniteFrucht.Preserves A f ∧ f m = n := by
  have old {m n : R} (hm : ∃ r, A.Adj m r) (hn : ∃ r, A.Adj n r)
      (g : Iso (addTriangle A m).Adj (addTriangle A n).Adj) (r : R) :
      g.toEquiv (.inl r) = .inl (unmark n (g.toEquiv (.inl r))) := by
    cases he : g.toEquiv (.inl r) with
    | inl s => rfl
    | inr b =>
      have p := (extra_characterization A free hn (.inr b)).mpr rfl
      have t := triangle_maps g.symm p.1
      have l := low_maps g.symm p.2
      have e : g.symm.toEquiv (.inr b) = .inl r := by rw [← he]; exact g.toEquiv.symm_apply_apply _
      rw [e] at t l
      exact False.elim (Bool.noConfusion ((extra_characterization A free hm (.inl r)).mp ⟨t,l⟩))
  let f : Equiv.Perm R := {
    toFun := fun a => unmark n (iso.toEquiv (.inl a))
    invFun := fun b => unmark m (iso.toEquiv.symm (.inl b))
    left_inv := fun r => by dsimp only; rw [← old hm hn iso r,Equiv.symm_apply_apply]; rfl
    right_inv := fun r => by
      change unmark n (iso.toEquiv (.inl (unmark m (iso.symm.toEquiv (.inl r))))) = r
      rw [← old hn hm iso.symm]; change unmark n (iso.toEquiv (iso.toEquiv.symm _)) = _
      rw [Equiv.apply_symm_apply]; rfl }
  have im (r : R) : iso.toEquiv (.inl r) = .inl (f r) := old hm hn iso r
  refine ⟨f,?_,?_⟩
  · intro x y
    have h := iso.edges (.inl x) (.inl y)
    rw [im,im] at h
    exact h
  · have h : Triangle (addTriangle A m) (.inl m) := ⟨.inr false,.inr true,rfl,Bool.false_ne_true,rfl⟩
    have t := triangle_maps iso h
    rw [im] at t
    exact old_triangle A free t

theorem reach_reverse {Y} {B : SimpleGraph Y} {a b} (h : Reach B.Adj a b) : Reach B.Adj b a := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.head e.symm

/-- Marking a vertex preserves connectedness. -/
theorem mark_connected (conn : ∀ x y, Reach A.Adj x y) (m : R) (a b : R ⊕ Bool) :
    Reach (addTriangle A m).Adj a b := by
  have fromRoot (v : R ⊕ Bool) : Reach (addTriangle A m).Adj (.inl m) v := by
    cases v with
    | inl x => exact reach_map Sum.inl (fun h => h) (conn m x)
    | inr b => exact .single rfl
  exact (reach_reverse (fromRoot a)).trans (fromRoot b)

/-- Substituting the three identifying paths preserves connectedness. -/
theorem paths_connected (col : R → ℕ) (conn : ∀ x y, Reach A.Adj x y)
    (x y : FiniteFrucht.Vertex col) : Reach (FiniteFrucht.graph A col).Adj x y := by
  have fromRoot (v : FiniteFrucht.Vertex col) : Reach (FiniteFrucht.graph A col).Adj (.base (FiniteFrucht.root col v)) v := by
    cases v with
    | base r => exact .refl
    | tip r b j hj =>
      change Reach (FiniteFrucht.graph A col).Adj (.base r) (.tip r b j hj)
      induction j with
      | zero => exact .single ⟨rfl,rfl⟩
      | succ j ih => exact (ih (Nat.lt_of_succ_lt hj)).tail ⟨rfl,rfl,Or.inl rfl⟩
  exact (reach_reverse (fromRoot x)).trans ((reach_map FiniteFrucht.Vertex.base (fun h => h) (conn _ _)).trans (fromRoot y))

/-- Extending a bipartition along each pendant path keeps the graph triangle-free. -/
theorem paths_no_triangle (col : R → ℕ) (side : R → Bool) (different : ∀ {x y}, A.Adj x y → side x ≠ side y)
    (v : FiniteFrucht.Vertex col) : ¬ Triangle (FiniteFrucht.graph A col) v := by
  let paint : FiniteFrucht.Vertex col → Bool
    | .base r => side r
    | .tip r _ j _ => if j%2 = 0 then !(side r) else side r
  have mismatch {a b} (e : (FiniteFrucht.graph A col).Adj a b) : paint a ≠ paint b := by
    cases a with
    | base r =>
      cases b with
      | base s => exact different e
      | tip s c j hj => obtain ⟨rfl,rfl⟩ := e; simp [paint]
    | tip r k j hj =>
      cases b with
      | base s => obtain ⟨rfl,rfl⟩ := e; simp [paint]
      | tip s c l hl =>
        obtain ⟨rfl,rfl,adj⟩ := e
        rcases adj with rfl | rfl <;> simp only [paint] <;> split <;> split <;> first | omega | simp
  rintro ⟨a,b,va,ab,bv⟩
  have p := mismatch va
  have q := mismatch ab
  have t := mismatch bv
  cases h₁ : paint v <;> cases h₂ : paint a <;> cases h₃ : paint b <;> simp_all

end WeakFrucht
