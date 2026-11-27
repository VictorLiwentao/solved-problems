module

public import SolvedProblems.FiniteFruchtSelector
public import SolvedProblems.FiniteFruchtPaths

@[expose] public section

namespace FiniteFrucht

/-- The two copies of G are kept distinct. A multiplication triple has separate
input and output vertices, even if its two group arguments coincide. -/
inductive Tag | pt | label | subset | family | pick | triple | input | output

def Tag.code : Tag → ℕ
  | .pt => 0 | .label => 1 | .subset => 2 | .family => 3
  | .pick => 4 | .triple => 5 | .input => 6 | .output => 7

private theorem code_injective : Function.Injective Tag.code := by
  intro i j h
  cases i <;> cases j <;> simp_all [Tag.code]

abbrev Data (G : Type u) : Tag → Type u
  | .pt | .label => G
  | .subset => Set G
  | .family | .pick => Family (Set G)
  | .triple | .input | .output => G × G

abbrev Core (G : Type u) := Sigma (Data G)

def color {G : Type u} (q : Core G) := q.1.code

variable {G : Type u} [Group G] (sel : Family (Set G) → Set G)

/-- Adjacency between distinct sorts records both membership relations, the
selector, and the three ordered arguments of the multiplication relation. -/
def arcs : (i j : Tag) → Data G i → Data G j → Prop
  | .pt, .input, x, t => x = t.1
  | .pt, .output, x, t => x = t.1*t.2
  | .label, .subset, x, S => x ∈ S
  | .label, .triple, x, t => x = t.2
  | .subset, .family, S, F => S ∈ F.val
  | .subset, .pick, S, F => S = sel F
  | .family, .pick, F, H => F = H
  | .triple, .input, t, q => t = q
  | .triple, .output, t, q => t = q
  | _, _, _, _ => False

def coreGraph : SimpleGraph (Core G) where
  Adj u v := arcs sel u.1 v.1 u.2 v.2 ∨ arcs sel v.1 u.1 v.2 u.2
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by rintro ⟨i,x⟩; cases i <;> simp [arcs]⟩

/-- Left multiplication acts on group points and on the first component of a
multiplication triple. It acts identically on the whole label structure. -/
def translation (a : G) : (i : Tag) → Data G i → Data G i
  | .pt, x => a*x
  | .label, x => x
  | .subset, S => S
  | .family, F => F
  | .pick, F => F
  | .triple, t => (a*t.1,t.2)
  | .input, t => (a*t.1,t.2)
  | .output, t => (a*t.1,t.2)

def corePerm (a : G) : Equiv.Perm (Core G) where
  toFun q := ⟨q.1, translation a q.1 q.2⟩
  invFun q := ⟨q.1, translation a⁻¹ q.1 q.2⟩
  left_inv := by rintro ⟨i,x⟩; cases i <;> simp [translation]
  right_inv := by rintro ⟨i,x⟩; cases i <;> simp [translation]

theorem corePerm_color (a : G) (q : Core G) : color (corePerm a q) = color q := rfl

private theorem translation_arcs (a : G) (i j : Tag) (x : Data G i) (y : Data G j) :
    arcs sel i j (translation a i x) (translation a j y) ↔ arcs sel i j x y := by
  cases i <;> cases j <;> simp [arcs,translation,mul_assoc]
  all_goals exact ⟨fun h => Prod.ext h.1 h.2,fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩

theorem corePerm_adj (a : G) : Preserves (coreGraph sel) (corePerm a) := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  exact or_congr (translation_arcs sel a i j x y) (translation_arcs sel a j i y x)

private def valAt {K : Type v} {T : K → Type u} (q : Sigma T) {k : K} (e : q.1 = k) : T k :=
  e ▸ q.2

private theorem mk_valAt {K : Type v} {T : K → Type u} (q : Sigma T) {k : K} (e : q.1 = k) :
    (⟨k,valAt q e⟩ : Sigma T) = q := by cases q; cases e; rfl

private theorem mk_inj {K : Type v} {T : K → Type u} {k : K} {x y : T k}
    (h : (⟨k,x⟩ : Sigma T) = ⟨k,y⟩) : x = y := eq_of_heq (Sigma.mk.inj h).2

private theorem symm_typed {K : Type v} {T : K → Type u} (f : Equiv.Perm (Sigma T))
    (typed : ∀ u, (f u).1 = u.1) (u : Sigma T) : (f.symm u).1 = u.1 := by
  simpa using (typed (f.symm u)).symm

private def sortPerm {K : Type v} {T : K → Type u} (f : Equiv.Perm (Sigma T))
    (typed : ∀ u, (f u).1 = u.1) (k : K) : Equiv.Perm (T k) where
  toFun x := valAt (f ⟨k,x⟩) (typed ⟨k,x⟩)
  invFun x := valAt (f.symm ⟨k,x⟩) (symm_typed f typed ⟨k,x⟩)
  left_inv x := by
    apply mk_inj; dsimp only; rw [mk_valAt,mk_valAt,f.symm_apply_apply]
  right_inv x := by
    apply mk_inj; dsimp only; rw [mk_valAt,mk_valAt,f.apply_symm_apply]

private theorem sort_eq {K : Type v} {T : K → Type u} (f : Equiv.Perm (Sigma T))
    (typed : ∀ u, (f u).1 = u.1) (k : K) (x : T k) :
    f ⟨k,x⟩ = ⟨k,sortPerm f typed k x⟩ := (mk_valAt _ _).symm

/-- A color-preserving automorphism is uniquely a left translation. Its group
element is read off at the identity point. -/
theorem core_is_translation (em : ∀ p : Prop, p ∨ ¬p) (member : ∀ F, sel F ∈ F.val)
    (f : Equiv.Perm (Core G)) (hc : ∀ u, color (f u) = color u)
    (hf : Preserves (coreGraph sel) f) : ∃ a : G, ∀ u, f u = corePerm a u := by
  have typed (u : Core G) : (f u).1 = u.1 := code_injective (hc u)
  let a := sortPerm f typed
  have adj (i j : Tag) (x : Data G i) (y : Data G j) :
      (coreGraph sel).Adj ⟨i,a i x⟩ ⟨j,a j y⟩ ↔ (coreGraph sel).Adj ⟨i,x⟩ ⟨j,y⟩ := by
    rw [← sort_eq f typed,← sort_eq f typed]
    exact hf _ _
  have inc (x : G) (S : Set G) : a .label x ∈ a .subset S ↔ x ∈ S := by
    simpa [coreGraph,arcs] using adj .label .subset x S
  have img_eq (S : Set G) : a .subset S = img (a .label) S := by
    ext y
    change y ∈ a .subset S ↔ (a .label).symm y ∈ S
    simpa only [Equiv.apply_symm_apply] using inc ((a .label).symm y) S
  have fam (S : Set G) (F : Family (Set G)) : a .subset S ∈ (a .family F).val ↔ S ∈ F.val := by
    simpa [coreGraph,arcs] using adj .subset .family S F
  have pick_eq (F : Family (Set G)) : a .family F = a .pick F := by
    simpa [coreGraph,arcs] using (adj .family .pick F F).mpr (Or.inl rfl)
  have choose_eq (F : Family (Set G)) : a .subset (sel F) = sel (a .family F) := by
    rw [pick_eq]; simpa [coreGraph,arcs] using (adj .subset .pick (sel F) F).mpr (Or.inl rfl)
  have family_fixed (F : Family (Set G)) (stable : ∀ S, S ∈ F.val ↔ a .subset S ∈ F.val) : a .family F = F := by
    apply Subtype.ext
    ext T
    obtain ⟨S,rfl⟩ := (a .subset).surjective T
    exact (fam S F).trans (stable S)
  have label_fixed : ∀ x : G, a .label x = x := by
    apply selector_fixes em sel member
    intro F invariant
    have fixF := family_fixed F (fun S => by rw [img_eq]; exact invariant S)
    rw [← img_eq,choose_eq,fixF]
  have subset_fixed (S : Set G) : a .subset S = S := by
    ext x; simpa only [label_fixed] using inc x S
  have fam_fixed (F : Family (Set G)) : a .family F = F := family_fixed F (fun S => by rw [subset_fixed])
  have pick_fixed (F : Family (Set G)) : a .pick F = F := (pick_eq F).symm.trans (fam_fixed F)
  have third (h g : G) : (a .triple (h,g)).2 = g := by
    have := (adj .label .triple g (h,g)).mpr (Or.inl rfl)
    symm; simpa [coreGraph,arcs,label_fixed] using this
  have inlet (h g : G) : a .input (h,g) = a .triple (h,g) := by
    symm; simpa [coreGraph,arcs] using (adj .triple .input (h,g) (h,g)).mpr (Or.inl rfl)
  have outlet (h g : G) : a .output (h,g) = a .triple (h,g) := by
    symm; simpa [coreGraph,arcs] using (adj .triple .output (h,g) (h,g)).mpr (Or.inl rfl)
  have first (h g : G) : (a .triple (h,g)).1 = a .pt h := by
    have := (adj .pt .input h (h,g)).mpr (Or.inl rfl)
    symm; simpa [coreGraph,arcs,inlet] using this
  have trans (h : G) : a .pt h = (a .pt 1)*h := by
    have := (adj .pt .output h (1,h)).mpr (Or.inl (one_mul h).symm)
    simpa [coreGraph,arcs,outlet,first,third] using this
  have pair (h g : G) : a .triple (h,g) = ((a .pt 1)*h,g) := Prod.ext ((first h g).trans (trans h)) (third h g)
  refine ⟨a .pt 1,?_⟩
  rintro ⟨i,x⟩
  rw [sort_eq f typed]; change (⟨i,a i x⟩ : Core G) = ⟨i,translation _ i x⟩
  apply congrArg (Sigma.mk i)
  cases i with
  | pt => exact trans x
  | label => exact label_fixed x
  | subset => exact subset_fixed x
  | family => exact fam_fixed x
  | pick => exact pick_fixed x
  | triple => exact pair x.1 x.2
  | input => exact (inlet x.1 x.2).trans (pair x.1 x.2)
  | output => exact (outlet x.1 x.2).trans (pair x.1 x.2)

end FiniteFrucht
