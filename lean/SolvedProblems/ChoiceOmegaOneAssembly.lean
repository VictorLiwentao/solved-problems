module

public import SolvedProblems.ChoiceOmegaOneSequence
public import SolvedProblems.ChoiceOmegaOneBranches
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Subgroup
open scoped commutatorElement

variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V] {x : V}
variable (W : Witness I P V x)

/-- Read the unique selected block containing a coordinate, if any. -/
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

/-- Simultaneously apply one element per active block; disjointness makes this
a single element of the full direct product. -/
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
/-- The four-branch commutator contradicts countability of the orbit. -/
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
