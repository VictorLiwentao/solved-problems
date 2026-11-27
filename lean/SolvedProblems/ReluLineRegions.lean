module

public import SolvedProblems.ReluNetworkModel
public import SolvedProblems.ReluSignPolynomial
public import Mathlib.Data.Finset.NAry

@[expose] public section

namespace ReluMoments

abbrev Line := ℝ × ℝ

def Line.value (l : Line) (x : ℝ) : ℝ := l.1*x+l.2

def Line.add (l k : Line) : Line := (l.1+k.1,l.2+k.2)

def Line.sub (l k : Line) : Line := (l.1-k.1,l.2-k.2)

def Line.scale (w : ℝ) (l : Line) : Line := (w*l.1,w*l.2)

def Line.zero : Line := (0,0)

noncomputable def Network.lines {p : ℕ} (θ : Vector p) : Network 1 p → Finset Line
  | .constant r => {(0,r)}
  | .input _ => {(1,0)}
  | .parameter i => {(0,θ i)}
  | .add f g => Finset.image₂ Line.add (f.lines θ) (g.lines θ)
  | .scale i f => (f.lines θ).image (Line.scale (θ i))
  | .relu f => insert Line.zero (f.lines θ)

noncomputable def Network.gateLines {p : ℕ} (θ : Vector p) : Network 1 p → Finset Line
  | .constant _ | .input _ | .parameter _ => ∅
  | .add f g => f.gateLines θ ∪ g.gateLines θ
  | .scale _ f => f.gateLines θ
  | .relu f => f.gateLines θ ∪ f.lines θ

/-- A pair of points with the same activation decisions has a common affine
output branch. Gate tests include all potentially active pieces of each gate. -/
theorem Network.common_line {p : ℕ} (θ : Vector p) (f : Network 1 p) (x y : ℝ)
    (ht : ∀ l ∈ f.gateLines θ, 0 ≤ l.value x ↔ 0 ≤ l.value y) :
    ∃ l ∈ f.lines θ, f.eval θ (fun _ => x) = l.value x ∧ f.eval θ (fun _ => y) = l.value y := by
  induction f with
  | constant r => exact ⟨(0,r),by simp [lines],by simp [Line.value,eval],by simp [Line.value,eval]⟩
  | input i => exact ⟨(1,0),by simp [lines],by simp [Line.value,eval],by simp [Line.value,eval]⟩
  | parameter i => exact ⟨(0,θ i),by simp [lines],by simp [Line.value,eval],by simp [Line.value,eval]⟩
  | add f g hf hg =>
    obtain ⟨l,hl,hx,hy⟩ := hf (fun l hl => ht l (Finset.mem_union_left _ hl))
    obtain ⟨k,hk,hx',hy'⟩ := hg (fun k hk => ht k (Finset.mem_union_right _ hk))
    refine ⟨l.add k,Finset.mem_image₂_of_mem hl hk,?_,?_⟩
    · simp only [eval,hx,hx',Line.add,Line.value]; ring
    · simp only [eval,hy,hy',Line.add,Line.value]; ring
  | scale i f hf =>
    obtain ⟨l,hl,hx,hy⟩ := hf ht
    refine ⟨l.scale (θ i),Finset.mem_image_of_mem _ hl,?_,?_⟩
    · simp only [eval,hx,Line.scale,Line.value]; ring
    · simp only [eval,hy,Line.scale,Line.value]; ring
  | relu f hf =>
    obtain ⟨l,hl,hx,hy⟩ := hf (fun l hl => ht l (Finset.mem_union_left _ hl))
    have ht' := ht l (Finset.mem_union_right _ hl)
    by_cases hp : 0 ≤ l.value x
    · refine ⟨l,Finset.mem_insert_of_mem hl,?_,?_⟩
      · simp [eval,hx,max_eq_left hp]
      · simp [eval,hy,max_eq_left (ht'.mp hp)]
    · refine ⟨Line.zero,Finset.mem_insert_self _ _,?_,?_⟩
      · rw [eval,hx,max_eq_right (le_of_not_ge hp)]; simp [Line.zero,Line.value]
      · rw [eval,hy,max_eq_right (le_of_not_ge (mt ht'.mpr hp))]; simp [Line.zero,Line.value]

def Network.lineCount {d p : ℕ} : Network d p → ℕ
  | .constant _ | .input _ | .parameter _ => 1
  | .add f g => f.lineCount * g.lineCount
  | .scale _ f => f.lineCount
  | .relu f => f.lineCount + 1

def Network.testCount {d p : ℕ} : Network d p → ℕ
  | .constant _ | .input _ | .parameter _ => 0
  | .add f g => f.testCount + g.testCount
  | .scale _ f => f.testCount
  | .relu f => f.testCount + f.lineCount

theorem Network.card_lines {p : ℕ} (θ : Vector p) (f : Network 1 p) :
    (f.lines θ).card ≤ f.lineCount ∧ (f.gateLines θ).card ≤ f.testCount := by
  induction f with
  | constant _ | input _ | parameter _ => simp [lines,gateLines,lineCount,testCount]
  | add f g hf hg =>
    exact ⟨(Finset.card_image₂_le ..).trans (Nat.mul_le_mul hf.1 hg.1),
      (Finset.card_union_le ..).trans (Nat.add_le_add hf.2 hg.2)⟩
  | scale i f hf => exact ⟨Finset.card_image_le.trans hf.1,hf.2⟩
  | relu f hf => exact ⟨(Finset.card_insert_le ..).trans (Nat.add_le_add_right hf.1 1),
      (Finset.card_union_le ..).trans (Nat.add_le_add hf.2 hf.1)⟩

/-- Root locations of all candidate gate and comparison lines partition the
real line into finitely many intervals on which a difference has fixed sign. -/
noncomputable def lineRoot (l : Line) : ℝ := -l.2/l.1

theorem line_same_sign {s : Finset Line} {x y : ℝ} (h : SameCell (s.image lineRoot) x y)
    (l : Line) (hl : l ∈ s) : (0 ≤ l.value x ↔ 0 ≤ l.value y) := by
  by_cases hz : l.1 = 0
  · simp [Line.value,hz]
  have hm : lineRoot l ∈ s.image lineRoot := Finset.mem_image_of_mem _ hl
  have hx : x ≠ lineRoot l := fun e => h.1 (e ▸ hm)
  have hy : y ≠ lineRoot l := fun e => h.2.1 (e ▸ hm)
  have hxy := h.2.2 _ hm
  have heq (t : ℝ) : l.value t = l.1*(t-lineRoot l) := by
    simp only [Line.value,lineRoot]
    field_simp
    ring
  rw [heq,heq]
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simp only [mul_nonneg_iff,not_le_of_gt hneg,hneg.le,false_and,true_and,false_or,sub_nonpos]
    exact ⟨fun h => (hxy.mp (lt_of_le_of_ne h hx)).le,fun h => (hxy.mpr (lt_of_le_of_ne h hy)).le⟩
  · simp only [mul_nonneg_iff_of_pos_left hpos,sub_nonneg]
    exact ⟨fun h => le_of_not_gt (mt hxy.mpr (not_lt_of_ge h)),fun h => le_of_not_gt (mt hxy.mp (not_lt_of_ge h))⟩

def Network.pairCutBound {p r : ℕ} (f : Network 1 p) (g : Network 1 r) : ℕ :=
  f.testCount+g.testCount+f.lineCount*g.lineCount

theorem Network.sign_cuts {p r : ℕ} (f : Network 1 p) (g : Network 1 r) (θ : Vector p) (η : Vector r) :
    ∃ s : Finset ℝ, s.card ≤ f.pairCutBound g ∧
      ∀ x y, SameCell s x y → 0 ≤
        (f.eval θ (fun _ => x)-g.eval η (fun _ => x)) * (f.eval θ (fun _ => y)-g.eval η (fun _ => y)) := by
  let t := (f.gateLines θ ∪ g.gateLines η) ∪ Finset.image₂ Line.sub (f.lines θ) (g.lines η)
  refine ⟨t.image lineRoot,?_,?_⟩
  · apply Finset.card_image_le.trans
    exact (Finset.card_union_le ..).trans (Nat.add_le_add
      ((Finset.card_union_le ..).trans (Nat.add_le_add (f.card_lines θ).2 (g.card_lines η).2))
      ((Finset.card_image₂_le ..).trans (Nat.mul_le_mul (f.card_lines θ).1 (g.card_lines η).1)))
  · intro x y hxy
    obtain ⟨l,hl,hx,hy⟩ := f.common_line θ x y (fun l hl => line_same_sign hxy l
      (Finset.mem_union_left _ (Finset.mem_union_left _ hl)))
    obtain ⟨k,hk,hx',hy'⟩ := g.common_line η x y (fun k hk => line_same_sign hxy k
      (Finset.mem_union_left _ (Finset.mem_union_right _ hk)))
    have hs := line_same_sign hxy (l.sub k) (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hl hk))
    have hv (z : ℝ) : (l.sub k).value z = l.value z - k.value z := by simp [Line.value,Line.sub]; ring
    rw [hv,hv] at hs
    rw [hx,hx',hy,hy']
    by_cases hp : 0 ≤ l.value x-k.value x
    · exact mul_nonneg hp (hs.mp hp)
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hp) (le_of_not_ge (mt hs.mpr hp))

end ReluMoments
