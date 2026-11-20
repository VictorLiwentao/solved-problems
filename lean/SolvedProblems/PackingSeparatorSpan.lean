module

public import Std

public section

namespace PackingSeparatorSpan

/-- Coordinate after traversing the first i gaps, stopping at the right endpoint. -/
private def coord : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | a :: rest, i+1 => a + coord rest i

private abbrev Vertex (g : List Nat) (x : Nat) := ∃ i, coord g i = x

private theorem coord_zero (g : List Nat) : coord g 0 = 0 := by cases g <;> rfl

private theorem coord_length (g : List Nat) : coord g g.length = g.sum := by
  induction g with
  | nil => rfl
  | cons a g ih => simp [coord, ih]

private theorem coord_le_sum (g : List Nat) (i : Nat) : coord g i ≤ g.sum := by
  induction g generalizing i with
  | nil => simp [coord]
  | cons a g ih =>
    cases i with
    | zero => simp [coord]
    | succ i => exact Nat.add_le_add_left (ih i) a

private theorem refineAt (g : List Nat) (x : Nat) (ne : g ≠ []) (bound : x ≤ g.sum) :
    ∃ h : List Nat, h.sum = g.sum ∧ h.length = g.length+1 ∧ Vertex h x ∧
      ∀ y, Vertex g y → Vertex h y := by
  induction g generalizing x with
  | nil => contradiction
  | cons a g ih =>
    simp only [List.sum_cons] at bound
    by_cases le : x ≤ a
    · refine ⟨x::(a-x)::g, ?_, rfl, ⟨1, by simp [coord]⟩, ?_⟩
      · simp only [List.sum_cons]
        omega
      · rintro y ⟨i, rfl⟩
        cases i with
        | zero => exact ⟨0,rfl⟩
        | succ j =>
          refine ⟨j+2, ?_⟩
          simp only [coord]
          omega
    · have remaining : x-a ≤ g.sum := by omega
      have nonempty : g ≠ [] := by
        rintro rfl
        simp at bound
        omega
      obtain ⟨h, sumEq, lenEq, ⟨i, hi⟩, old⟩ := ih (x-a) nonempty remaining
      refine ⟨a::h, by simp [sumEq], by simp [lenEq], ⟨i+1, ?_⟩, ?_⟩
      · simp only [coord, hi]
        omega
      · rintro y ⟨j, rfl⟩
        cases j with
        | zero => exact ⟨0,rfl⟩
        | succ j =>
          obtain ⟨v,hv⟩ := old (coord g j) ⟨j,rfl⟩
          exact ⟨v+1, congrArg (a+·) hv⟩

private theorem partitionAt (S : Nat) (marks : List Nat) (inSpan : ∀ x ∈ marks, x ≤ S) :
    ∃ g : List Nat, g.sum = S ∧ g.length = marks.length+1 ∧ ∀ x ∈ marks, Vertex g x := by
  induction marks with
  | nil => exact ⟨[S], by simp, rfl, by simp⟩
  | cons x marks ih =>
    obtain ⟨g,gs,gl,old⟩ := ih (fun y hy => inSpan _ (List.mem_cons_of_mem _ hy))
    have nonempty : g ≠ [] := by rintro rfl; simp at gl
    obtain ⟨h,hs,hl,hx,retained⟩ := refineAt g x nonempty (gs ▸ inSpan x List.mem_cons_self)
    refine ⟨h,hs.trans gs,by simp [hl,gl],?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl|hm
    · exact hx
    · exact retained _ (old _ hm)

/-- A pair of partitions with the same gap lengths up to clipping at b. -/
private inductive Matched (b : Nat) : List Nat → List Nat → Prop
  | nil : Matched b [] []
  | cons {x y g h} : min b x = min b y → Matched b g h → Matched b (x::g) (y::h)

private theorem clipped (b : Nat) (g : List Nat) : Matched b g (g.map (min b)) := by
  induction g with
  | nil => exact .nil
  | cons a g ih => exact .cons (by omega) ih

private theorem clipped_sum (b : Nat) (g : List Nat) : (g.map (min b)).sum ≤ g.length*b := by
  induction g with
  | nil => simp
  | cons a g ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

private theorem fitTo (g : List Nat) (b T : Nat) (nonempty : g ≠ [])
    (large : g.length*b ≤ g.sum) (room : g.length*b ≤ T) :
    ∃ h : List Nat, Matched b g h ∧ h.sum = T := by
  induction g generalizing T with
  | nil => contradiction
  | cons a g ih =>
    simp only [List.length_cons, Nat.succ_mul, List.sum_cons] at large room
    by_cases big : b ≤ a
    · let tail := g.map (min b)
      have tailBound : tail.sum ≤ g.length*b := clipped_sum b g
      have bank : b ≤ T-tail.sum := by omega
      refine ⟨(T-tail.sum)::tail, .cons (by omega) (clipped b g), ?_⟩
      simp only [List.sum_cons]
      omega
    · have ne : g ≠ [] := by rintro rfl; simp_all; omega
      obtain ⟨h,rel,hs⟩ := ih (T-a) ne (by omega) (by omega)
      exact ⟨a::h,.cons rfl rel,by simp [hs]; omega⟩

private theorem sameLength {b g h} (rel : Matched b g h) : g.length = h.length := by
  induction rel with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem clip_add {b x x' y y' : Nat}
    (a : min b x = min b x') (c : min b y = min b y') :
    min b (x+y) = min b (x'+y') := by omega

private theorem prefix_clip {b g h} (rel : Matched b g h) (j : Nat) :
    min b (coord g j) = min b (coord h j) := by
  induction rel generalizing j with
  | nil => rfl
  | cons eq _ ih =>
    cases j with
    | zero => rfl
    | succ j => exact clip_add eq (ih j)

private theorem distance_clip {b g h} (rel : Matched b g h) (i j : Nat) :
    min b (coord g j - coord g i) = min b (coord h j - coord h i) := by
  induction rel generalizing i j with
  | nil => rfl
  | @cons x y g h eq rel ih =>
    cases i with
    | zero => simpa only [coord_zero, Nat.sub_zero] using prefix_clip (Matched.cons eq rel) j
    | succ i =>
      cases j with
      | zero => simp [coord]
      | succ j => simpa only [coord, Nat.add_sub_add_left] using ih i j

/-- Five marked coordinates and the two endpoints can be moved between any two
spans of length at least 6b while preserving every directed distance truncated at b. -/
theorem transferFive {b S T : Nat} (hb : 0 < b) (hs : 6*b ≤ S) (ht : 6*b ≤ T)
    (p : Fin 5 → Nat) (hp : ∀ i, p i ≤ S) :
    ∃ f : Nat → Nat, f 0 = 0 ∧ f S = T ∧ (∀ x ≤ S, f x ≤ T) ∧
      ∀ x y, (x = 0 ∨ x = S ∨ ∃ i, p i = x) → (y = 0 ∨ y = S ∨ ∃ i, p i = y) →
        min b (f y - f x) = min b (y-x) := by
  classical
  obtain ⟨g,gs,gl,marked⟩ := partitionAt S (List.ofFn p) (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hp i)
  simp only [List.length_ofFn] at gl
  have ne : g ≠ [] := by rintro rfl; simp at gl
  obtain ⟨h,rel,hsum⟩ := fitTo g b T ne (by simpa [gs,gl] using hs) (by simpa [gl] using ht)
  let f := fun x => if v : Vertex g x then coord h v.choose else 0
  have atCoord (i : Nat) : f (coord g i) = coord h i := by
    have ex : Vertex g (coord g i) := ⟨i,rfl⟩
    simp only [f, dite_eq_left ex]
    have forward := distance_clip rel i ex.choose
    have back := distance_clip rel ex.choose i
    rw [ex.choose_spec] at forward back
    omega
  have left : f 0 = 0 := by simpa only [coord_zero] using atCoord 0
  have right : f S = T := by
    have hRight := atCoord g.length
    rw [coord_length,gs,sameLength rel,coord_length,hsum] at hRight
    exact hRight
  have locate (x) (hx : x=0 ∨ x=S ∨ ∃ i, p i=x) : Vertex g x := by
    rcases hx with rfl|rfl|⟨i,rfl⟩
    · exact ⟨0,coord_zero g⟩
    · exact ⟨g.length,(coord_length g).trans gs⟩
    · exact marked _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  refine ⟨f,left,right,?_,?_⟩
  · intro x _
    dsimp only [f]
    split
    · exact hsum ▸ coord_le_sum h _
    · exact Nat.zero_le _
  · intro x y hx hy
    obtain ⟨i,rfl⟩ := locate x hx
    obtain ⟨j,rfl⟩ := locate y hy
    simpa only [atCoord] using (distance_clip rel i j).symm

end PackingSeparatorSpan
