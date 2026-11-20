module

public import SolvedProblems.SelectedClass

public section

namespace SelectedDisagreement

theorem distinct_hypotheses : ∀ ⦃g h : Hyp⦄, label g = label h → g = h := by
  intro g h eq
  have atPoint (x : Point) := congrFun eq x
  cases g <;> cases h
  all_goals try rfl
  case central.fallback => have := atPoint (.marker 0); simp [label] at this
  case fallback.central => have := atPoint (.marker 0); simp [label] at this
  case central.named a => have := atPoint (.marker (a+1)); simp [label] at this
  case named.central a => have := atPoint (.marker (a+1)); simp [label] at this
  case fallback.named a => have := atPoint (.marker a); simp [label] at this
  case named.fallback a => have := atPoint (.marker a); simp [label] at this
  case named.named a b =>
    have := atPoint (.marker a)
    by_cases hab : a = b
    · rw [hab]
    · simp [label, Ne.symm hab] at this

theorem observe_fits (g t : Hyp) (s : List Point) :
    fits g (observe t s) ↔ ∀ x ∈ s, label g x = label t x := by
  constructor
  · intro h x hx
    exact h x _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  · intro h x y hxy
    obtain ⟨z,hz,eq⟩ := List.mem_map.mp hxy
    cases eq
    exact h _ hz

theorem select_fits (s) (t : Hyp) (ok : fits t s) : fits (select s) s := by
  classical
  unfold select
  split
  · assumption
  · split
    · exact Exists.choose_spec ‹∃ a, fits (.named a) s›
    · cases t with
      | central => exact ok
      | fallback => contradiction
      | named a => exact False.elim (‹¬ ∃ a, fits (.named a) s› ⟨a,ok⟩)

theorem named_unique {s a b} (hf : ¬ fits .fallback s) (ha : fits (.named a) s)
    (hb : fits (.named b) s) : a = b := by
  apply Classical.byContradiction
  intro ne
  apply hf
  intro x y hm
  have ea := ha x y hm
  have eb := hb x y hm
  cases x with
  | ordinary i => simp [label] at ea eb ⊢; split at ea <;> split at eb <;> omega
  | marker i => simp [label] at ea eb ⊢; split at ea <;> split at eb <;> omega

theorem named_marker {a t s} (sel : select (observe t s) = .named a) (wrong : t ≠ .named a) :
    Point.marker a ∈ s := by
  classical
  have h := (observe_fits _ _ _).mp (select_fits _ t ((observe_fits t t s).mpr (fun _ _ => rfl)))
  rw [sel] at h
  have hf : ¬ fits .fallback (observe t s) := by
    intro hf
    simp [select,hf] at sel
  rw [observe_fits] at hf
  simp only [Classical.not_forall] at hf
  obtain ⟨x,hx,ne⟩ := hf
  have eq := h x hx
  cases t with
  | central =>
    cases x with
    | ordinary i => simp [label] at ne
    | marker b => simp [label] at eq; simpa [eq] using hx
  | fallback => contradiction
  | named b =>
    have ab : a ≠ b := by rintro rfl; exact wrong rfl
    cases x with
    | ordinary i => simp [label] at ne; simp [label, ne] at eq; split at eq <;> omega
    | marker b' => simp [label] at eq; split at eq <;> split at eq <;> simp_all

theorem select_marker (a : Nat) : select (observe .central [.marker a]) = .named a := by
  classical
  have h (g : Hyp) : fits g (observe .central [.marker a]) ↔ label g (.marker a) = 0 := by
    rw [observe_fits]
    simp [label]
  have hf : ¬ fits .fallback (observe .central [.marker a]) := by simp [h, label]
  have ha : fits (.named a) (observe .central [.marker a]) := by simp [h,label]
  have ex : ∃ b, fits (.named b) (observe .central [.marker a]) := ⟨a,ha⟩
  simp only [select, ite_eq_right hf, dite_eq_left ex]
  rw [named_unique hf ex.choose_spec ha]

private theorem bits (n : Nat) (v : Nat → Bool) :
    ∃ a : Nat, ∀ i < n, a.testBit i = v i := by
  induction n with
  | zero => exact ⟨0, by omega⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := ih
    refine ⟨if v n then a ||| 2^n else a &&& (2^n-1),?_⟩
    intro i hi
    by_cases eq : i = n
    · subst i
      cases v n <;> simp [Nat.testBit_two_pow_self]
    · have ilt : i < n := by omega
      cases v n <;> simp [ne_comm.mp eq, ilt,ha i ilt]

/-- Every labelling of the first n ordinary points occurs as the disagreement
with the central hypothesis of a hypothesis actually selected on central-target data. -/
theorem shatters (n : Nat) (v : Nat → Bool) : ∃ s : List Point,
    ∀ i < n, (label (select (observe .central s)) (.ordinary i) ≠ label .central (.ordinary i)
      ↔ v i = true) := by
  obtain ⟨a,ha⟩ := bits n v
  refine ⟨[.marker a],?_⟩
  intro i hi
  rw [select_marker]
  cases h : v i <;> simp [label,ha i hi,h]

end SelectedDisagreement
