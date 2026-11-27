module

public import SolvedProblems.ChainWordsExpansion

@[expose] public section

namespace ChainWords

theorem length_descWord {α : Type*} (f : α → ℕ) (l : List α) :
    (descWord f l).length = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rcases l with _ | ⟨y,l⟩
    · rfl
    · simp [descWord,ih]

private theorem allows_self (s : List Bool) : Allows s s := by
  induction s with
  | nil => exact .nil
  | cons b s ih => exact .cons (by cases b <;> simp) ih

private theorem allows_lt {s d : List Bool} (h : Allows s d) :
    d = s ∨ d.count false < s.count false := by
  induction h with
  | nil => exact Or.inl rfl
  | @cons b c s d h _ ih =>
    have hle : d.count false ≤ s.count false := ih.elim (fun h => h ▸ le_rfl) Nat.le_of_lt
    cases b <;> cases c <;> simp_all

noncomputable def exactCount {α : Type*} [Fintype α] [PartialOrder α]
    (f : α → ℕ) (n : ℕ) (d : List Bool) : ℕ := by
  classical exact ((extensions α n).filter (fun l => descWord f l.val = d)).card

private theorem fiber_sum {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ)
    (n : ℕ) (D : Finset (List Bool)) (hD : ∀ l ∈ extensions α n, descWord f l.val ∈ D)
    (s : List Bool) [DecidablePred (Allows s)] :
    ∑ d ∈ D.filter (Allows s), exactCount f n d =
      ((extensions α n).filter (fun l => Allows s (descWord f l.val))).card := by
  classical
  simp only [exactCount,Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_congr
  intro l hl
  simp [hD l hl]

private theorem equal_exact_counts {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
    (f : α ↪ ℕ) (g : β ↪ ℕ) (h : monomialCoefficient f = monomialCoefficient g)
    (n : ℕ) (D : Finset (List Bool)) (hP : ∀ l ∈ extensions α n, descWord f l.val ∈ D)
    (hQ : ∀ l ∈ extensions β n, descWord g l.val ∈ D) (s : List Bool) (hs : s ∈ D)
    (hlen : s.length+1 = n) : exactCount f n s = exactCount g n s := by
  classical
  have sums := calc
    ∑ d ∈ D.filter (Allows s), exactCount f n d =
        ((extensions α n).filter (fun l => Allows s (descWord f l.val))).card := fiber_sum f n D hP s
    _ = ((extensions β n).filter (fun l => Allows s (descWord g l.val))).card := by
      subst n
      exact (fundamental_expansion f s).symm.trans ((congrFun h _).trans (fundamental_expansion g s))
    _ = ∑ d ∈ D.filter (Allows s), exactCount g n d := (fiber_sum g n D hQ s).symm
  have hmem : s ∈ D.filter (Allows s) := Finset.mem_filter.mpr ⟨hs,allows_self s⟩
  have rest : ∑ d ∈ (D.filter (Allows s)).erase s, exactCount f n d =
      ∑ d ∈ (D.filter (Allows s)).erase s, exactCount g n d := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hne,hd⟩ := Finset.mem_erase.mp hd
    obtain ⟨hd,ha⟩ := Finset.mem_filter.mp hd
    exact equal_exact_counts f g h n D hP hQ d hd (by rw [← ha.length_eq,hlen])
  rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem,rest] at sums
  exact Nat.add_left_cancel sums
termination_by s.count false
decreasing_by exact (allows_lt ha).resolve_left hne

private theorem subset_of_equal_enumerators {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : fundamentalSupport f ⊆ fundamentalSupport g := by
  classical
  intro _ hc
  obtain ⟨l,he,rfl⟩ := hc
  let n := l.length
  let d := descWord f l
  let v : List.Vector α n := ⟨l,rfl⟩
  let D := ((extensions α n).image fun r => descWord f r.val) ∪ ((extensions β n).image fun r => descWord g r.val)
  have hP (r : List.Vector α n) (hr : r ∈ extensions α n) : descWord f r.val ∈ D :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)
  have hQ (r : List.Vector β n) (hr : r ∈ extensions β n) : descWord g r.val ∈ D :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)
  have hv : v ∈ extensions α n := (mem_extensions v).mpr he
  have hl : l ≠ [] := by
    intro hn
    obtain ⟨x⟩ := ‹Nonempty α›
    have hx := (he.2.1 x).mpr (Set.mem_univ _)
    simp [hn] at hx
  have hn : d.length + 1 = n := by
    have hlen := List.length_pos_iff.mpr hl
    dsimp [d,n]
    rw [length_descWord]
    omega
  have eq := equal_exact_counts f g h n D hP hQ d (hP v hv) hn
  have pos : 0 < exactCount f n d := Finset.card_pos.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  rw [eq] at pos
  obtain ⟨r,hr⟩ := Finset.card_pos.mp pos
  obtain ⟨hx,hd⟩ := Finset.mem_filter.mp hr
  exact ⟨r.val,(mem_extensions r).mp hx,Prod.ext r.2.symm hd.symm⟩

private theorem empty_coefficient {α : Type*} [Fintype α] [PartialOrder α] [IsEmpty α] (f : α → ℕ) :
    monomialCoefficient f [] = 1 := by
  classical
  let c : Colorings f [] := ⟨fun _ => 0, fun {x} => isEmptyElim x, by simp⟩
  let _ : Subsingleton (Colorings f []) := ⟨fun a b => Subtype.ext (funext fun x => isEmptyElim x)⟩
  let _ : Unique (Colorings f []) := uniqueOfSubsingleton c
  exact Nat.card_unique

private theorem nonempty_coefficient {α : Type*} [Fintype α] [PartialOrder α] [Nonempty α] (f : α → ℕ) :
    monomialCoefficient f [] = 0 := by
  have empty : IsEmpty (Colorings f []) := ⟨fun c => by
    have h := c.2.2.length_eq
    simp at h⟩
  simp [monomialCoefficient]

private theorem nonempty_of_equal_enumerators {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : Nonempty β := by
  by_contra hn
  have _ := not_nonempty_iff.mp hn
  have hc := congrFun h []
  rw [nonempty_coefficient,empty_coefficient] at hc
  contradiction

private theorem empty_support {α : Type*} [PartialOrder α] [IsEmpty α] (f : α → ℕ) :
    fundamentalSupport f = {(0,[])} := by
  ext c
  constructor
  · rintro ⟨_ | ⟨x,l⟩,he,rfl⟩
    · rfl
    · exact isEmptyElim x
  · rintro rfl
    exact ⟨[],⟨by simp,fun x => isEmptyElim x,by simp⟩,rfl⟩

/-- Equality of the actual monomial coefficients of the partition enumerators
recovers their fundamental supports, including the degree of each descent word. -/
theorem support_of_equal_enumerators {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : fundamentalSupport f = fundamentalSupport g := by
  by_cases ha : Nonempty α
  · have _ := nonempty_of_equal_enumerators f g h
    exact Set.Subset.antisymm (subset_of_equal_enumerators f g h) (subset_of_equal_enumerators g f h.symm)
  · have _ := not_nonempty_iff.mp ha
    have hb : ¬ Nonempty β := fun _ => ha (nonempty_of_equal_enumerators g f h.symm)
    have _ := not_nonempty_iff.mp hb
    exact (empty_support f).trans (empty_support g).symm

/-- McNamara and Ward's equal-height question with height in vertices. -/
theorem equal_enumerators_height {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β] (f : α ↪ ℕ) (g : β ↪ ℕ)
    (h : monomialCoefficient f = monomialCoefficient g) : height α = height β := by
  have hs := support_of_equal_enumerators f g h
  exact le_antisymm (height_antitone g f hs.ge) (height_antitone f g hs.le)

end ChainWords
