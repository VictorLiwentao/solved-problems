module

public import SolvedProblems.PackingCutoffModel

public section

namespace PackingCutoff

private def key (d : Nat) {n} (p : Pos n) := label d p.1.val p.2

private theorem translated {d i n} {a : Pos n} (ha : i ≤ a.1.val) :
    label d (a.1.val-i) a.2 + 3*i = key d a := by
  obtain ⟨a,l⟩ := a
  change i ≤ a.val at ha
  cases l <;> simp [key,label] <;> omega

private theorem windowOrder {d i n} {a b : Pos n} (ha : i ≤ a.1.val) (hb : i ≤ b.1.val) :
    key d a < key d b ↔ label d (a.1.val-i) a.2 < label d (b.1.val-i) b.2 := by
  have := translated (d:=d) ha
  have := translated (d:=d) hb
  omega

private theorem key_inj (d : Nat) {n} {a b : Pos n} (eq : key d a = key d b) : a = b := by
  obtain ⟨⟨a, ha⟩, la⟩ := a
  obtain ⟨⟨b, hb⟩, lb⟩ := b
  cases la <;> cases lb <;> simp [key,label] at eq ⊢ <;> omega

private theorem byKey {α : Type} (f : α → Nat) (inj : ∀ {a b}, f a = f b → a = b) :
    linear (fun a b => f a < f b) := by
  refine ⟨fun a => Nat.lt_irrefl _, fun a b c => Nat.lt_trans, ?_⟩
  intro a b ne
  have h : f a ≠ f b := fun e => ne (inj e)
  omega

private theorem canonical (w d t : Nat) :
    packs w d t (fun a b => key d a < key d b) :=
  ⟨byKey _ (key_inj d), fun _ _ _ _ ha _ hb _ => windowOrder ha hb⟩

private theorem localEdge {w d t} {r : Pos (w+t) → Pos (w+t) → Prop}
    (hr : packs w d t r) {a b : Pos (w+t)}
    (hab : a.1.val < b.1.val+w) (hba : b.1.val < a.1.val+w) (h : key d a < key d b) : r a b := by
  let i := min t (min a.1.val b.1.val)
  have ha := a.1.isLt
  have hb := b.1.isLt
  apply (hr.2 i (by dsimp [i]; omega) a b (by dsimp [i]; omega)
    (by dsimp [i]; omega) (by dsimp [i]; omega) (by dsimp [i]; omega)).2
  exact (windowOrder (by dsimp [i]; omega) (by dsimp [i]; omega)).1 h

private theorem forced {w d t} (width : d+2 ≤ w) (short : w+t ≤ 2*d+1)
    {r : Pos (w+t) → Pos (w+t) → Prop} (hr : packs w d t r)
    (a b : Pos (w+t)) (h : key d a < key d b) : r a b := by
  by_cases close₁ : a.1.val < b.1.val+w
  · by_cases close₂ : b.1.val < a.1.val+w
    · exact localEdge hr close₁ close₂ h
    · let c : Pos (w+t) := (⟨a.1.val+1, by have := b.1.isLt; omega⟩, a.2)
      have ac : key d a < key d c := by
        obtain ⟨a,l⟩ := a; cases l <;> simp [c,key,label] <;> omega
      have cb : key d c < key d b := by
        have bound := b.1.isLt
        obtain ⟨a,l⟩ := a; obtain ⟨b,k⟩ := b
        have gap : a.val+w ≤ b.val := Nat.le_of_not_gt close₂
        have endb := b.isLt
        cases l <;> cases k <;> simp [key,label,c] at h ⊢ <;> omega
      exact hr.1.2.1 a c b (localEdge hr (by simp [c]; omega) (by simp [c]; omega) ac)
        (forced width short hr c b cb)
  · let c : Pos (w+t) := (⟨a.1.val-d, by have := a.1.isLt; omega⟩,.y)
    have bounds : key d a < key d c ∧ key d c < key d b := by
      have bound := a.1.isLt
      obtain ⟨a,l⟩ := a; obtain ⟨b,k⟩ := b
      have gap : b.val+w ≤ a.val := Nat.le_of_not_gt close₁
      have enda := a.isLt
      cases l <;> cases k <;> simp [key,label,c] at h ⊢ <;> omega
    exact hr.1.2.1 a c b (forced width short hr a c bounds.1) (forced width short hr c b bounds.2)
termination_by key d b - key d a
decreasing_by
  · change key d b - key d c < key d b - key d a
    omega
  · change key d c - key d a < key d b - key d a
    omega
  · change key d b - key d c < key d b - key d a
    omega

private theorem uniqueEarly {w d t} (width : d+2 ≤ w) (short : w+t ≤ 2*d+1) :
    ∃ r, packs w d t r ∧ ∀ s, packs w d t s → s = r := by
  refine ⟨_, canonical w d t, ?_⟩
  intro r hr
  funext a b
  apply propext
  refine ⟨?_, forced width short hr a b⟩
  intro ab
  apply Classical.byContradiction
  intro h
  by_cases e : key d a = key d b
  · have := key_inj d e
    cases this
    exact hr.1.1 a ab
  · have ba := forced width short hr b a (show key d b < key d a by omega)
    exact hr.1.1 a (hr.1.2.1 a b a ab ba)

/-- Exchange two adjacent integer keys. -/
private def swap (k x : Nat) := if x = k then k+1 else if x = k+1 then k else x

private theorem swap_twice (k x : Nat) : swap k (swap k x) = x := by
  by_cases e : x = k
  · subst x; simp [swap]
  · by_cases f : x = k+1
    · subst x; simp [swap]
    · simp [swap,e,f]

private theorem swap_order {k x y : Nat} (a : ¬(x = k ∧ y = k+1))
    (b : ¬(y = k ∧ x = k+1)) : swap k x < swap k y ↔ x < y := by
  unfold swap
  split <;> (repeat' split) <;> omega

private def orderAt (d i : Nat) {n} (a b : Pos n) :=
  swap (3*(i+2*d)+2) (key d a) < swap (3*(i+2*d)+2) (key d b)

private theorem lowBlock {d i n} {a : Pos n} (h : key d a = 3*(i+2*d)+2) :
    a.1.val = i := by
  obtain ⟨a,l⟩ := a; cases l <;> simp [key,label] at h ⊢ <;> omega

private theorem highBlock {d i n} {a : Pos n} (h : key d a = 3*(i+2*d)+2+1) :
    a.1.val = i+2*d+1 := by
  obtain ⟨a,l⟩ := a; cases l <;> simp [key,label] at h ⊢ <;> omega

private theorem swapPacks {w d : Nat} (width : w ≤ 2*d+1) (t i : Nat) :
    packs w d t (orderAt d i) := by
  constructor
  · apply byKey (fun a => swap (3*(i+2*d)+2) (key d a))
    intro a b eq
    apply key_inj d
    have e := congrArg (swap (3*(i+2*d)+2)) eq
    simpa only [swap_twice] using e
  · intro j _ a b ha ha' hb hb'
    apply Iff.trans _ (windowOrder ha hb)
    apply swap_order
    · rintro ⟨hx,hy⟩
      have := lowBlock hx
      have := highBlock hy
      omega
    · rintro ⟨hx,hy⟩
      have := lowBlock hx
      have := highBlock hy
      omega

private theorem detect (d i j : Nat) {n} (hi : i+2*d+1 < n) :
    orderAt d j ((⟨i,by omega⟩,.z) : Pos n) ((⟨i+2*d+1,hi⟩,.x) : Pos n) ↔ i ≠ j := by
  change swap (3*(j+2*d)+2) (3*(i+2*d)+2) < swap _ (3*(i+2*d+1)) ↔ _
  rw [show 3*(i+2*d+1) = 3*(i+2*d)+2+1 by omega]
  by_cases eq : i = j
  · subst i; simp [swap]
  · exact ⟨fun _ => eq, fun _ => (swap_order (by omega) (by omega)).2 (by omega)⟩

private theorem many {w d} (width : w ≤ 2*d+1) : unbounded w d := by
  intro m
  let t := m+2*d+1
  refine ⟨t, fun i => orderAt d i.val, fun i => swapPacks width _ _, ?_⟩
  intro i j eq
  apply Fin.ext
  apply Classical.byContradiction
  intro ne
  have hi : i.val+2*d+1 < w+t := by have := i.isLt; dsimp [t]; omega
  have h := (detect d i.val j.val hi).2 ne
  change @orderAt d i.val (w+t) = @orderAt d j.val (w+t) at eq
  rw [← eq] at h
  exact (detect d i.val i.val hi).1 h rfl

private theorem two {w d t} (width : w ≤ 2*d+1) (long : 2*d+1 < w+t) :
    ∃ r s, packs w d t r ∧ packs w d t s ∧ r ≠ s := by
  refine ⟨(fun a b => key d a < key d b), orderAt d 0, canonical w d t, swapPacks width t 0, ?_⟩
  intro eq
  have hi : 0+2*d+1 < w+t := by omega
  let a : Pos (w+t) := (⟨0,by omega⟩,.z)
  let b : Pos (w+t) := (⟨0+2*d+1,hi⟩,.x)
  have ab : key d a < key d b := by simp [a,b,key,label]; omega
  have flipped : orderAt d 0 a b := by rw [← eq]; exact ab
  exact (detect d 0 0 hi).1 flipped rfl

/-- For every positive cutoff h, two patterns of the same length 3w and overlap 3(w−1)
have one packing for each of the first h window counts. At h+1 windows the first
has at least two packings and the second has exactly one. Both counts are unbounded. -/
theorem noUniversalCutoff (h : Nat) (positive : 0 < h) :
    ∃ w d e : Nat, 1 < w ∧ d ≠ e ∧
      (∀ t < h, one w d t ∧ one w e t) ∧
      (∃ r s, packs w d h r ∧ packs w d h s ∧ r ≠ s) ∧ one w e h ∧
      unbounded w d ∧ unbounded w e := by
  refine ⟨h+4, h+1, h+2, by omega, by omega, ?_, two (by omega) (by omega),
    uniqueEarly (by omega) (by omega), many (by omega), many (by omega)⟩
  intro t ht
  exact ⟨uniqueEarly (by omega) (by omega), uniqueEarly (by omega) (by omega)⟩

end PackingCutoff
