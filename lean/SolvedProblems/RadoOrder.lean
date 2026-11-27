module

public import SolvedProblems.RadoModel

public section

namespace RadoSelection

/-- Compare two incidence words on the finite sample at their first difference. -/
private def EarlierBit {A : Type u} (r : A → A → Prop) (s : Sample A)
    (p q : A → Prop) : Prop :=
  ∃ t ∈ s, ¬ p t ∧ q t ∧ ∀ z ∈ s, r z t → (p z ↔ q z)

private theorem earliest {A : Type u} [∀ p : Prop, Decidable p]
    {D : A → Prop} {r : A → A → Prop} (o : StrictOn D r)
    (s : Sample A) (p : A → Prop) (hp : ∀ x, p x → D x)
    (hne : ∃ x ∈ s, p x) :
    ∃ t ∈ s, p t ∧ ∀ z ∈ s, p z → ¬ r z t := by
  induction s using Sample.induction with
  | empty => obtain ⟨_, h, _⟩ := hne; exact False.elim (List.not_mem_nil h)
  | step a s ih =>
    by_cases hex : ∃ x ∈ s, p x
    · obtain ⟨t, ht, hpt, hmin⟩ := ih hex
      by_cases hnew : p a ∧ r a t
      · refine ⟨a, Or.inl rfl, hnew.1, ?_⟩
        intro z hz hpz hza
        rcases Sample.mem_adjoin.mp hz with rfl | hzs
        · exact o.irrefl _ (hp _ hpz) hza
        · exact hmin z hzs hpz (o.trans (hp _ hpz) (hp _ hnew.1) (hp _ hpt) hza hnew.2)
      · refine ⟨t, Or.inr ht, hpt, ?_⟩
        intro z hz hpz hzt
        rcases Sample.mem_adjoin.mp hz with rfl | hzs
        · exact hnew ⟨hpz, hzt⟩
        · exact hmin z hzs hpz hzt
    · obtain ⟨t, ht, hpt⟩ := hne
      rcases Sample.mem_adjoin.mp ht with rfl | hts
      · refine ⟨t, Or.inl rfl, hpt, ?_⟩
        intro z hz hpz hzt
        rcases Sample.mem_adjoin.mp hz with rfl | hzs
        · exact o.irrefl _ (hp _ hpz) hzt
        · exact hex ⟨z, hzs, hpz⟩
      · exact False.elim (hex ⟨t, hts, hpt⟩)

/-- Incidence words which differ on the sample compare in one direction. -/
private theorem bit_compare {A : Type u} [∀ p : Prop, Decidable p]
    {D : A → Prop} {r : A → A → Prop} (o : StrictOn D r)
    {p q : A → Prop} {s : Sample A}
    (hd : ∀ x, ¬ (p x ↔ q x) → D x) (hne : ∃ x ∈ s, ¬ (p x ↔ q x)) :
    EarlierBit r s p q ∨ EarlierBit r s q p := by
  obtain ⟨t, ht, hdiff, hmin⟩ := earliest o s (fun x => ¬ (p x ↔ q x)) hd hne
  have before : ∀ z ∈ s, r z t → (p z ↔ q z) := by
    intro z hz hzt
    apply Decidable.byContradiction
    intro hn
    exact hmin z hz hn hzt
  by_cases hp : p t
  · right
    refine ⟨t, ht, ?_, hp, fun z hz hzt => (before z hz hzt).symm⟩
    exact fun hq => hdiff ⟨fun _ => hq, fun _ => hp⟩
  · left
    refine ⟨t, ht, hp, ?_, before⟩
    apply Decidable.byContradiction
    intro hq
    exact hdiff ⟨fun h => (hp h).elim, fun h => (hq h).elim⟩

private theorem bit_trans {A : Type u} [∀ p : Prop, Decidable p]
    {D : A → Prop} {r : A → A → Prop} (o : StrictOn D r)
    {p q v : A → Prop} {s : Sample A}
    (hp : ∀ x, p x → D x) (hq : ∀ x, q x → D x) (hv : ∀ x, v x → D x)
    (h₁ : EarlierBit r s p q) (h₂ : EarlierBit r s q v) : EarlierBit r s p v := by
  obtain ⟨a, ha, hpa, hqa, ab⟩ := h₁
  obtain ⟨b, hb, hqb, hvb, bb⟩ := h₂
  have hne : a ≠ b := fun h => hqb (h ▸ hqa)
  rcases o.compare (hq a hqa) (hv b hvb) hne with hab | hba
  · refine ⟨a, ha, hpa, (bb a ha hab).mp hqa, ?_⟩
    intro z hz hza
    by_cases hzd : D z
    · exact (ab z hz hza).trans (bb z hz (o.trans hzd (hq a hqa) (hv b hvb) hza hab))
    · exact ⟨fun hpz => (hzd (hq _ ((ab z hz hza).mp hpz))).elim,
        fun hvz => (hzd (hv _ hvz)).elim⟩
  · refine ⟨b, hb, fun hpb => hqb ((ab b hb hba).mp hpb), hvb, ?_⟩
    intro z hz hzb
    by_cases hzd : D z
    · exact (ab z hz (o.trans hzd (hv b hvb) (hq a hqa) hzb hba)).trans (bb z hz hzb)
    · exact ⟨fun hpz => (hzd (hp _ hpz)).elim, fun hvz => (hzd (hv _ hvz)).elim⟩

/-- Put the previously constructed layer orders end to end, below the current rank. -/
private def below {A : Type u} {I : Type v} [LT I] (H : Hierarchy A I) (i : I)
    (rec : ∀ j, j < i → A → A → Prop) (x y : A) : Prop :=
  H.rank x < H.rank y ∨ ∃ hx : H.rank x < i, H.rank x = H.rank y ∧ rec (H.rank x) hx x y

private theorem below_strict {A : Type u} {I : Type v} [LinearOrder I]
    (H : Hierarchy A I) (i : I) (rec : ∀ j, j < i → A → A → Prop)
    (hrec : ∀ j h, StrictOn (fun x => H.rank x = j) (rec j h)) :
    StrictOn (fun x => H.rank x < i) (below H i rec) := by
  constructor
  · rintro x _ (h | ⟨hx, _, h⟩)
    · exact lt_irrefl _ h
    · exact (hrec _ hx).irrefl x rfl h
  · rintro x y z hx _ _ (hxy | ⟨_, exy, hxy⟩) (hyz | ⟨_, eyz, hyz⟩)
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl (eyz ▸ hxy)
    · exact Or.inl (exy ▸ hyz)
    · refine Or.inr ⟨hx, exy.trans eyz, ?_⟩
      have hyz' : rec (H.rank x) hx y z := exy.symm.rec (motive := fun j _ => ∀ hj, rec j hj y z) (fun _ => hyz) hx
      exact (hrec _ hx).trans rfl exy.symm (exy.trans eyz).symm hxy hyz'
  · intro x y hx hy hn
    rcases lt_trichotomy (H.rank x) (H.rank y) with h | e | h
    · exact Or.inl (Or.inl h)
    · rcases (hrec _ hx).compare rfl e.symm hn with h | h
      · exact Or.inl (Or.inr ⟨hx, e, h⟩)
      · refine Or.inr (Or.inr ⟨hy, e.symm, ?_⟩)
        exact e.rec (motive := fun j _ => ∀ hj, rec j hj y x) (fun _ => h) hy
    · exact Or.inr (Or.inl h)

private def layer {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    (H : Hierarchy A I) (U : (Sample A → Prop) → Prop) (i : I) : A → A → Prop :=
  wellFounded_lt.fix (C := fun _ => A → A → Prop) (fun j rec x y =>
    U (fun s => EarlierBit (below H j rec) s (H.mem · x) (H.mem · y))) i

private theorem layer_eq {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    (H : Hierarchy A I) (U : (Sample A → Prop) → Prop) (i : I) (x y : A) :
    layer H U i x y ↔ U (fun s => EarlierBit
      (below H i (fun j _ => layer H U j)) s (H.mem · x) (H.mem · y)) := by
  unfold layer
  rw [WellFounded.fix_eq]

private theorem Fine.disj {A : Type u} {U : (Sample A → Prop) → Prop}
    (F : Fine U) {p q : Sample A → Prop} (h : U (fun s => p s ∨ q s)) : U p ∨ U q := by
  rcases F.decide p with yes | no
  · exact Or.inl yes
  · exact Or.inr (F.mono (fun _ h => h.1.resolve_left h.2) (F.inter h no))

private theorem layer_strict {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    [∀ p : Prop, Decidable p] (H : Hierarchy A I) {U : (Sample A → Prop) → Prop}
    (F : Fine U) (i : I) : StrictOn (fun x => H.rank x = i) (layer H U i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have o := below_strict H i (fun j _ => layer H U j) ih
    have mem_lower {x : A} (hx : H.rank x = i) (t : A) (h : H.mem t x) : H.rank t < i :=
      hx ▸ H.lower h
    constructor
    · intro x _ h
      have h' := (layer_eq H U i x x).mp h
      exact F.proper (F.mono (fun _ ⟨_, _, h₁, h₂, _⟩ => h₁ h₂) h')
    · intro x y z hx hy hz hxy hyz
      apply (layer_eq H U i x z).mpr
      exact F.mono (fun _ h => bit_trans o (mem_lower hx) (mem_lower hy) (mem_lower hz) h.1 h.2)
        (F.inter ((layer_eq H U i x y).mp hxy) ((layer_eq H U i y z).mp hyz))
    · intro x y hx hy hn
      have witness : ∃ t, ¬ (H.mem t x ↔ H.mem t y) := by
        apply Decidable.byContradiction
        intro h
        apply hn
        apply H.ext
        intro t
        apply Decidable.byContradiction
        intro h'
        exact h ⟨t, h'⟩
      obtain ⟨t, ht⟩ := witness
      have hdiff (z : A) (hz : ¬ (H.mem z x ↔ H.mem z y)) : H.rank z < i := by
        by_cases hh : H.mem z x
        · exact mem_lower hx z hh
        · by_cases hh' : H.mem z y
          · exact mem_lower hy z hh'
          · exact (hz ⟨fun h => (hh h).elim, fun h => (hh' h).elim⟩).elim
      have h := F.disj (F.mono (fun s hs => bit_compare o hdiff ⟨t, hs, ht⟩) (F.cone t))
      exact h.imp (layer_eq H U i x y).mpr (layer_eq H U i y x).mpr

/-- A single fine ultrafilter on unordered finite subsets orders a pure transitive
membership hierarchy. The relation is defined by recursion on its given well-founded
ranks. The only logical input is decidability of propositions (classical logic). -/
theorem order_from_fine {A : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    [∀ p : Prop, Decidable p] (H : Hierarchy A I) {U : (Sample A → Prop) → Prop}
    (F : Fine U) : ∃ r : A → A → Prop, StrictOn (fun _ => True) r := by
  let r := fun x y => H.rank x < H.rank y ∨
    (H.rank x = H.rank y ∧ layer H U (H.rank x) x y)
  refine ⟨r, ?_, ?_, ?_⟩
  · rintro x _ (h | ⟨_, h⟩)
    · exact lt_irrefl _ h
    · exact (layer_strict H F _).irrefl x rfl h
  · rintro x y z _ _ _ (hxy | ⟨exy, hxy⟩) (hyz | ⟨eyz, hyz⟩)
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl (eyz ▸ hxy)
    · exact Or.inl (exy ▸ hyz)
    · refine Or.inr ⟨exy.trans eyz, ?_⟩
      have hyz' : layer H U (H.rank x) y z := exy ▸ hyz
      exact (layer_strict H F _).trans rfl exy.symm (exy.trans eyz).symm hxy hyz'
  · intro x y _ _ hn
    rcases lt_trichotomy (H.rank x) (H.rank y) with h | e | h
    · exact Or.inl (Or.inl h)
    · rcases (layer_strict H F _).compare rfl e.symm hn with h | h
      · exact Or.inl (Or.inr ⟨e, h⟩)
      · exact Or.inr (Or.inr ⟨e.symm, e ▸ h⟩)
    · exact Or.inr (Or.inl h)

end RadoSelection
