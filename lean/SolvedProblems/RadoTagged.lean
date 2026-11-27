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

/-- A membership system with a linear order of tags at each rank. Equal-tag
objects are determined by their members. Distinct atoms may have distinct tags. -/
structure Tagged (A : Type u) (I : Type v) [LT I] (K : Type w) where
  rank : A → I
  mem : A → A → Prop
  lower : ∀ {t x}, mem t x → rank t < rank x
  tag : A → K
  ext : ∀ {x y}, tag x = tag y → (∀ t, mem t x ↔ mem t y) → x = y

/-- Compare keys first, then compare inside a single key. -/
private def byKey {A : Type u} {K : Type w} (key : A → K) (r : K → K → Prop)
    (s : A → A → Prop) (x y : A) : Prop := r (key x) (key y) ∨ (key x = key y ∧ s x y)

private theorem byKey_strict {A : Type u} {K : Type w} [∀ p : Prop, Decidable p]
    (D : A → Prop) (key : A → K) {r : K → K → Prop} (rk : StrictOn (fun _ => True) r)
    {s : A → A → Prop} (hs : ∀ k, StrictOn (fun x => D x ∧ key x = k) s) :
    StrictOn D (byKey key r s) := by
  constructor
  · rintro x hx (h | ⟨_,h⟩)
    · exact rk.irrefl _ trivial h
    · exact (hs _).irrefl x ⟨hx,rfl⟩ h
  · rintro x y z hx hy hz (hxy | ⟨exy,hxy⟩) (hyz | ⟨eyz,hyz⟩)
    · exact Or.inl (rk.trans trivial trivial trivial hxy hyz)
    · exact Or.inl (eyz ▸ hxy)
    · exact Or.inl (exy ▸ hyz)
    · exact Or.inr ⟨exy.trans eyz,
        (hs _).trans ⟨hx,rfl⟩ ⟨hy,exy.symm⟩ ⟨hz,(exy.trans eyz).symm⟩ hxy hyz⟩
  · intro x y hx hy hn
    by_cases e : key x = key y
    · rcases (hs _).compare ⟨hx,rfl⟩ ⟨hy,e.symm⟩ hn with h | h
      · exact Or.inl (Or.inr ⟨e,h⟩)
      · exact Or.inr (Or.inr ⟨e.symm,h⟩)
    · exact (rk.compare trivial trivial e).imp Or.inl Or.inl

/-- Stack the ordered rank layers belonging to the domain D. -/
private def stack {A : Type u} {I : Type v} [LT I] (rank : A → I) (D : I → Prop)
    (rec : ∀ j, D j → A → A → Prop) : A → A → Prop :=
  byKey rank (· < ·) (fun x y => ∃ h, rec (rank x) h x y)

private theorem stack_strict {A : Type u} {I : Type v} [LinearOrder I] [∀ p : Prop, Decidable p]
    (rank : A → I) (D : I → Prop) (rec : ∀ j, D j → A → A → Prop)
    (ok : ∀ j h, StrictOn (fun x => rank x = j) (rec j h)) :
    StrictOn (fun x => D (rank x)) (stack rank D rec) := by
  apply byKey_strict _ _ (r := (· < ·))
    ⟨fun _ _ => lt_irrefl _, fun _ _ _ => lt_trans, fun _ _ hn => lt_or_gt_of_ne hn⟩
  intro i
  constructor
  · rintro x ⟨hx,_⟩ ⟨_,h⟩
    exact (ok _ hx).irrefl x rfl h
  · rintro x y z ⟨hx,hxi⟩ ⟨hy,hyi⟩ ⟨_,hzi⟩ ⟨_,hxy⟩ ⟨_,hyz⟩
    have eq := hyi.trans hxi.symm
    have hyz' : rec (rank x) hx y z :=
      eq.rec (motive := fun j _ => ∀ hj, rec j hj y z) (fun _ => hyz) hx
    exact ⟨hx,(ok _ hx).trans rfl eq (hzi.trans hxi.symm) hxy hyz'⟩
  · rintro x y ⟨hx,hxi⟩ ⟨hy,hyi⟩ hn
    have eq := hxi.trans hyi.symm
    rcases (ok _ hx).compare rfl eq.symm hn with h | h
    · exact Or.inl ⟨hx,h⟩
    · exact Or.inr ⟨hy,eq.rec (motive := fun j _ => ∀ hj, rec j hj y x) (fun _ => h) hy⟩

private def layer {A : Type u} {I : Type v} {K : Type w} [LinearOrder I] [WellFoundedLT I]
    (H : Tagged A I K) (r : K → K → Prop) (U : (Sample A → Prop) → Prop) (i : I) : A → A → Prop :=
  wellFounded_lt.fix (C := fun _ => A → A → Prop) (fun j rec =>
    byKey H.tag r (fun x y => U (fun s => EarlierBit (stack H.rank (· < j) rec) s (H.mem · x) (H.mem · y)))) i

private theorem layer_eq {A : Type u} {I : Type v} {K : Type w} [LinearOrder I] [WellFoundedLT I]
    (H : Tagged A I K) (r : K → K → Prop) (U : (Sample A → Prop) → Prop) (i : I) :
    layer H r U i = byKey H.tag r (fun x y => U (fun s => EarlierBit
      (stack H.rank (· < i) (fun j _ => layer H r U j)) s (H.mem · x) (H.mem · y))) := by
  unfold layer
  rw [WellFounded.fix_eq]

private theorem Fine.disj {A : Type u} {U : (Sample A → Prop) → Prop}
    (F : Fine U) {p q : Sample A → Prop} (h : U (fun s => p s ∨ q s)) : U p ∨ U q := by
  rcases F.decide p with yes | no
  · exact Or.inl yes
  · exact Or.inr (F.mono (fun _ h => h.1.resolve_left h.2) (F.inter h no))

private theorem layer_strict {A : Type u} {I : Type v} {K : Type w} [LinearOrder I]
    [WellFoundedLT I] [∀ p : Prop, Decidable p] (H : Tagged A I K)
    {r : K → K → Prop} (rk : StrictOn (fun _ => True) r) {U : (Sample A → Prop) → Prop}
    (F : Fine U) (i : I) : StrictOn (fun x => H.rank x = i) (layer H r U i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have o := stack_strict H.rank (· < i) (fun j _ => layer H r U j) ih
    have mem_lower {x : A} (hx : H.rank x = i) (t : A) (h : H.mem t x) : H.rank t < i :=
      hx ▸ H.lower h
    rw [layer_eq]
    apply byKey_strict _ _ rk
    intro k
    constructor
    · intro x _ h
      exact F.proper (F.mono (fun _ ⟨_, _, h₁, h₂, _⟩ => h₁ h₂) h)
    · intro x y z hx hy hz hxy hyz
      exact F.mono (fun _ h => bit_trans o (mem_lower hx.1) (mem_lower hy.1) (mem_lower hz.1) h.1 h.2)
        (F.inter hxy hyz)
    · intro x y hx hy hn
      have witness : ∃ t, ¬ (H.mem t x ↔ H.mem t y) := by
        apply Decidable.byContradiction
        intro h
        apply hn
        apply H.ext (hx.2.trans hy.2.symm)
        intro t
        apply Decidable.byContradiction
        intro h'
        exact h ⟨t, h'⟩
      obtain ⟨t, ht⟩ := witness
      have hdiff (z : A) (hz : ¬ (H.mem z x ↔ H.mem z y)) : H.rank z < i := by
        by_cases hh : H.mem z x
        · exact mem_lower hx.1 z hh
        · by_cases hh' : H.mem z y
          · exact mem_lower hy.1 z hh'
          · exact (hz ⟨fun h => (hh h).elim, fun h => (hh' h).elim⟩).elim
      exact F.disj (F.mono (fun s hs => bit_compare o hdiff ⟨t, hs, ht⟩) (F.cone t))

/-- A fine ultrafilter orders a ranked hierarchy with a linearly ordered set of
tags distinguishing the objects left indistinguishable by membership. -/
theorem tagged_order {A : Type u} {I : Type v} {K : Type w} [LinearOrder I]
    [WellFoundedLT I] [∀ p : Prop, Decidable p] (H : Tagged A I K)
    {r : K → K → Prop} (rk : StrictOn (fun _ => True) r) {U : (Sample A → Prop) → Prop}
    (F : Fine U) : ∃ s : A → A → Prop, StrictOn (fun _ => True) s := by
  exact ⟨stack H.rank (fun _ => True) (fun j _ => layer H r U j),
    stack_strict H.rank (fun _ => True) _ (fun j _ => layer_strict H rk F j)⟩

end RadoSelection
