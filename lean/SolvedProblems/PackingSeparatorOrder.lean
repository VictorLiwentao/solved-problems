module

public import SolvedProblems.PackingSeparatorModel

public section

namespace PackingSeparator

private abbrev iter (f : Nat → Nat) (x n : Nat) : Nat := Nat.rec x (fun _ r => f r) n
private abbrev Mono (f : Nat → Nat) := ∀ ⦃i j⦄, i ≤ j → f i ≤ f j

private theorem adv_bound (k a z x n) : advance k a z x n ≤ k := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [advance]
    split <;> omega

private theorem adv_le {k a z x r} (hr : r < k) (n : Nat) :
    advance k a z x n ≤ r ↔ ∃ i < n, x ≤ a i ∧ z i ≤ r := by
  induction n with
  | zero => simp [advance, Nat.not_le_of_lt hr]
  | succ n ih =>
    simp only [advance]
    constructor
    · intro h
      by_cases hx : x ≤ a n
      · rw [ite_eq_left hx] at h
        by_cases low : z n ≤ r
        · exact ⟨n,by omega,hx,low⟩
        · obtain ⟨i,hi,u,v⟩ := ih.mp (by omega)
          exact ⟨i,by omega,u,v⟩
      · rw [ite_eq_right hx] at h
        obtain ⟨i,hi,u,v⟩ := ih.mp h
        exact ⟨i,by omega,u,v⟩
    · rintro ⟨i,hi,u,v⟩
      by_cases eq : i=n
      · subst i; rw [ite_eq_left u]; omega
      · have le := ih.mpr ⟨i,by omega,u,v⟩
        split <;> omega

private theorem adv_mem (k a z x n) :
    advance k a z x n ∈ k :: (List.range n).map z := by
  induction n with
  | zero => simp [advance]
  | succ n ih =>
    simp only [advance, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    have old : advance k a z x n ∈ k :: ((List.range n).map z ++ [z n]) := by
      simp at ih ⊢
      rcases ih with h|⟨a,b,c⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨a,b,c⟩)
    split
    · rcases Nat.le_total (advance k a z x n) (z n) with lo|lo
      · rw [Nat.min_eq_left lo]; exact old
      · rw [Nat.min_eq_right lo]; simp
    · exact old

private theorem adv_mono (k a z n) : Mono (fun x => advance k a z x n) := by
  intro x y le
  by_cases h : advance k a z y n < k
  · obtain ⟨i,hi,yi,zi⟩ := (adv_le h n).mp (Nat.le_refl _)
    exact (adv_le h n).mpr ⟨i,hi,Nat.le_trans le yi,zi⟩
  · exact Nat.le_trans (adv_bound k a z x n) (Nat.le_of_not_lt h)

private abbrev pref {k m} (p : Pattern k m) := p.rank
private abbrev suff {k m} (p : Pattern k m) := fun i => p.rank (k-m+i)
private abbrev F {k m} (p : Pattern k m) := fun x => advance k (suff p) (pref p) x m
private abbrev G {k m} (p : Pattern k m) := fun x => advance k (pref p) (suff p) x m

private theorem cancel {k m} {a z : Nat → Nat} (az : ∀ i < m, ∀ h < m, z i ≤ z h → a i ≤ a h)
    (bound : ∀ i < m, z i < k) {x} (hx : x ≤ k) :
    x ≤ advance k z a (advance k a z x m) m := by
  let y := advance k z a (advance k a z x m) m
  change x ≤ y
  by_cases less : y < k
  · obtain ⟨i,hi,lo,hi'⟩ := (adv_le less m).mp (Nat.le_refl y)
    obtain ⟨h,hh,hx',hz⟩ := (adv_le (bound i hi) m).mp lo
    exact Nat.le_trans hx' (Nat.le_trans (az h hh i hi hz) hi')
  · omega

private theorem GF {k m} (p : Pattern k m) {x} (hx : x ≤ k) : x ≤ G p (F p x) :=
  cancel (fun i hi h hh => (p.agrees i hi h hh).mp) (fun i hi => p.bounded i (by have := p.short; omega)) hx

private theorem FG {k m} (p : Pattern k m) {x} (hx : x ≤ k) : x ≤ F p (G p x) :=
  cancel (fun i hi h hh => (p.agrees i hi h hh).mpr) (fun i hi => p.bounded (k-m+i) (by have := p.short; omega)) hx

private theorem iter_bound {f : Nat → Nat} {k x} (h : ∀ i, f i ≤ k) (hx : x ≤ k) (n) :
    iter f x n ≤ k := by cases n with
  | zero => exact hx
  | succ n => exact h _

private def distanceRank {k m} (p : Pattern k m) (w r v : Nat) :=
  if w ≤ v then iter (F p) r (v-w) else iter (G p) r (w-v)

private theorem d_right {k m} (p : Pattern k m) (w r v) (hr : r < k) :
    distanceRank p w r (v+1) ≤ F p (distanceRank p w r v) := by
  unfold distanceRank
  by_cases h : w ≤ v
  · rw [ite_eq_left h, ite_eq_left (by omega : w ≤ v+1),show v+1-w=(v-w)+1 by omega]
    exact Nat.le_refl _
  · rw [ite_eq_right h]
    by_cases e : w = v+1
    · subst w; simp only [Nat.le_refl, ite_true, Nat.sub_self, Nat.add_sub_cancel_left]
      exact FG p (Nat.le_of_lt hr)
    · rw [ite_eq_right (by omega : ¬ w ≤ v+1),show w-v = (w-(v+1))+1 by omega]
      exact FG p (iter_bound (fun i => adv_bound _ _ _ _ _) (Nat.le_of_lt hr) _)

private theorem d_left {k m} (p : Pattern k m) (w r v) (hr : r < k) :
    distanceRank p w r v ≤ G p (distanceRank p w r (v+1)) := by
  unfold distanceRank
  by_cases h : w ≤ v
  · rw [ite_eq_left h,ite_eq_left (by omega : w ≤ v+1),show v+1-w=(v-w)+1 by omega]
    exact GF p (iter_bound (fun i => adv_bound _ _ _ _ _) (Nat.le_of_lt hr) _)
  · rw [ite_eq_right h]
    by_cases e : w = v+1
    · subst w; simp only [Nat.le_refl, ite_true, Nat.sub_self, Nat.add_sub_cancel_left]; exact Nat.le_refl _
    · rw [ite_eq_right (by omega : ¬ w ≤ v+1),show w-v = (w-(v+1))+1 by omega]
      exact Nat.le_refl _

private theorem sound {k m j w r v s} {p : Pattern k m} (hr : r < k)
    (path : Below p j w r v s) : distanceRank p w r v ≤ s := by
  induction path with
  | refl => simp only [distanceRank, Nat.le_refl, ite_true, Nat.sub_self]; exact Nat.le_refl _
  | rise _ le _ ih => exact Nat.le_trans ih le
  | @right v i _ hi _ ih =>
    exact Nat.le_trans (d_right p w r v hr) ((adv_le (p.bounded i (by have := p.short; omega)) m).mpr
      ⟨i,hi,ih,Nat.le_refl _⟩)
  | @left v i _ hi ih =>
    exact Nat.le_trans (d_left p w r v hr) ((adv_le (p.bounded (k-m+i) (by have := p.short; omega)) m).mpr
      ⟨i,hi,ih,Nat.le_refl _⟩)

private theorem completeR {k m j w r} (p : Pattern k m) (d : Nat) {s}
    (valid : w+d < j) (hs : s < k) (h : iter (F p) r d ≤ s) : Below p j w r (w+d) s := by
  induction d generalizing s with
  | zero => exact Below.rise .refl h hs
  | succ d ih =>
    obtain ⟨i,hi,source,target⟩ := (adv_le hs m).mp h
    have ok : suff p i < k := p.bounded _ (by have := p.short; omega)
    exact Below.rise (Below.right (ih (by omega) ok source) hi valid) target hs

private theorem completeL {k m j w r} (p : Pattern k m) (d : Nat) {s}
    (valid : d ≤ w) (hs : s < k) (h : iter (G p) r d ≤ s) : Below p j w r (w-d) s := by
  induction d generalizing s with
  | zero => exact Below.rise .refl h hs
  | succ d ih =>
    obtain ⟨i,hi,source,target⟩ := (adv_le hs m).mp h
    have ok : pref p i < k := p.bounded _ (by have := p.short; omega)
    have path := ih (by omega) ok source
    rw [show w-d=(w-(d+1))+1 by omega] at path
    exact Below.rise (Below.left path hi) target hs

private theorem compareIff {k m j} (p : Pattern k m) (x y : Mark k j) :
    LEPos p x y ↔ distanceRank p x.1.val x.2.val y.1.val ≤ y.2.val := by
  constructor
  · exact sound x.2.isLt
  · unfold distanceRank
    split
    next hw =>
      intro h
      have path := completeR (w := x.1.val) (j := j) p (y.1.val-x.1.val) (by have := y.1.isLt; omega) y.2.isLt h
      simpa [LEPos, show x.1.val + (y.1.val-x.1.val) = y.1.val by omega] using path
    next hw =>
      intro h
      have path := completeL (w := x.1.val) (j := j) p (x.1.val-y.1.val) (by omega) y.2.isLt h
      simpa [LEPos, show x.1.val - (x.1.val-y.1.val) = y.1.val by omega] using path


private theorem along {u : Nat → Nat} (step : ∀ n, u n ≤ u (n+1)) {i j : Nat}
    (h : i ≤ j) : u i ≤ u j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (step _)

private theorem alongRev {u : Nat → Nat} (step : ∀ n, u (n+1) ≤ u n) {i j : Nat}
    (h : i ≤ j) : u j ≤ u i := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans (step _) ih

private theorem iterPlateau (f : Nat → Nat) (mono : Mono f) (x : Nat) {i j : Nat}
    (lt : i < j) (eq : iter f x i = iter f x j) : iter f x (i+1) = iter f x i := by
  rcases Nat.le_total x (f x) with up|down
  · have step : ∀ n, iter f x n ≤ iter f x (n+1) := by
      intro n
      induction n with
      | zero => exact up
      | succ n ih => exact mono ih
    exact Nat.le_antisymm (eq.symm ▸ along (u := iter f x) step lt) (step i)
  · have step : ∀ n, iter f x (n+1) ≤ iter f x n := by
      intro n
      induction n with
      | zero => exact down
      | succ n ih => exact mono ih
    exact Nat.le_antisymm (step i) (eq ▸ alongRev (u := iter f x) step lt)

private theorem persist (f : Nat → Nat) (x : Nat) {i j : Nat} (h : i ≤ j)
    (fixed : iter f x (i+1) = iter f x i) : iter f x (j+1) = iter f x j := by
  induction h with
  | refl => exact fixed
  | step _ ih => exact congrArg f ih

private theorem clip (k a z x m d) :
    let f := fun y => advance k a z y m
    iter f x d = iter f x (min (m+1) d) := by
  let f := fun y => advance k a z y m
  change iter f x d = iter f x (min (m+1) d)
  have fixed : iter f x (m+1+1) = iter f x (m+1) := by
    apply Classical.byContradiction
    intro no
    let orbit := (List.range (m+2)).map (fun i => iter f x (i+1))
    let choices := k :: (List.range m).map z
    have subset : orbit ⊆ choices := by
      intro v hv
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
      exact adv_mem _ _ _ _ _
    have collapse {i j : Nat} (lt : i<j) (bound : j<m+2)
        (eq : iter f x (i+1) = iter f x (j+1)) : False :=
      no (persist f x (by omega : i+1 ≤ m+1)
        (iterPlateau f (adv_mono _ _ _ _) x (by omega) eq))
    have nodup : orbit.Nodup := by
      apply List.nodup_iff_eq_of_getElem_eq.mpr
      intro i j hi hj eq
      simp [orbit] at hi hj eq
      rcases Nat.lt_trichotomy i j with h|h|h
      · exact False.elim (collapse h hj eq)
      · exact h
      · exact False.elim (collapse h hi eq.symm)
    have too := nodup.length_le_of_subset subset
    simp [orbit,choices] at too
  rcases Nat.le_total d (m+1) with le|le
  · rw [Nat.min_eq_right le]
  · rw [Nat.min_eq_left le]
    induction le with
    | refl => rfl
    | step h ih => exact (persist f x h fixed).trans ih

/-- The bounded numerical rank test decides the full generated comparison. -/
theorem rankTest_iff {k m j} (p : Pattern k m) (x y : Mark k j) :
    LEPos p x y ↔ RankTest p x y := by
  rw [compareIff]
  unfold distanceRank RankTest
  split
  next hw =>
    simp only [Nat.sub_eq_zero_of_le hw, Nat.add_zero]
    rw [clip]
  next hw =>
    simp only [Nat.sub_eq_zero_of_le (by omega : y.1.val ≤ x.1.val), Nat.zero_add]
    rw [clip]

theorem withinWindow {k m j} (p : Pattern k m) (w : Fin j) (r s : Fin k) :
    LEPos p (w,r) (w,s) ↔ r.val ≤ s.val := by
  rw [compareIff]
  simp only [distanceRank, Nat.le_refl, ite_true, Nat.sub_self]
  rfl

theorem firstToSecond {k m j} (p : Pattern k m) (h : 1 < j) (r s : Fin k) :
    LEPos p (⟨0,by omega⟩,r) (⟨1,h⟩,s) ↔
      ∃ i < m, r.val ≤ p.rank (k-m+i) ∧ p.rank i ≤ s.val := by
  rw [compareIff]
  exact adv_le s.isLt m

theorem secondToFirst {k m j} (p : Pattern k m) (h : 1 < j) (r s : Fin k) :
    LEPos p (⟨1,h⟩,r) (⟨0,by omega⟩,s) ↔
      ∃ i < m, r.val ≤ p.rank i ∧ p.rank (k-m+i) ≤ s.val := by
  rw [compareIff]
  exact adv_le s.isLt m

end PackingSeparator
