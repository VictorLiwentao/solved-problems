module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace PackingFactor

def shared (c : Nat → Fin 3) (w : List Nat) := w.filter (fun x => c x == 1)
def leftList (c : Nat → Fin 3) (w : List Nat) := w.filter (fun x => c x != 2)
def rightList (c : Nat → Fin 3) (w : List Nat) := w.filter (fun x => c x != 0)

/-- An exclusive letter lies after exactly g shared anchors. -/
def Occupied (c : Nat → Fin 3) (w : List Nat) (g : Nat) : Prop :=
  ∃ u x v, w = u ++ x::v ∧ c x ≠ 1 ∧ (shared c u).length = g

variable {c : Nat → Fin 3}

private theorem colors (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by fin_cases i <;> decide

/-- Lists on the two sides can always be interleaved if their shared anchors agree. -/
theorem merge_exists {l r : List Nat} (hl : ∀ x ∈ l, c x ≠ 2)
    (hr : ∀ x ∈ r, c x ≠ 0) (hs : shared c l = shared c r) :
    ∃ w, leftList c w=l ∧ rightList c w=r := by
  cases l with
  | nil =>
    refine ⟨r,?_,?_⟩
    · apply List.filter_eq_nil_iff.mpr
      intro x hx
      have h1 := (List.filter_eq_nil_iff.mp hs.symm) x hx
      rcases colors (c x) with h|h|h <;> simp_all
    · exact List.filter_eq_self.mpr (by simpa using hr)
  | cons a l =>
    cases r with
    | nil =>
      refine ⟨a::l, List.filter_eq_self.mpr (by simpa using hl),?_⟩
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have h2 := hl x hx
      have h1 := (List.filter_eq_nil_iff.mp hs) x hx
      rcases colors (c x) with h|h|h <;> simp_all
    | cons b r =>
      have hl' : ∀ x ∈ l, c x ≠ 2 := fun x hx => hl x (by simp [hx])
      have hr' : ∀ x ∈ r, c x ≠ 0 := fun x hx => hr x (by simp [hx])
      rcases colors (c a) with ha|ha|ha
      · have hs' : shared c l = shared c (b::r) := by simpa [shared,ha] using hs
        obtain ⟨w,hw,hw'⟩ := merge_exists hl' hr hs'
        exact ⟨a::w, by simpa [leftList,ha] using hw, by simpa [rightList,ha] using hw'⟩
      · rcases colors (c b) with hb|hb|hb
        · exact False.elim (hr b List.mem_cons_self hb)
        · have hpair : a = b ∧ shared c l = shared c r := by simpa [shared,ha,hb] using hs
          obtain ⟨w,hw,hw'⟩ := merge_exists hl' hr' hpair.2
          exact ⟨a::w,by simpa [leftList,ha] using hw,by simpa [rightList,ha,hpair.1,hb] using hw'⟩
        · have hs' : shared c (a::l) = shared c r := by simpa [shared,hb] using hs
          obtain ⟨w,hw,hw'⟩ := merge_exists hl hr' hs'
          exact ⟨b::w,by simpa [leftList,hb] using hw,by simpa [rightList,hb] using hw'⟩
      · exact False.elim (hl a List.mem_cons_self ha)
termination_by l.length + r.length

private theorem occupied_head {x w} (hx : c x ≠ 1) : Occupied c (x::w) 0 :=
  ⟨[], x, w, rfl, hx, rfl⟩

private theorem occupied_cons {x w g} (h : Occupied c w g) :
    Occupied c (x::w) (if c x=1 then g+1 else g) := by
  obtain ⟨u,y,v,rfl,hy,hg⟩ := h
  refine ⟨x::u,y,v,rfl,hy,?_⟩
  by_cases hx : c x=1 <;> simp [shared,hx,shared] at hg ⊢ <;> omega

/-- With both projections fixed, a first difference between two orders must exchange
a left-only and a right-only letter within the same anchor gap. -/
private theorem distinguish {w z : List Nat} (hl : leftList c w = leftList c z)
    (hr : rightList c w = rightList c z) (hne : w ≠ z) :
    ∃ g, Occupied c (leftList c w) g ∧ Occupied c (rightList c w) g := by
  induction w generalizing z with
  | nil =>
    cases z with
    | nil => contradiction
    | cons b z => rcases colors (c b) with h|h|h <;> simp [leftList,rightList,h] at hl hr
  | cons a w ih =>
    cases z with
    | nil => rcases colors (c a) with h|h|h <;> simp [leftList,rightList,h] at hl hr
    | cons b z =>
      by_cases eq : a=b
      · subst b
        have tailL : leftList c w = leftList c z := by
          rcases colors (c a) with h|h|h <;> simpa [leftList,h] using hl
        have tailR : rightList c w = rightList c z := by
          rcases colors (c a) with h|h|h <;> simpa [rightList,h] using hr
        obtain ⟨g,lg,rg⟩ := ih tailL tailR (by simpa using hne)
        rcases colors (c a) with h|h|h
        · exact ⟨g, by simpa [leftList,h] using (occupied_cons (x:=a) lg), by simpa [rightList,h] using rg⟩
        · exact ⟨g+1, by simpa [leftList,h] using (occupied_cons (x:=a) lg),
            by simpa [rightList,h] using (occupied_cons (x:=a) rg)⟩
        · exact ⟨g, by simpa [leftList,h] using lg, by simpa [rightList,h] using (occupied_cons (x:=a) rg)⟩
      · rcases colors (c a) with h|h|h <;> rcases colors (c b) with f|f|f
        all_goals try solve | simp [leftList,rightList,h,f,eq] at hl hr
        · refine ⟨0,?_,?_⟩
          · simp [leftList,h]; exact occupied_head (by simp [h])
          · rw [hr]; simp [rightList,f]; exact occupied_head (by simp [f])
        · refine ⟨0,?_,?_⟩
          · rw [hl]; simp [leftList,f]; exact occupied_head (by simp [f])
          · simp [rightList,h]; exact occupied_head (by simp [h])

/-- A common occupied gap permits both relative orders of a pair of exclusive letters. -/
private theorem ambiguous {l r : List Nat} (hl : ∀ x ∈ l, c x ≠ 2)
    (hr : ∀ x ∈ r, c x ≠ 0) (hs : shared c l = shared c r)
    {g : Nat} (lg : Occupied c l g) (rg : Occupied c r g) :
    ∃ w z, w ≠ z ∧ leftList c w = l ∧ rightList c w = r ∧ leftList c z = l ∧ rightList c z = r := by
  obtain ⟨u,x,v,rfl,hx,len₁⟩ := lg
  obtain ⟨a,y,b,rfl,hy,len₂⟩ := rg
  have x0 : c x=0 := by rcases colors (c x) with h|h|h <;> simp_all
  have y2 : c y=2 := by rcases colors (c y) with h|h|h <;> simp_all
  have hs' : shared c u ++ shared c v = shared c a ++ shared c b := by simpa [shared,x0,y2] using hs
  have hpre := congrArg (List.take g) hs'
  rw [List.take_left' len₁,List.take_left' len₂] at hpre
  have hpost : shared c v = shared c b := by simpa [hpre] using hs'
  obtain ⟨pre, lp,rp⟩ := merge_exists (l:=u) (r:=a) (fun t h => hl t (by simp [h])) (fun t h => hr t (by simp [h])) hpre
  obtain ⟨post, ls,rs⟩ := merge_exists (l:=v) (r:=b) (fun t h => hl t (by simp [h])) (fun t h => hr t (by simp [h])) hpost
  have xy : x ≠ y := fun e => by subst y; simp_all
  refine ⟨pre++x::y::post,pre++y::x::post,?_,?_,?_,?_,?_⟩
  · simp [xy]
  all_goals simpa [leftList,rightList,x0,y2] using (by first | exact congrArg₂ List.append lp (congrArg (List.cons x) ls) | exact congrArg₂ List.append rp (congrArg (List.cons y) rs))

/-- Restriction onto the two sides is surjective. It is bijective exactly when
no gap can hold exclusive letters from both sides. -/
theorem merge_count {c : Nat → Fin 3} (L R G : Finset (List Nat))
    (hl : ∀ l ∈ L, ∀ x ∈ l, c x ≠ 2) (hr : ∀ r ∈ R, ∀ x ∈ r, c x ≠ 0)
    (hs : ∀ l ∈ L, ∀ r ∈ R, shared c l = shared c r)
    (hg : ∀ w, w ∈ G ↔ leftList c w ∈ L ∧ rightList c w ∈ R) :
    L.card * R.card ≤ G.card ∧ (G.card = L.card * R.card ↔
      ∀ l ∈ L, ∀ r ∈ R, ∀ g, ¬ (Occupied c l g ∧ Occupied c r g)) := by
  classical
  let f (w : G) : L × R :=
    (⟨leftList c w.val, ((hg _).mp w.property).1⟩, ⟨rightList c w.val, ((hg _).mp w.property).2⟩)
  have onto : Function.Surjective f := by
    rintro ⟨l,r⟩
    obtain ⟨w,lw,rw⟩ := merge_exists (hl _ l.property) (hr _ r.property) (hs _ l.property _ r.property)
    exact ⟨⟨w,(hg _).mpr (by simpa [lw,rw] using And.intro l.property r.property)⟩,
      Prod.ext (Subtype.ext lw) (Subtype.ext rw)⟩
  refine ⟨by simpa using Fintype.card_le_of_surjective f onto, ?_⟩
  constructor
  · intro heq l lm r rm g overlap
    have card : Fintype.card G = Fintype.card (L × R) := by simpa using heq
    have inject := (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq card) (f := f)).mpr onto
    obtain ⟨w,z,ne,wl,wr,zl,zr⟩ := ambiguous (hl l lm) (hr r rm) (hs l lm r rm) overlap.1 overlap.2
    let pw : G := ⟨w, (hg w).mpr (by simpa [wl,wr] using And.intro lm rm)⟩
    let pz : G := ⟨z, (hg z).mpr (by simpa [zl,zr] using And.intro lm rm)⟩
    have same : f pw = f pz := Prod.ext (Subtype.ext (wl.trans zl.symm)) (Subtype.ext (wr.trans zr.symm))
    exact ne (congrArg Subtype.val (inject same))
  · intro separate
    have inject : Function.Injective f := by
      intro w z eq
      apply Subtype.ext
      by_contra ne
      have l := congrArg (fun p : L × R => p.1.val) eq
      have r := congrArg (fun p : L × R => p.2.val) eq
      obtain ⟨g,lw,rw⟩ := distinguish (c:=c) (w:=w.val) (z:=z.val) l r ne
      exact separate _ (f w).1.property _ (f w).2.property g ⟨lw,rw⟩
    simpa using Fintype.card_congr (Equiv.ofBijective f ⟨inject,onto⟩)

end PackingFactor
