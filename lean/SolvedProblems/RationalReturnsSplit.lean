module

public import SolvedProblems.RationalReturnsModel
import Mathlib.Data.Finset.Interval

public section

namespace RationalReturns

theorem edge_strict {m n : ℕ} (hn : 0<n) (hm : n≤m) : StrictMono (edge m n) := by
  apply strictMono_nat_of_lt_succ
  intro i
  unfold edge
  rw [Nat.succ_mul]
  calc
    i*m/n < i*m/n+1 := Nat.lt_succ_self _
    _ = (i*m+n)/n := (Nat.add_div_right _ hn).symm
    _ ≤ (i*m+m)/n := Nat.div_le_div_right (by omega)

/-- Boundary contacts strictly between the two endpoints of a segment. -/
@[expose] noncomputable def contactRows {m n d k i j} (w : Segment m n d k i j) : Finset ℕ := by
  classical
  exact (Finset.Ioo i j).filter (fun a => ∃ r : Fin (j-i),
    i+r.val = a ∧ (w.val r).val = edge m n a)

private def atRow {m n d k i j} (w : Segment m n d k i j) (a : ℕ) : ℕ :=
  if h : a-i < j-i then (w.val ⟨a-i,h⟩).val else 0

private theorem at_idx {w : Segment m n d k i j} (r : Fin (j-i)) :
    atRow w (i+r.val) = (w.val r).val := by simp [atRow]

private theorem at_mem {w : Segment m n d k i j} {a} (hi : i ≤ a) (hj : a < j) :
    atRow w a < m := by
  simp only [atRow, dite_eq_left (show a-i<j-i by omega)]
  exact Fin.isLt _

private theorem at_valid {w : Segment m n d k i j} {a} (hi : i ≤ a) (hj : a < j) :
    edge m n i ≤ atRow w a ∧ atRow w a ≤ edge m n a ∧ atRow w a ≠ k*d := by
  let r : Fin (j-i) := ⟨a-i,by omega⟩
  have e : i+r.val=a := by dsimp [r]; omega
  rw [← e, at_idx]
  exact ⟨(w.property.2.1 r).1,(w.property.2.1 r).2,w.property.2.2.1 r⟩

private theorem at_mono {w : Segment m n d k i j} {a b}
    (hi : i≤a) (hab : a≤b) (hj : b<j) : atRow w a ≤ atRow w b := by
  simp only [atRow, dite_eq_left (show a-i<j-i by omega), dite_eq_left (show b-i<j-i by omega)]
  exact w.property.1 (show (⟨a-i,by omega⟩ : Fin (j-i)) ≤ ⟨b-i,by omega⟩ by
    exact Nat.sub_le_sub_right hab _)

private theorem at_required {w : Segment m n d k i j} {c} (lo : edge m n i ≤ c)
    (hi : c < edge m n j) (hc : required d k c) :
    ∃ a, i≤a ∧ a<j ∧ atRow w a = c := by
  obtain ⟨r,hr⟩ := w.property.2.2.2 _ lo hi hc
  exact ⟨i+r.val,by omega,by have := r.isLt; omega,(at_idx r).trans hr⟩

private theorem contacts_iff {w : Segment m n d k i j} {a} :
    a ∈ contactRows w ↔ i<a ∧ a<j ∧ atRow w a = edge m n a := by
  classical
  simp only [contactRows,Finset.mem_filter,Finset.mem_Ioo]
  constructor
  · rintro ⟨⟨h,h'⟩,r,e,he⟩
    exact ⟨h,h',e ▸ (at_idx r).trans (e.symm ▸ he)⟩
  · rintro ⟨lo,hi,he⟩
    let r : Fin (j-i) := ⟨a-i,by omega⟩
    have e : i+r.val = a := by dsimp [r]; omega
    exact ⟨⟨lo,hi⟩,r,e,(at_idx r).symm.trans (e.symm ▸ he)⟩

private def build {m n d k i j} (f : ℕ → ℕ)
    (hm : ∀ a, i≤a → a<j → f a<m)
    (mono : ∀ a b, i≤a → a≤b → b<j → f a≤f b)
    (bounds : ∀ a, i≤a → a<j → edge m n i≤f a ∧ f a≤edge m n a ∧ f a≠k*d)
    (req : ∀ c, edge m n i ≤ c → c<edge m n j → required d k c →
      ∃ a, i≤a ∧ a<j ∧ f a=c) : Segment m n d k i j := by
  let w (r : Fin (j-i)) : Fin m := ⟨f (i+r.val),hm _ (by omega) (by have := r.isLt; omega)⟩
  refine ⟨w,?_,?_,?_,?_⟩
  · intro a b hab
    exact mono _ _ (by omega) (by have := Fin.mk_le_mk.mp hab; omega) (by have := b.isLt; omega)
  · intro r
    exact ⟨(bounds _ (by omega) (by have := r.isLt; omega)).1,
      (bounds _ (by omega) (by have := r.isLt; omega)).2.1⟩
  · intro r
    exact (bounds _ (by omega) (by have := r.isLt; omega)).2.2
  · intro c lo hi hc
    obtain ⟨a,ha,hj,e⟩ := req c lo hi hc
    refine ⟨⟨a-i,by omega⟩,?_⟩
    simpa [w,Nat.add_sub_of_le ha] using e

private theorem at_build {m n d k i j} {f : ℕ → ℕ} {hm mono bounds req}
    {a} (hi : i≤a) (hj : a<j) :
    atRow (build (m:=m) (n:=n) (d:=d) (k:=k) (i:=i) (j:=j) f hm mono bounds req) a = f a := by
  simp [atRow,build,show a-i<j-i by omega,Nat.add_sub_of_le hi]

private theorem ext_at {v w : Segment m n d k i j}
    (h : ∀ a, i≤a → a<j → atRow v a = atRow w a) : v=w := by
  apply Subtype.ext
  funext r
  apply Fin.ext
  simpa only [at_idx] using h (i+r.val) (by omega) (by have := r.isLt; omega)

private def leftSide {m n d k i a j} (strict : StrictMono (edge m n)) (hia:i<a) (haj:a<j) (w:Segment m n d k i j)
    (hit : a∈contactRows w) : Segment m n d k i a :=
  build (atRow w) (fun _ hi hj => at_mem hi (by omega))
    (fun _ _ hi hab hj => at_mono hi hab (by omega))
    (fun _ hi hj => at_valid hi (by omega)) (by
      intro c lo hi hc
      obtain ⟨b,hb,hbj,e⟩ := at_required (w:=w) lo (hi.trans (strict haj)) hc
      refine ⟨b,hb,?_,e⟩
      by_contra! h
      have le := at_mono (w:=w) (show i≤a by omega) h hbj
      rw [(contacts_iff.mp hit).2.2,e] at le
      omega)

private def rightSide {m n d k i a j} (strict : StrictMono (edge m n)) (hia:i<a) (_haj:a<j)
    (w:Segment m n d k i j) (hit : a∈contactRows w) : Segment m n d k a j :=
  build (atRow w) (fun _ hi hj => at_mem (by omega) hj)
    (fun _ _ hi hab hj => at_mono (by omega) hab hj) (by
      intro b lo hi
      have v := at_valid (w:=w) (show i≤b by omega) hi
      have le := at_mono (w:=w) hia.le lo hi
      exact ⟨(contacts_iff.mp hit).2.2 ▸ le,v.2⟩) (by
      intro c lo hi hc
      obtain ⟨b,hb,hbj,e⟩ := at_required (w:=w) ((strict hia).le.trans lo) hi hc
      refine ⟨b,?_,hbj,e⟩
      by_contra! h
      have bnd := (at_valid (w:=w) hb hbj).2.1
      have := strict h
      omega)

private theorem at_left {w:Segment m n d k i j} {strict hia haj hit} {x}
    (hi : i≤x) (hx : x<a) : atRow (leftSide (a:=a) strict hia haj w hit) x = atRow w x := by
  simp [leftSide, build, atRow, show x-i<a-i by omega]

private theorem at_right {w:Segment m n d k i j} {strict hia haj hit} {x}
    (ha : a≤x) (hx : x<j) : atRow (rightSide (a:=a) strict hia haj w hit) x = atRow w x := by
  simp [rightSide, build, atRow, show x-a<j-a by omega, Nat.add_sub_of_le ha]

private def glue {m n d k i a j} (strict : StrictMono (edge m n)) (hia:i<a) (haj:a<j)
    (l:Segment m n d k i a) (r:Segment m n d k a j) : Segment m n d k i j :=
  build (fun x => if x<a then atRow l x else atRow r x) (by
    intro x hi hj; split <;> first | exact at_mem hi (by omega) | exact at_mem (by omega) hj) (by
    intro x y hi hxy hj
    by_cases h : y<a
    · simpa [h,show x<a by omega] using at_mono (w:=l) hi hxy h
    by_cases t : x<a
    · simp only [ite_eq_left t,ite_eq_right h]
      exact ((at_valid (w:=l) hi t).2.1).trans ((strict t).le.trans (at_valid (w:=r) (by omega) hj).1)
    · simpa [h,t] using at_mono (w:=r) (show a≤x by omega) hxy hj) (by
    intro x hi hj
    split
    next t => exact at_valid hi t
    next t =>
      have v := at_valid (w:=r) (show a≤x by omega) hj
      exact ⟨(strict hia).le.trans v.1,v.2⟩) (by
    intro c lo hi hc
    by_cases h : c<edge m n a
    · obtain ⟨x,hx,ha,e⟩ := at_required (w:=l) lo h hc
      exact ⟨x,hx,by omega,by simp [ha,e]⟩
    · obtain ⟨x,ha,hx,e⟩ := at_required (w:=r) (by omega) hi hc
      exact ⟨x,by omega,hx,by simp [show ¬x<a by omega,e]⟩)

private theorem at_glue {l:Segment m n d k i a} {r:Segment m n d k a j} {strict hia haj}
    {x} (hi : i≤x) (hj : x<j) :
    atRow (glue strict hia haj l r) x = if x<a then atRow l x else atRow r x := at_build hi hj

private theorem contact_glue {l:Segment m n d k i a} {r:Segment m n d k a j} {strict hia haj} :
    a ∈ contactRows (glue strict hia haj l r) := by
  apply contacts_iff.mpr
  have h := at_valid (w:=r) (le_refl a) haj
  exact ⟨hia,haj,by rw [at_glue hia.le haj,ite_eq_right (lt_irrefl _)]; exact le_antisymm h.2.1 h.1⟩

noncomputable def splitAtContact {m n d k i a j} (strict : StrictMono (edge m n)) (hia:i<a) (haj:a<j) :
    {w:Segment m n d k i j // a ∈ contactRows w} ≃ Segment m n d k i a × Segment m n d k a j where
  toFun w := (leftSide strict hia haj w.val w.property, rightSide strict hia haj w.val w.property)
  invFun lr := ⟨glue strict hia haj lr.1 lr.2,contact_glue⟩
  left_inv w := by
    apply Subtype.ext
    apply ext_at
    intro x hi hj
    rw [at_glue hi hj]
    split
    next h => exact at_left (strict:=strict) (hia:=hia) (haj:=haj) (hit:=w.property) hi h
    next h => exact at_right (strict:=strict) (hia:=hia) (haj:=haj) (hit:=w.property) (by omega) hj
  right_inv lr := by
    have hit : a ∈ contactRows (glue strict hia haj lr.1 lr.2) := contact_glue
    apply Prod.ext <;> apply ext_at
    · intro x hi hx
      have col := at_left (strict:=strict) (hia:=hia) (haj:=haj) (hit:=hit) hi hx
      exact col.trans ((at_glue hi (hx.trans haj)).trans (ite_eq_left hx))
    · intro x hx hj
      have col := at_right (strict:=strict) (hia:=hia) (haj:=haj) (hit:=hit) hx hj
      exact col.trans ((at_glue (by omega) hj).trans (ite_eq_right (not_lt_of_ge hx)))

theorem left_contacts {w:Segment m n d k i j} {a} (strict : StrictMono (edge m n))
    (hia:i<a) (haj:a<j) (hit:a∈contactRows w) :
    contactRows ((splitAtContact strict hia haj ⟨w,hit⟩).1) =
      (contactRows w).filter (· < a) := by
  classical
  ext x
  simp only [Finset.mem_filter, contacts_iff]
  constructor
  · rintro ⟨lo,hi,e⟩
    have eqn : atRow ((splitAtContact strict hia haj ⟨w,hit⟩).1) x = atRow w x := at_left (strict:=strict) (hia:=hia) (haj:=haj) (hit:=hit) lo.le hi
    exact ⟨⟨lo,by omega,eqn.symm.trans e⟩,hi⟩
  · rintro ⟨⟨lo,_,e⟩,hi⟩
    exact ⟨lo,hi,(at_left (strict:=strict) (hia:=hia) (haj:=haj) (hit:=hit) lo.le hi).trans e⟩

theorem contactRows_subset {w:Segment m n d k i j} : contactRows w ⊆ Finset.Ioo i j :=
  fun _ hx => Finset.mem_Ioo.mpr ⟨(contacts_iff.mp hx).1,(contacts_iff.mp hx).2.1⟩

end RationalReturns
