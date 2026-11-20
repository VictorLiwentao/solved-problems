module

public import SolvedProblems.RationalReturnsBags
import SolvedProblems.RationalReturnsSplit

@[expose] public section

namespace RationalReturns

@[simp] theorem edge_end {m n : ℕ} (hn : 0 < n) : edge m n n = m := by
  simp [edge, Nat.mul_div_cancel_left _ hn]

/-- The floor boundary on rows and the ceiling boundary on columns are inverse thresholds. -/
theorem lt_demand {m n : ℕ} (hn : 0 < n) (hm : 0 < m) (i q c : ℕ) :
    q < demand m n i c ↔ edge m n (i+q) < c := by
  unfold demand edge
  rw [Nat.div_lt_iff_lt_mul hn]
  have e : (n*c+m-1)-(m-1) = n*c := by omega
  have h : i+q < (n*c+m-1)/m ↔ (i+q)*m < c*n := by
    rw [Nat.lt_div_iff_mul_lt hm,e,Nat.mul_comm c n]
  omega

theorem demand_le {m n i j c : ℕ} (hn : 0 < n) (hm : n ≤ m) (hij : i ≤ j)
    (hc : c ≤ edge m n j) : demand m n i c ≤ j-i := by
  by_contra! bad
  have over := (lt_demand hn (hn.trans_le hm) i (j-i) c).mp bad
  have atj : i+(j-i)=j := by omega
  rw [atj] at over
  exact over.not_ge hc

theorem mem_mandatory {d k L U c : ℕ} :
    c ∈ mandatory d k L U ↔ required d k c ∧ L ≤ c ∧ c < U := by
  simp [mandatory,required]

theorem mem_allowed {d k L U c : ℕ} :
    c ∈ allowed d k L U ↔ c ≠ k*d ∧ L ≤ c ∧ c < U := by
  simp [allowed]

theorem mandatory_subset_allowed {d k L U : ℕ} (hd : 0 < d) :
    mandatory d k L U ⊆ allowed d k L U := by
  intro c hc
  obtain ⟨⟨p,hp,rfl⟩,lo,hi⟩ := mem_mandatory.mp hc
  exact mem_allowed.mpr ⟨(Nat.mul_lt_mul_of_pos_right hp hd).ne,lo,hi⟩

/-- Multiplicities of physical north steps. The prefix lower bounds check
all diagonal inequalities, including arrivals at both endpoints. -/
def BagGood (t : ℕ) (A B : Finset ℕ) (D : ℕ → ℕ) (L U : ℕ) (s : Multiset ℕ) : Prop :=
  s.card = t ∧ (∀ x ∈ s, x ∈ A) ∧ B.val ≤ s ∧
    ∀ c ∈ Finset.Icc L U, D c ≤ less s c

theorem good_bag {m n d k i j : ℕ} (hn : 0 < n) (hm : n ≤ m)
    (hij : i < j) {w : Word m (j-i)} (valid : Valid m n d k i j w) :
    BagGood (j-i) (allowed d k (edge m n i) (edge m n j))
      (mandatory d k (edge m n i) (edge m n j)) (demand m n i)
      (edge m n i) (edge m n j) (bag fun q => (w q).val) := by
  obtain ⟨mono,bounds,avoid,requiredCols⟩ := valid
  have orderWord : Monotone (fun q => (w q).val) := fun _ _ h => mono h
  refine ⟨card_bag _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q,rfl⟩ := mem_bag.mp hx
    exact mem_allowed.mpr ⟨avoid q,(bounds q).1,(bounds q).2.trans_lt
      (edge_strict hn hm (by have := q.isLt; omega))⟩
  · apply (Multiset.le_iff_subset (Finset.nodup _)).mpr
    intro c hc
    obtain ⟨need,lo,hi⟩ := mem_mandatory.mp hc
    exact mem_bag.mpr (requiredCols c lo hi need)
  · intro c hc
    have hu := (Finset.mem_Icc.mp hc).2
    apply (less_bound orderWord (demand_le hn hm hij.le hu)).mpr
    intro q hq
    exact (bounds q).2.trans_lt ((lt_demand hn (hn.trans_le hm) i q.val c).mp hq)

theorem valid_of_good_bag {m n d k i j : ℕ} (hn : 0 < n) (hm : n ≤ m)
    {w : Word m (j-i)} (mono : Monotone w)
    (good : BagGood (j-i) (allowed d k (edge m n i) (edge m n j))
      (mandatory d k (edge m n i) (edge m n j)) (demand m n i)
      (edge m n i) (edge m n j) (bag fun q => (w q).val)) : Valid m n d k i j w := by
  have orderWord : Monotone (fun q => (w q).val) := fun _ _ h => mono h
  have col (q : Fin (j-i)) := mem_allowed.mp (good.2.1 _ (mem_bag.mpr ⟨q,rfl⟩))
  refine ⟨mono, fun q => ⟨(col q).2.1,?_⟩, fun q => (col q).1, ?_⟩
  · let c := edge m n (i+q.val)+1
    have hc : c ∈ Finset.Icc (edge m n i) (edge m n j) := by
      apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.le_succ_of_le ((edge_strict hn hm).monotone (Nat.le_add_right ..))
      · exact edge_strict hn hm (by have := q.isLt; omega)
    have qd := (lt_demand hn (hn.trans_le hm) i q.val c).mpr (Nat.lt_succ_self _)
    exact Nat.le_of_lt_succ ((lt_less_iff orderWord q c).mp (qd.trans_le (good.2.2.2 c hc)))
  · intro c lo hi h
    exact mem_bag.mp ((Multiset.le_iff_subset (Finset.nodup _)).mp good.2.2.1
      (mem_mandatory.mpr ⟨h,lo,hi⟩))

/-- Forgetting the order of a monotone column word is reversible by sorting.
The positive/forbidden column constraints become lower bounds on multiplicities. -/
noncomputable def segmentBags {m n d k i j : ℕ} (hn : 0 < n) (hm : n ≤ m)
    (hij : i < j) (hj : j ≤ n) : Segment m n d k i j ≃
    {s : Multiset ℕ // BagGood (j-i) (allowed d k (edge m n i) (edge m n j))
      (mandatory d k (edge m n i) (edge m n j)) (demand m n i)
      (edge m n i) (edge m n j) s} := by
  let A := allowed d k (edge m n i) (edge m n j)
  let B := mandatory d k (edge m n i) (edge m n j)
  let P := BagGood (j-i) A B (demand m n i) (edge m n i) (edge m n j)
  let word (s : {s : Multiset ℕ // P s}) (q : Fin (j-i)) : Fin m := ⟨sortedWord s.val s.property.1 q,by
    have mem : sortedWord s.val s.property.1 q ∈ s.val := by
      have e := (mem_bag (w:=sortedWord s.val s.property.1)).mpr ⟨q,rfl⟩
      simpa only [bag_sorted] using e
    have hu := (mem_allowed.mp (s.property.2.1 _ mem)).2.2
    exact hu.trans_le (by simpa [edge_end hn] using (edge_strict hn hm).monotone hj)⟩
  have wm (s : {s : Multiset ℕ // P s}) : Monotone (word s) :=
    fun _ _ h => sorted_mono s.val s.property.1 h
  have bagword (s : {s : Multiset ℕ // P s}) : (bag fun q => (word s q).val) = s.val :=
    bag_sorted s.val s.property.1
  refine ⟨fun w => ⟨_,good_bag hn hm hij w.property⟩,fun s => ⟨word s,?valid⟩,?left,?right⟩
  case valid =>
    apply valid_of_good_bag hn hm (wm s)
    rw [bagword]; exact s.property
  case left =>
    intro w
    apply Subtype.ext; funext q; apply Fin.ext
    let s : {s : Multiset ℕ // P s} := ⟨_,good_bag hn hm hij w.property⟩
    exact congrFun (bag_inj (v:=fun q => (word s q).val) (w:=fun q => (w.val q).val)
      (fun _ _ h => wm s h) (fun _ _ h => w.property.1 h) (bagword s)) q
  case right => exact fun s => Subtype.ext (bagword s)
end RationalReturns
