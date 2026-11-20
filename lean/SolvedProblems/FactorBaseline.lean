module

public import SolvedProblems.FactorPackingModel
import SolvedProblems.FactorColors
import SolvedProblems.FactorProfiles
public import SolvedProblems.FactorMerge

public section

namespace PackingFactorization

private def sliced (anchors xs : List Nat) := xs.filter (fun x => decide (x ∈ anchors))

private def ranked {K} (p : Pattern K) (v : Fin K → Nat) (a b : Nat) :=
  ∃ i j, v i = a ∧ v j = b ∧ p i ≤ p j

private theorem ranked_pairwise {K} (p : Pattern K) (v : Fin K → Nat) :
    (rankOrder p v).Pairwise (ranked p v) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  let a : Fin K := ⟨i,by simpa [rankOrder] using hi⟩
  let b : Fin K := ⟨j,by simpa [rankOrder] using hj⟩
  refine ⟨p.symm a,p.symm b,?_,?_,?_⟩
  · simp [rankOrder,a]
  · simp [rankOrder,b]
  · simpa [a,b] using (show a ≤ b from Nat.le_of_lt hij)

/-- Opposite copies of the same overlap induce identical linear orders of its labels. -/
private theorem compatible {K} {p : Pattern K} (a : Overlap p) (s : Bool)
    (v w : Fin K → Nat) (iv : Function.Injective v) (iw : Function.Injective w)
    (id : Fin a.size → Nat) (hv : ∀ t, v (slot a s t) = id t)
    (hw : ∀ t, w (slot a (!s) t) = id t) :
    sliced (List.ofFn id) (rankOrder p v) = sliced (List.ofFn id) (rankOrder p w) := by
  classical
  let A := List.ofFn id
  let L := sliced A (rankOrder p v)
  let R := sliced A (rankOrder p w)
  have ha {x} : x ∈ A ↔ ∃ t, id t = x := List.mem_ofFn
  have mL (x) : x ∈ L ↔ x ∈ A := by
    simp only [L,sliced,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    rintro hx
    obtain ⟨t,ht⟩ := ha.mp hx
    exact (rank_mem _ _ _).mpr ⟨_,(hv t).trans ht⟩
  have mR (x) : x ∈ R ↔ x ∈ A := by
    simp only [R,sliced,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    rintro hx
    obtain ⟨t,ht⟩ := ha.mp hx
    exact (rank_mem _ _ _).mpr ⟨_,(hw t).trans ht⟩
  have left : L.Pairwise (ranked p v) := (ranked_pairwise p v).filter _
  have right : R.Pairwise (ranked p w) := (ranked_pairwise p w).filter _
  have right' : R.Pairwise (ranked p v) := by
    apply right.imp_of_mem
    rintro x y hx hy ⟨i,j,hx',hy',le⟩
    obtain ⟨t,ht⟩ := ha.mp ((mR _).mp hx)
    obtain ⟨z,hz⟩ := ha.mp ((mR _).mp hy)
    have ei := iw (hx'.trans ((hw t).trans ht).symm)
    have ej := iw (hy'.trans ((hw z).trans hz).symm)
    rw [ei,ej] at le
    refine ⟨_,_,(hv t).trans ht,(hv z).trans hz,?_⟩
    cases s
    · exact (a.agrees t z).mpr le
    · exact (a.agrees t z).mp le
  have perm : L.Perm R := (List.perm_ext_iff_of_nodup ((rank_nodup _ _ iv).filter _)
      ((rank_nodup _ _ iw).filter _)).mpr (fun x => (mL x).trans (mR x).symm)
  apply List.Perm.eq_of_pairwise (le := ranked p v) _ left right' perm
  rintro x y _ _ ⟨i,j,ei,ej,le⟩ ⟨u,t,eu,et,rev⟩
  have h1 := iv (ei.trans et.symm)
  have h2 := iv (ej.trans eu.symm)
  subst t; subst u
  exact ei.symm.trans ((congrArg v (p.injective (le_antisymm le rev))).trans ej)

/-- Filtering a sublist gives the full shared restriction when it contains every kept label. -/
private theorem slice_sub {A x w : List Nat} (sub : w.Sublist x) (nd : x.Nodup)
    (inc : ∀ a ∈ x, a ∈ A → a ∈ w) : sliced A x = sliced A w := by
  have h : (sliced A w).Sublist (sliced A x) := sub.filter _
  apply (h.eq_of_length_le _).symm
  apply (nd.filter _).length_le_of_subset
  intro a ha
  obtain ⟨hx,hm⟩ := List.mem_filter.mp ha
  exact List.mem_filter.mpr ⟨inc a hx (of_decide_eq_true hm),hm⟩

private theorem glue {xs ys A : List Nat} (nx : xs.Nodup) (ny : ys.Nodup)
    (agree : sliced A xs = sliced A ys) (common : ∀ t ∈ xs, t ∈ ys → t ∈ A) :
    ∃ z : List Nat, z.Nodup ∧ xs.Sublist z ∧ ys.Sublist z ∧ ∀ t ∈ z, t ∈ xs ∨ t ∈ ys := by
  let c : Nat → Fin 3 := fun t => if t ∈ A then 1 else if t ∈ xs then 0 else 2
  have hl (t) (h : t ∈ xs) : c t ≠ 2 := by by_cases hA : t ∈ A <;> simp [c,h,hA]
  have hr (t) (h : t ∈ ys) : c t ≠ 0 := by
    by_cases hA : t ∈ A
    · simp [c,hA]
    · have hx : t ∉ xs := fun e => hA (common t e h)
      simp [c,hA,hx]
  have proj (u : List Nat) : PackingFactor.shared c u = sliced A u := by
    apply List.filter_congr
    intro t _
    by_cases hA : t ∈ A <;> by_cases hx : t ∈ xs <;> simp [c,hA,hx]
  obtain ⟨z,l,r⟩ := PackingFactor.merge_exists hl hr ((proj xs).trans (agree.trans (proj ys).symm))
  have pl : xs.Sublist z := l ▸ List.filter_sublist
  have pr : ys.Sublist z := r ▸ List.filter_sublist
  refine ⟨z,?_,pl,pr,?_⟩
  · apply List.nodup_iff_count.mpr
    intro t
    by_cases hc : c t = 2
    · have p : (c t != 0) = true := by simp [hc]
      have eq := List.count_filter (l := z) (p := fun u => c u != 0) p
      rw [← r] at ny
      exact eq ▸ (List.nodup_iff_count.mp ny t)
    · have p : (c t != 2) = true := by simpa using hc
      have eq := List.count_filter (l := z) (p := fun u => c u != 2) p
      rw [← l] at nx
      exact eq ▸ (List.nodup_iff_count.mp nx t)
  · intro t ht
    by_cases hc : c t = 2
    · exact Or.inr (r ▸ List.mem_filter.mpr ⟨ht,by simp [hc]⟩)
    · exact Or.inl (l ▸ List.mem_filter.mpr ⟨ht,by simpa using hc⟩)

/-- Grow the packing one window at a time. Every new exclusive label is larger
than all labels already used, so the immediately preceding overlap is the entire intersection. -/
private theorem extend {K} {p : Pattern K} (r : Bool) (w : List (Overlap p)) (v : Fin K → Nat)
    (n : Nat) (xs : List Nat) (nd : xs.Nodup) (ow : (rankOrder p v).Sublist xs)
    (low : ∀ t ∈ xs, t < limit K n) (iv : Function.Injective v) :
    ∃ z : List Nat, z.Nodup ∧ xs.Sublist z ∧
      (∀ f ∈ framesAux r v n w, (rankOrder p f).Sublist z) ∧
      ∀ t ∈ z, t ∈ xs ∨ ∃ f ∈ framesAux r v n w, t ∈ rankOrder p f := by
  induction w generalizing n v xs with
  | nil => exact ⟨xs,nd,List.Sublist.refl _,by simpa [framesAux] using ow,fun _ h => Or.inl h⟩
  | cons a w ih =>
    let next := attach r a v n
    let id (i : Fin a.size) := v (slot a r i)
    let A := List.ofFn id
    have lv (i) := low _ (ow.subset ((rank_mem p v _).mpr ⟨i,rfl⟩))
    have iv' : Function.Injective next := attach_inj r a v n lv iv
    have common (t) (ht : t ∈ xs) (ht' : t ∈ rankOrder p next) : t ∈ A := by
      obtain ⟨i,hi⟩ := (rank_mem _ _ _).mp ht'
      by_cases hs : shared a (!r) i
      · apply List.mem_ofFn.mpr
        exact ⟨seamIndex a (!r) i hs, by simpa [next,attach,hs,id] using hi⟩
      · have hge := fresh_ge K r n i.val
        have hlow := low t ht
        simp [next,attach,hs] at hi
        omega
    have cut : sliced A xs = sliced A (rankOrder p v) := by
      apply slice_sub ow nd
      rintro _ _ h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      exact (rank_mem _ _ _).mpr ⟨slot a r i,rfl⟩
    have agree := compatible a r v next iv iv' id (fun _ => rfl) (attach_shared r a v n)
    obtain ⟨y,ny,old,new,mem⟩ := glue nd (rank_nodup p next iv') (cut.trans agree) common
    have low' (t) (ht : t ∈ y) : t < limit K (n+1) := by
      rcases mem t ht with h|h
      · exact lt_of_lt_of_le (low t h) (limit_mono _ _)
      · obtain ⟨i,rfl⟩ := (rank_mem _ _ _).mp h
        exact attach_lt r a v n lv i
    obtain ⟨z,nz,yz,all,cover⟩ := ih next (n+1) y ny new low' iv'
    refine ⟨z,nz,old.trans yz,?_,?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with e|e
      · subst f; exact ow.trans (old.trans yz)
      · exact all f e
    · intro t ht
      rcases cover t ht with h|⟨f,hf,ht⟩
      · rcases mem t h with h|h
        · exact Or.inl h
        · have hnext : next ∈ framesAux r next (n+1) w := by cases w <;> simp [framesAux]
          exact Or.inr ⟨next,List.mem_cons_of_mem _ hnext,h⟩
      · exact Or.inr ⟨f,List.mem_cons_of_mem _ hf,ht⟩

theorem side_nonempty {K} {p : Pattern K} (r) (m : Overlap p) (w : List (Overlap p)) :
    ∃ x, Packs (orders r m w) x := by
  let v := initial r m
  let xs := rankOrder p v
  have inj := initial_inj r m
  have low (t) (ht : t ∈ xs) : t < limit K 1 := by
    obtain ⟨i,rfl⟩ := (rank_mem _ _ _).mp ht
    exact initial_lt r m i
  obtain ⟨z,nd,xz,all,cover⟩ := extend r w v 1 xs (rank_nodup p v inj) (List.Sublist.refl _) low inj
  have vmem : v ∈ frames r m w := by cases w <;> simp [v,frames,framesAux]
  refine ⟨z,nd,?_,?_⟩
  · intro t
    constructor
    · intro ht
      rcases cover t ht with h|⟨f,hf,h⟩
      · exact ⟨xs,List.mem_map.mpr ⟨v,vmem,rfl⟩,h⟩
      · exact ⟨_,List.mem_map.mpr ⟨f,hf,rfl⟩,h⟩
    · rintro ⟨o,ho,ht⟩
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ho
      exact (all f hf).subset ht
  · intro o ho
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ho
    exact all f hf

private theorem seamView {K} {p : Pattern K} {m : Overlap p} {r w xs}
    (pack : Packs (orders r m w) xs) :
    PackingFactor.shared hue xs = sliced (List.ofFn (@seamMark m.size)) (rankOrder p (initial r m)) := by
  let A := List.ofFn (@seamMark m.size)
  have view : PackingFactor.shared hue xs = sliced A xs := by
    apply List.filter_congr
    intro x hx
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq,A,List.mem_ofFn]
    exact side_mark_iff pack hx
  have mem : initial r m ∈ frames r m w := by cases w <;> simp [frames,framesAux]
  rw [view]
  apply slice_sub (pack_sublist pack (List.mem_map.mpr ⟨_,mem,rfl⟩)) pack.1
  intro x _ hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact (rank_mem _ _ _).mpr ⟨_, initial_shared r m i⟩

/-- Each packing side contains the same marks in the order imposed by the seam. -/
theorem side_shared {K} {p : Pattern K} (m : Overlap p) (u v : List (Overlap p)) {l t}
    (hl : Packs (orders false m u) l) (hr : Packs (orders true m v) t) :
    PackingFactor.shared hue l = PackingFactor.shared hue t := by
  rw [seamView hl,seamView hr]
  exact compatible m true _ _ (initial_inj false m) (initial_inj true m) seamMark
    (initial_shared false m) (initial_shared true m)

end PackingFactorization
