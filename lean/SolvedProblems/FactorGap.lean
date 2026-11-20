module

public import SolvedProblems.FactorOccupancy
public import SolvedProblems.FactorBuckets

public section

namespace PackingFactorization

private theorem first_aligned {K} {p : Pattern K} {r} {m : Overlap p} {w P c ds}
    (all : AlignedAll p P (frames r m w) (c::ds)) : Aligned p P (initial r m) c := by
  cases w <;> cases all <;> assumption

private theorem at_frame {K} {p : Pattern K} {P fs cs} (h : AlignedAll p P fs cs) :
    ∀ f∈fs, ∃ c, Aligned p P f c := by
  induction h with
  | nil => simp
  | cons head _ ih =>
    intro f mem
    rcases List.mem_cons.mp mem with rfl|mem
    · exact ⟨_,head⟩
    · exact ih f mem

private theorem unique_cuts {K} {p : Pattern K} {P Q fs cs ds}
    (one : AlignedAll p P fs cs) (two : AlignedAll p Q fs ds)
    (agree : ∀ f∈fs, ∀ i, P (f i) ↔ Q (f i)) : cs=ds := by
  induction one generalizing ds with
  | nil => cases two; rfl
  | @cons v c vs cs head tail ih =>
    cases two with
    | @cons _ d _ ds hq tq =>
      have eq (i : Fin K) : (p i).val<c.val ↔ (p i).val<d.val :=
        (head i).symm.trans ((agree v (by simp) i).trans (hq i))
      have le {u t : Cut K} (comp : ∀ i : Fin K, (p i).val<u.val → (p i).val<t.val) : u.val ≤ t.val := by
        by_contra! h
        let j : Fin K := ⟨t.val,by have := u.isLt; omega⟩
        have ht := comp (p.symm j) (by simpa [j] using h)
        simpa [j] using ht
      have cd : c=d := Fin.ext (Nat.le_antisymm (le (fun i => (eq i).mp)) (le (fun i => (eq i).mpr)))
      exact congrArg₂ List.cons cd (ih tq (fun f hf => agree f (by simp [hf])))

private theorem fixedMarks {K} {p : Pattern K} {r} {m : Overlap p} {P Q c d}
    (old : Aligned p P (initial r m) c) (new : Aligned p Q (initial r m) d)
    (eq : anchorCount m (!r) c = anchorCount m (!r) d) :
    ∀ i : Fin m.size, P (seamMark i) ↔ Q (seamMark i) := by
  change (anchors m (!r) c).card = (anchors m (!r) d).card at eq
  have mono {x y : Cut K} (le : x.val≤y.val) : anchors m (!r) x ⊆ anchors m (!r) y := by
    intro i hi
    simp only [anchors,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    omega
  have sets : anchors m (!r) c = anchors m (!r) d := by
    rcases Nat.le_total c.val d.val with h|h
    · exact Finset.eq_of_subset_of_card_le (mono h) eq.ge
    · exact (Finset.eq_of_subset_of_card_le (mono h) eq.le).symm
  intro i
  have ranks : (p (slot m (!r) i)).val < c.val ↔ (p (slot m (!r) i)).val < d.val := by
    simpa [anchors] using (show i∈anchors m (!r) c ↔ i∈anchors m (!r) d from sets ▸ Iff.rfl)
  simpa [seamMark,initial_shared] using
    (old (slot m (!r) i)).trans (ranks.trans (new (slot m (!r) i)).symm)

/-- Two different compatible cuts with the same anchor count have a nonempty
middle layer. Stable sorting a physical packing by the intersection, symmetric
difference, and complement of the two cuts gives a packing occupying the gap. -/
theorem profiles_occupied {K} {p : Pattern K} {r} {m : Overlap p} {w h xs}
    (pack : Packs (orders r m w) xs) (two : TwoProfiles r m h w) :
    ∃ ys, Packs (orders r m w) ys ∧ PackingFactor.Occupied hue ys h := by
  classical
  obtain ⟨cs,ds,hc,hd,ne⟩ := two
  obtain ⟨P,one⟩ := realize hc
  obtain ⟨Q,two⟩ := realize hd
  have changed : ∃ f∈frames r m w, ∃ i, ¬(P (f i) ↔ Q (f i)) := by
    by_contra! agree
    exact ne (unique_cuts one two agree)
  obtain ⟨f,mf,i,diff⟩ := changed
  let g := grade P Q
  have ordered : ∀ o ∈ orders r m w, o.Pairwise (fun x y => g x ≤ g y) := by
    intro o ho
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (show o ∈ (frames r m w).map (rankOrder p) from ho)
    obtain ⟨_,c⟩ := at_frame one v hv
    obtain ⟨_,d⟩ := at_frame two v hv
    exact aligned_order p c d
  have pack' := reorder_packs pack g ordered
  obtain ⟨c,cs,rfl,count,_⟩ := hc
  obtain ⟨d,ds,rfl,count',_⟩ := hd
  have head := first_aligned one
  have agree := fixedMarks head (first_aligned two) (count.trans count'.symm)
  have mid : f i ∈ bucket g 1 xs := by
    simp only [bucket,List.mem_filter,beq_iff_eq]
    exact ⟨nonempty_support mf i pack,grade_one.mpr diff⟩
  obtain ⟨z,zs,eq⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem mid)
  have mem : z ∈ bucket g 1 xs := eq ▸ List.mem_cons_self ..
  obtain ⟨inz,gz⟩ := List.mem_filter.mp mem
  have ex : hue z ≠ 1 := by
    intro hz
    obtain ⟨i,rfl⟩ := (side_mark_iff pack inz).mp hz
    exact (grade_one.mp (beq_iff_eq.mp gz)) (agree i)
  have mass : seamMass m.size (fun x => x ∈ bucket g 0 xs) = seamMass m.size P := by
    unfold seamMass
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,bucket,List.mem_filter,beq_iff_eq,
      side_has_mark pack, true_and, g,grade_zero]
    exact ⟨And.left,fun h => ⟨h,(agree i).mp h⟩⟩
  have lowCount := prefix_mass pack (show (bucket g 0 xs).Nodup from pack.1.filter _)
    (show bucket g 0 xs ⊆ xs from List.filter_sublist.subset)
  refine ⟨_,pack',bucket g 0 xs,z,zs++bucket g 2 xs,?_,ex,
    lowCount.trans (mass.trans ((initial_mass head).trans count))⟩
  simp [reorder,eq,List.append_assoc]

end PackingFactorization
