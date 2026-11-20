module

public import SolvedProblems.FactorColors

public section

namespace PackingFactorization

private theorem alignedCross {K} {p : Pattern K} {r} {a : Overlap p} {v n P c d}
    (old : Aligned p P v c) (new : Aligned p P (attach r a v n) d) : Cross r a c d := by
  change (anchors a r c).card = (anchors a (!r) d).card
  congr 1
  ext i
  simp only [anchors,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (old _).symm.trans (by simpa only [attach_shared] using new (slot a (!r) i))

private theorem cutsFor {K} {p : Pattern K} {r P} (w : List (Overlap p)) (v : Fin K → Nat) (n)
    (every : ∀ f ∈ framesAux r v n w, ∃ c, Aligned p P f c) :
    ∃ c ds, AlignedAll p P (framesAux r v n w) (c::ds) ∧ Walk r c w ds := by
  induction w generalizing v n with
  | nil =>
    obtain ⟨c,h⟩ := every v (by simp [framesAux])
    exact ⟨c,[],.cons h .nil,.nil _⟩
  | cons a w ih =>
    obtain ⟨c,h⟩ := every v (by simp [framesAux])
    obtain ⟨d,ds,all,walk⟩ := ih (attach r a v n) (n+1)
      (fun f hf => every f (by simp [framesAux,hf]))
    have head : Aligned p P (attach r a v n) d := by
      cases w <;> cases all <;> assumption
    exact ⟨c,d::ds,.cons h all,.step (alignedCross h head) walk⟩

private theorem splitCut {K} (p : Pattern K) (f : Fin K → Nat) {u v : List Nat}
    (nd : (u++v).Nodup) (sub : (rankOrder p f).Sublist (u++v)) :
    ∃ c : Cut K, Aligned p (fun x => x∈u) f c := by
  obtain ⟨a,b,eq,au,bv⟩ := List.sublist_append_iff.mp sub
  have len : a.length + b.length = K := by
    simpa [rankOrder] using (congrArg List.length eq).symm
  refine ⟨⟨a.length,by omega⟩,?_⟩
  intro i
  let r := (p i).val
  have valid : r < (a++b).length := by simp [len,r]
  have atRank : (a++b)[r] = f i := by
    have ok : r < (rankOrder p f).length := by simp [rankOrder,r]
    have back := List.getElem_of_eq eq ok
    simpa [rankOrder,r] using back.symm
  change f i ∈ u ↔ r < a.length
  by_cases early : r < a.length
  · simp only [early,iff_true]
    rw [←atRank,List.getElem_append_left early]
    exact au.subset (List.getElem_mem _)
  · have late : a.length ≤ r := by omega
    have inside : f i ∈ v := by
      rw [←atRank,List.getElem_append_right late]
      exact bv.subset (List.getElem_mem _)
    exact ⟨fun h => False.elim ((List.nodup_append.mp nd).2.2 _ h _ inside rfl),fun h => (early h).elim⟩

private theorem profileFor {K} {p : Pattern K} {r} {m : Overlap p} {w u v}
    (pack : Packs (orders r m w) (u++v)) :
    ∃ cs, Profile r m (PackingFactor.shared hue u).length w cs ∧
      AlignedAll p (fun x => x∈u) (frames r m w) cs := by
  obtain ⟨c,ds,all,walk⟩ := cutsFor w (initial r m) 1
    (fun f mem => splitCut p f pack.1 (pack.2.2 _ (List.mem_map.mpr ⟨_,mem,rfl⟩)))
  have head : Aligned p (fun x => x∈u) (initial r m) c := by
    cases w <;> cases all <;> assumption
  have mass := prefix_mass pack (List.nodup_append.mp pack.1).1
    (List.sublist_append_left u v).subset
  exact ⟨_,⟨_,_,rfl,(initial_mass head).symm.trans mass.symm,walk⟩,all⟩

private theorem agreeOn {K} {p : Pattern K} {P Q vs cs}
    (h : AlignedAll p P vs cs) (k : AlignedAll p Q vs cs) :
    ∀ f ∈ vs, ∀ i, P (f i) ↔ Q (f i) := by
  induction h with
  | nil => simp
  | @cons f c fs ds a b ih =>
    cases k with
    | cons a' b' =>
      intro v hv i
      rcases List.mem_cons.mp hv with rfl|hm
      · exact (a i).trans (a' i).symm
      · exact ih b' v hm i

/-- An exclusive position in a physical linear extension yields two different
compatible profiles: the prefix immediately before, and immediately after it. -/
theorem occupied_profiles {K} {p : Pattern K} {r} {m : Overlap p} {w h xs}
    (pack : Packs (orders r m w) xs) (occ : PackingFactor.Occupied hue xs h) :
    TwoProfiles r m h w := by
  rcases occ with ⟨u,x,v,rfl,exclusive,rfl⟩
  obtain ⟨cs,pc,ac⟩ := profileFor pack
  have eq : u++x::v=(u++[x])++v := by simp
  obtain ⟨ds,pd,ad⟩ := profileFor (eq ▸ pack)
  have hlen : (PackingFactor.shared hue (u++[x])).length = (PackingFactor.shared hue u).length := by
    simp [PackingFactor.shared,exclusive]
  rw [hlen] at pd
  refine ⟨cs,ds,pc,pd,?_⟩
  rintro rfl
  obtain ⟨ww,hm,hx⟩ := (pack.2.1 x).mp (by simp)
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
  obtain ⟨i,hi⟩ := (rank_mem p f x).mp hx
  have both := agreeOn ac ad f hf i
  simp only [hi] at both
  have first : x∈u := both.mpr (by simp)
  exact (List.nodup_append.mp pack.1).2.2 _ first _ (List.mem_cons_self ..) rfl

end PackingFactorization
