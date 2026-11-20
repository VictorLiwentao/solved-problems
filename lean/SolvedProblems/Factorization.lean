module

public import SolvedProblems.FactorGap
public import SolvedProblems.FactorFull
public import SolvedProblems.FactorReach
public import SolvedProblems.FactorSearch
public import SolvedProblems.FactorBaseline

public section

namespace PackingFactorization

private theorem counts {K} {p : Pattern K} (m : Overlap p) (u v : List (Overlap p)) :
    let L := orders false m u
    let R := orders true m v
    (packings L).card * (packings R).card ≤ (packings (L++R)).card ∧
    (Factors m u v ↔ ∀ h, ¬(TwoProfiles false m h u ∧ TwoProfiles true m h v)) := by
  obtain ⟨left,hl⟩ := side_nonempty false m u
  obtain ⟨right,hr⟩ := side_nonempty true m v
  obtain ⟨le,eq⟩ := PackingFactor.merge_count (c := hue) (packings (orders false m u))
    (packings (orders true m v)) (packings (orders false m u++orders true m v))
    (by
      intro l mem x inl
      rcases sideTag (mem_packings.mp mem) inl with col|⟨i,rfl⟩
      · simp_all
      · simp [hue_mark])
    (by
      intro l mem x inl
      rcases sideTag (mem_packings.mp mem) inl with col|⟨i,rfl⟩
      · simp_all
      · simp [hue_mark])
    (fun l hl t ht => side_shared m u v (mem_packings.mp hl) (mem_packings.mp ht))
    (fun w => by simpa only [mem_packings] using projection_iff hl hr w)
  refine ⟨le,eq.trans ⟨?_,?_⟩⟩
  · intro all h ⟨one,two⟩
    obtain ⟨l,lp,lo⟩ := profiles_occupied hl one
    obtain ⟨r,rp,ro⟩ := profiles_occupied hr two
    exact all _ (mem_packings.mpr lp) _ (mem_packings.mpr rp) h ⟨lo,ro⟩
  · intro none l lp t tp h ⟨lo,ro⟩
    exact none h ⟨occupied_profiles (mem_packings.mp lp) lo,occupied_profiles (mem_packings.mp tp) ro⟩

/-- An alphabet's designated seam splits every overlap word precisely when its
two finite sets of occupiable gaps are disjoint. The actual packing counts
enumerate permutations realizing all the specified physical windows. Both words
are read outwards: the overlap word in left-to-right order is u.reverse ++ [m] ++ v. -/
theorem factorization_criterion {K} {p : Pattern K} (A : Set (Overlap p)) (m : Overlap p) :
    (∀ u v, (∀ a ∈ u, a∈A) → (∀ a ∈ v, a∈A) → Factors m u v) ↔
      ∀ h, ¬(Marked A false m h ∧ Marked A true m h) := by
  constructor
  · intro all h ⟨⟨u,hu,_,lu⟩,⟨v,hv,_,rv⟩⟩
    exact ((counts m u v).2.mp (all u v hu hv) h) ⟨lu,rv⟩
  · intro none u v hu hv
    apply (counts m u v).2.mpr
    rintro h ⟨lu,rv⟩
    exact none h ⟨finite_cut_test.mpr ⟨u,hu,lu⟩,finite_cut_test.mpr ⟨v,hv,rv⟩⟩

/-- Failure has a witness using at most K+1 added windows on either side, and
the number of global permutations is strictly greater than the product. -/
theorem short_counterexample {K} {p : Pattern K} (A : Set (Overlap p)) (m : Overlap p)
    (failure : ¬∀ u v, (∀ a ∈ u, a∈A) → (∀ a ∈ v, a∈A) → Factors m u v) :
    ∃ u v, (∀ a ∈ u, a∈A) ∧ (∀ a ∈ v, a∈A) ∧ u.length ≤ K+1 ∧ v.length ≤ K+1 ∧
      (packings (orders false m u)).card * (packings (orders true m v)).card <
        (packings (orders false m u++orders true m v)).card := by
  have bad : ¬∀ h, ¬(Marked A false m h ∧ Marked A true m h) :=
    fun ok => failure ((factorization_criterion A m).mpr ok)
  push Not at bad
  obtain ⟨h,⟨u,hu,ub,lu⟩,⟨v,hv,vb,rv⟩⟩ := bad
  have ne : ¬Factors m u v := fun eq => ((counts m u v).2.mp eq h) ⟨lu,rv⟩
  exact ⟨u,v,hu,hv,ub,vb,lt_of_le_of_ne (counts m u v).1 (Ne.symm ne)⟩

/-- Check all m+1 seam gaps against the actual finite list of allowed overlaps. -/
@[expose] def factorTest {K} {p : Pattern K} (A : List (Overlap p)) (m : Overlap p) : Bool :=
  (List.range (m.size+1)).all (fun h => !(marked? A false m h && marked? A true m h))

/-- The executable test returns true precisely when every word splits at this seam. -/
theorem factorTest_correct {K} {p : Pattern K} (A : List (Overlap p)) (m : Overlap p) :
    factorTest A m = true ↔
      ∀ u v, (∀ a ∈ u, a∈A) → (∀ a ∈ v, a∈A) → Factors m u v := by
  change _ ↔ ∀ u v, (∀ a∈u, a∈({a | a ∈ A} : Set (Overlap p))) →
    (∀ a∈v, a∈({a | a ∈ A} : Set (Overlap p))) → Factors m u v
  rw [factorization_criterion]
  have bound {r h} (mark : Marked {a | a∈A} r m h) : h < m.size+1 := by
    obtain ⟨_,_,_,_,_,⟨c,_,_,count,_⟩,_,_⟩ := mark
    have card : (anchors m (!r) c).card ≤ m.size := by
      simpa using (Finset.card_le_univ (anchors m (!r) c))
    change (anchors m (!r) c).card = h at count
    omega
  simp only [factorTest,List.all_eq_true,List.mem_range,Bool.not_eq_true',
    Bool.eq_false_iff]
  constructor
  · intro ok h ⟨left,right⟩
    exact ok h (bound left) (Bool.and_eq_true_iff.mpr ⟨(marked?_spec ..).mpr left,(marked?_spec ..).mpr right⟩)
  · intro no h _ both
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp both
    exact no h ⟨(marked?_spec ..).mp left,(marked?_spec ..).mp right⟩

end PackingFactorization
