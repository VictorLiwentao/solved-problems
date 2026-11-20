module

public import SolvedProblems.FactorCuts

public section

namespace PackingFactorization

private inductive Route {K} {p : Pattern K} (A : Set (Overlap p)) (right : Bool) (z : Cut K) :
    Cut K → List (Overlap p) → List (Cut K) → Prop
  | stop : Route A right z z [] []
  | cons {c d a w ds} : a ∈ A → Cross right a c d → Route A right z d w ds →
      Route A right z c (a::w) (d::ds)

private theorem suffixRoute {K p A r} {z c x : Cut K} {w : List (Overlap p)} {ds}
    (h : Route A r z c w ds) (mem : x ∈ c::ds) (nd : (c::ds).Nodup) :
    ∃ w' ds', Route A r z x w' ds' ∧ (x::ds').Nodup := by
  induction h with
  | stop =>
    have e : x=z := by simpa using mem
    subst x; exact ⟨[],[],.stop,by simp⟩
  | cons aa step tail ih =>
    rcases List.mem_cons.mp mem with eq|mem
    · subst x; exact ⟨_,_,.cons aa step tail,nd⟩
    · exact ih mem (List.nodup_cons.mp nd).2

private theorem shortRoute {K p A r} {z c : Cut K} {w : List (Overlap p)} {ds}
    (h : Route A r z c w ds) : ∃ w' ds', Route A r z c w' ds' ∧ (c::ds').Nodup := by
  induction h with
  | stop => exact ⟨[],[],.stop,by simp⟩
  | @cons c d a w ds aa step tail ih =>
    obtain ⟨w',ds',route,nd⟩ := ih
    by_cases mem : c ∈ d::ds'
    · exact suffixRoute route mem nd
    · exact ⟨_,_,.cons aa step route,List.nodup_cons.mpr ⟨mem,nd⟩⟩

private theorem routeInfo {K p A r} {z c : Cut K} {w : List (Overlap p)} {ds}
    (h : Route A r z c w ds) :
    (∀ a ∈ w, a ∈ A) ∧ w.length=ds.length := by
  induction h with
  | stop => simp
  | cons aa _ _ ih => simpa using And.intro (And.intro aa ih.1) ih.2

private theorem appendFork {K p A r} {z c d : Cut K} {w : List (Overlap p)} {ds} {a}
    (h : Route A r z c w ds) (step : Cross r a z d) :
    Walk r c (w++[a]) (ds++[d]) := by
  induction h with
  | stop => exact .step step (.nil _)
  | cons _ edge _ ih => exact .step edge ih

private def Fork {K} {p : Pattern K} (A : Set (Overlap p)) (r : Bool) (c : Cut K) :=
  ∃ a ∈ A, ∃ d e, Cross r a c d ∧ Cross r a c e ∧ d≠e

private theorem walkFork {K p A r} {c : Cut K} {w : List (Overlap p)} {ds es}
    (hw : ∀ a ∈ w, a ∈ A) (hd : Walk r c w ds) (he : Walk r c w es) (ne : ds ≠ es) :
    ∃ z w' cs, Route A r z c w' cs ∧ Fork A r z := by
  induction hd generalizing es with
  | nil => cases he; exact (ne rfl).elim
  | @step a c d w ds step tail ih =>
    cases he with
    | @step _ _ e _ es step' tail' =>
      by_cases eq : d=e
      · subst e
        obtain ⟨z,v,cs,route,fork⟩ := ih (fun a ha => hw a (by simp [ha])) tail' (by rintro rfl; exact ne rfl)
        exact ⟨z,a::v,d::cs,.cons (hw a (by simp)) step route,fork⟩
      · exact ⟨c,[],[],.stop,a,hw a (by simp),d,e,step,step',eq⟩

/-- If distinct compatible cut profiles occur at any word, a pair already occurs
on a word of at most K+1 overlaps: erase all loops before its first fork. -/
theorem finite_cut_test {K} {p : Pattern K} {A : Set (Overlap p)} {r m h} :
    Marked A r m h ↔ ∃ w, (∀ a ∈ w, a ∈ A) ∧ TwoProfiles r m h w := by
  constructor
  · rintro ⟨w,hw,_,pair⟩; exact ⟨w,hw,pair⟩
  · rintro ⟨w,hw,cs,es,⟨c,ds,rfl,init,hd⟩,⟨e,es,rfl,init',he⟩,ne⟩
    by_cases eq : c=e
    · subst e
      obtain ⟨z,_,_,route,fork⟩ := walkFork hw hd he (by rintro rfl; exact ne rfl)
      obtain ⟨v,as,route,nd⟩ := shortRoute route
      obtain ⟨a,aa,d,e,cd,ce,de⟩ := fork
      obtain ⟨allowed,len⟩ := routeInfo route
      have card := nd.length_le_of_subset (l₂ := List.finRange (K+1)) (fun x _ => List.mem_finRange x)
      refine ⟨v++[a],by intro b hb; rcases List.mem_append.mp hb with h|h; exact allowed b h; simpa using (List.mem_singleton.mp h ▸ aa),by simpa [len] using card,
        c::(as++[d]),c::(as++[e]),⟨_,_,rfl,init,appendFork route cd⟩,
        ⟨_,_,rfl,init,appendFork route ce⟩,?_⟩
      simpa using de
    · exact ⟨[],by simp,by simp,[c],[e],⟨_,_,rfl,init,.nil _⟩,⟨_,_,rfl,init',.nil _⟩,
        by simpa using eq⟩

end PackingFactorization
