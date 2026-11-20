module

public import SolvedProblems.PositiveWitnessModel

public section

namespace PositiveWitness

private def bound (xs : List Word) := (xs.map rank).foldr max 0
private theorem bounded {x : Word} {xs : List Word} (hx : x ∈ xs) : rank x ≤ bound xs := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih hx) (Nat.le_max_right ..)

private def core (j : Nat) : List Word :=
  let ids := List.range (j+1)
  ids.map Word.neutralCore ++ [false,true].flatMap fun b =>
    ids.flatMap fun k => ids.map (Word.stripe b k)

private theorem coreNeutral {r j} (h : r ≤ j) : Word.neutralCore r ∈ core j := by
  simp [core,h,Nat.lt_succ_iff]

private theorem coreStripe {b k r j} (hk : k ≤ j) (hr : r ≤ j) : Word.stripe b k r ∈ core j := by
  cases b <;> simp [core,Nat.lt_succ_iff,hk,hr]

private def four (j : Nat) := [Target.anchor false,.anchor true,.satellite false j,.satellite true j]

private theorem wholeIntersection {j x} (all : ∀ h ∈ four j, member h x) : x ∈ core j := by
  have a := all (.anchor false) (by simp [four])
  have b := all (.anchor true) (by simp [four])
  have s := all (.satellite false j) (by simp [four])
  have t := all (.satellite true j) (by simp [four])
  cases x with
  | anchorPart side inc r => cases side <;> simp_all [member]
  | partner _ _ => simp [member] at a
  | neutralCore r => exact coreNeutral (by simpa [member] using s)
  | stripe side k r =>
    apply coreStripe <;> cases side <;> by_cases z : k = 0 <;> by_cases eq : k = j+1 <;>
      simp_all [member]

private def joint (j : Nat) (x y : Word) := ∀ h ∈ four j, member h x ≠ member h y

private theorem corePartner {j x} (hx : x ∈ core j) : joint j x (.partner true j) := by
  cases x <;> simp [core,List.mem_flatMap,Nat.lt_succ_iff] at hx <;>
    simp_all [joint,four,member] <;> grind

private theorem mate {j x} (ok : x ∈ core j ∨
    ((member (.satellite true j) x ∨ member (.satellite false j) x) ∨
     (∃ a, member (.anchor a) x ∧ rank x ≤ j))) : ∃ y, joint j x y := by
  rcases ok with hx | hx
  · exact ⟨_,corePartner hx⟩
  cases x with
  | anchorPart b inc r =>
    exact ⟨.anchorPart (!b) (!inc) 0, by cases b <;> cases inc <;> simp [joint,four,member]⟩
  | neutralCore r =>
    have le : r ≤ j := by simpa [member,rank] using hx
    exact ⟨_,corePartner (coreNeutral le)⟩
  | stripe b k r =>
    by_cases small : k ≤ j ∧ r ≤ j
    · exact ⟨_,corePartner (coreStripe small.1 small.2)⟩
    · let side := member (.satellite false j) (.stripe b k r)
      refine ⟨.partner side (j+1), ?_⟩
      cases b <;> by_cases z : k = 0 <;> by_cases eq : k = j+1 <;>
        by_cases hk : k ≤ j <;> by_cases hr : r ≤ j <;>
        simp_all [joint,side,four,member] <;> grind
  | partner b i =>
    have ne : j ≠ i := by cases b <;> simpa [member] using hx
    exact ⟨.stripe (!b) 0 (j+1), by cases b <;> simp [joint,four,member,ne]⟩

private theorem incompatible : ¬ compatible := by
  classical
  rintro ⟨W,positive,valid⟩
  let anchors := W (.anchor true) ++ W (.anchor false)
  let j := bound anchors
  let required := core j ++ anchors ++ W (.satellite true j) ++ W (.satellite false j)
  have mates (x) (hx : x ∈ required) : ∃ y, joint j x y := by
    apply mate
    simp only [required,List.mem_append] at hx
    rcases hx with ((hc | ha) | ht) | hf
    · exact .inl hc
    · have small := bounded ha
      rcases List.mem_append.mp ha with ht|hf
      · exact .inr (.inr ⟨true,positive _ _ ht,small⟩)
      · exact .inr (.inr ⟨false,positive _ _ hf,small⟩)
    · exact .inr (.inl (.inl (positive _ _ ht)))
    · exact .inr (.inl (.inr (positive _ _ hf)))
  let edges := required.attach.map fun (x : {w // w ∈ required}) => (x.val,(mates x x.property).choose)
  have covered {x} (hx : x ∈ required) : seen (observed edges) x :=
    ⟨_,.inl (List.mem_map.mpr ⟨⟨x,hx⟩,List.mem_attach ..,rfl⟩)⟩
  have on {h} (hh : h ∈ four j) : active W (observed edges) h := by
    constructor
    · intro x y hxy
      rcases hxy with hxy|hyx
      · obtain ⟨u,_,eq⟩ := List.mem_map.mp hxy
        cases eq
        exact (mates u u.property).choose_spec h hh
      · obtain ⟨u,_,eq⟩ := List.mem_map.mp hyx
        cases eq
        exact Ne.symm ((mates u u.property).choose_spec h hh)
    · intro x hx
      apply covered
      simp [four] at hh
      rcases hh with rfl|rfl|rfl|rfl <;> simp [required,anchors,hx]
  obtain ⟨x,fresh,all⟩ := valid edges ⟨.anchor true,on (by simp [four])⟩
  have hx := wholeIntersection (j := j) (fun h hh => all h (on hh))
  exact fresh (covered (by simp [required,hx]))

private def safe (E : Edges) (x : Word) :=
  ¬ seen E x ∧ ∀ h, consistent h E → member h x

private noncomputable def generate (E : Edges) : Word := by
  classical
  exact if h : ∃ x, safe E x then h.choose else
    .anchorPart false true (if f : ∃ r, ¬ seen E (.anchorPart false true r) then f.choose else 0)

private theorem largeFresh (s : List (Word × Word)) :
    ∃ r, ∀ x, r ≤ rank x → ¬ seen (observed s) x := by
  let xs := s.flatMap fun p => [p.1,p.2]
  refine ⟨bound xs + 1,?_⟩
  rintro x hx ⟨y,h|h⟩
  · have := bounded (xs := xs) (List.mem_flatMap.mpr ⟨(x,y),h,by simp⟩ : x ∈ xs)
    omega
  · have := bounded (xs := xs) (List.mem_flatMap.mpr ⟨(y,x),h,by simp⟩ : x ∈ xs)
    omega

private theorem legal {h e} (ok : ∀ i, honest h (e i)) (n) : consistent h (prefixEdges e n) := by
  intro x y hxy
  rcases hxy with hxy|hyx
  · obtain ⟨i,_,he⟩ := List.mem_map.mp hxy
    simpa only [honest,he] using ok i
  · obtain ⟨i,_,he⟩ := List.mem_map.mp hyx
    exact Ne.symm (show member h (y,x).1 ≠ member h (y,x).2 from he ▸ ok i)

private theorem persists {e : Nat → Word × Word} {w t n} (le : t ≤ n)
    (h : (e t).1 = w ∨ (e t).2 = w) :
    ∃ y, (y = (e t).2 ∨ y = (e t).1) ∧ prefixEdges e n w y := by
  have mem : e t ∈ (List.range (n+1)).map e := List.mem_map.mpr ⟨t,by simp; omega,rfl⟩
  rcases h with h|h
  · exact ⟨_,.inl rfl,.inl (h ▸ mem)⟩
  · exact ⟨_,.inr rfl,.inr (h ▸ mem)⟩

private theorem missingAnchor {E : Edges} {r : Nat} (fresh : ∀ x, r ≤ rank x → ¬ seen E x)
    {a : Bool} (bad : ¬ consistent (.anchor a) E) : ∃ x, safe E x := by
  refine ⟨.anchorPart (!a) true r,fresh _ (Nat.le_refl _),?_⟩
  intro h hc
  cases h with
  | anchor b => cases a <;> cases b <;> simp_all [member]
  | satellite _ _ => rfl

private theorem partnerType {E : Edges} (both : ∀ b, consistent (.anchor b) E)
    {y} (edge : E (.neutralCore 0) y) : ∃ s j, y = .partner s j := by
  have h := both true _ _ edge
  have h' := both false _ _ edge
  cases y with
  | anchorPart b _ _ => cases b <;> simp_all [member]
  | partner s j => exact ⟨s,j,rfl⟩
  | _ => simp [member] at h

/-- Observing a late neutral core point rules out at least one of the two
satellites at j while both anchors remain consistent. -/
private theorem missingSatellite {E : Edges} (both : ∀ b, consistent (.anchor b) E)
    {y j} (edge : E (.neutralCore (j+1)) y) :
    ¬ consistent (.satellite false j) E ∨ ¬ consistent (.satellite true j) E := by
  classical
  by_cases h : consistent (.satellite false j) E
  · refine .inr fun ht => ?_
    have a := both true _ _ edge
    have b := both false _ _ edge
    have s := h _ _ edge
    have t := ht _ _ edge
    cases y with
    | anchorPart c _ _ => cases c <;> simp_all [member]
    | partner c i => cases c <;> simp_all [member] <;> omega
    | _ => simp [member] at a
  · exact .inl h

private theorem survivingBlock {E : Edges} {s : Bool} {j r : Nat}
    (fresh : ∀ x, r ≤ rank x → ¬ seen E x)
    (hub : E (.neutralCore 0) (.partner s j))
    (missing : ¬ consistent (.satellite false j) E ∨ ¬ consistent (.satellite true j) E) :
    ∃ x, safe E x := by
  have restricted {b i} (hc : consistent (.satellite b i) E) (eq : b = s) : i = j := by
    have := hc _ _ hub
    simpa [member,eq] using this
  by_cases bad : consistent (.satellite s j) E
  · have other : ¬ consistent (.satellite (!s) j) E := by cases s <;> simp_all
    refine ⟨.stripe s (j+1) r,fresh _ (Nat.le_max_right ..),?_⟩
    intro h hc
    cases h with
    | anchor _ => rfl
    | satellite b i =>
      by_cases eq : b = s
      · have hij := restricted hc eq
        simp [member,eq,hij]
      · have ne : i ≠ j := by
          intro hij
          have e : b = !s := by cases b <;> cases s <;> simp_all
          exact other (e ▸ hij ▸ hc)
        cases b <;> cases s <;> simp_all [member] <;> omega
  · refine ⟨.stripe (!s) 0 r,fresh _ (Nat.le_max_right ..),?_⟩
    intro h hc
    cases h with
    | anchor _ => rfl
    | satellite b i =>
      have ne : b ≠ s := fun eq => bad (eq ▸ (restricted hc eq) ▸ hc)
      cases b <;> cases s <;> simp_all [member]

private theorem generatorWorks : generates := by
  classical
  refine ⟨generate,?_⟩
  intro h e clean covers
  have good (n) (ex : ∃ x, safe (prefixEdges e n) x) :
      member h (generate (prefixEdges e n)) ∧ ¬ seen (prefixEdges e n) (generate (prefixEdges e n)) := by
    simpa [generate,ex] using And.intro (ex.choose_spec.2 h (legal clean n)) ex.choose_spec.1
  cases h with
  | satellite b i =>
    refine ⟨0,fun n _ => ?_⟩
    by_cases ex : ∃ x, safe (prefixEdges e n) x
    · exact good n ex
    · obtain ⟨r,hr⟩ := largeFresh ((List.range (n+1)).map e)
      have f : ∃ r, ¬ seen (prefixEdges e n) (.anchorPart false true r) :=
        ⟨r,hr _ (Nat.le_refl _)⟩
      simp [generate,ex,f,member,f.choose_spec]
  | anchor a =>
    obtain ⟨t,ht⟩ := covers (.neutralCore 0) rfl
    let partner := if (e t).1 = .neutralCore 0 then (e t).2 else (e t).1
    have hub (n) (hn : t ≤ n) : prefixEdges e n (.neutralCore 0) partner := by
      have mem : e t ∈ (List.range (n+1)).map e := List.mem_map.mpr ⟨t,by simp; omega,rfl⟩
      dsimp [partner]
      split
      next he => exact .inl (he ▸ mem)
      next he =>
        have he' := ht.resolve_left he
        exact .inr (he' ▸ mem)
    let j := match partner with | .partner _ i => i | _ => 0
    obtain ⟨u,hu⟩ := covers (.neutralCore (j+1)) rfl
    refine ⟨max t u,fun n hn => good n ?_⟩
    obtain ⟨r,hr⟩ := largeFresh ((List.range (n+1)).map e)
    by_cases a0 : consistent (.anchor false) (prefixEdges e n)
    · by_cases a1 : consistent (.anchor true) (prefixEdges e n)
      · have both (b : Bool) : consistent (.anchor b) (prefixEdges e n) := by cases b <;> assumption
        obtain ⟨s,i,eq⟩ := partnerType both (hub n (by omega))
        have ji : j = i := by simp [j,eq]
        obtain ⟨_,_,hy⟩ := persists (n := n) (by omega) hu
        have miss := missingSatellite both hy
        apply survivingBlock (s := s) (j := j) hr _ miss
        have h := hub n (by omega)
        rw [eq] at h
        rw [ji]
        exact h
      · exact missingAnchor hr a1
    · exact missingAnchor hr a0

theorem separation :
    (∀ h n, ∃ x y, n < rank x ∧ member h x ∧ n < rank y ∧ ¬ member h y) ∧
    generates ∧ ¬ compatible := by
  refine ⟨?_,generatorWorks,incompatible⟩
  intro h n
  cases h with
  | anchor b =>
    exact ⟨.neutralCore (n+1),.partner b (n+1),by simp [rank,member]⟩
  | satellite b j =>
    exact ⟨.anchorPart false true (n+1),.anchorPart false false (n+1),by simp [rank,member]⟩

end PositiveWitness
