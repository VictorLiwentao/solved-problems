module

public import SolvedProblems.ProgressModel

public section

namespace Progress
open GenerationThreshold (Edge)

private theorem nodup (h : Support) (s : List Edge) : (seen h s).Nodup := by
  induction s with
  | nil => simp [seen]
  | cons e s ih =>
    cases hpos : positive h e with
    | none => simpa [seen,hpos] using ih
    | some x =>
      by_cases mem : x ∈ seen h s <;> simp [seen,hpos,List.insert,mem,ih]

private theorem add_some (h : Support) (s : List Edge) {e x} (pos : positive h e = some x) :
    surplus h s ≤ surplus h (e :: s) := by
  by_cases mem : x ∈ seen h s <;>
    simp [surplus, seen, corrupt, pos, List.insert, mem] <;> omega

private theorem add_fresh (h : Support) (s : List Edge) {e x} (pos : positive h e = some x)
    (new : x ∉ seen h s) : surplus h s + 1 ≤ surplus h (e :: s) := by
  simp [surplus, seen, corrupt, pos, List.insert, new]
  omega

private theorem add_any (h : Support) (s : List Edge) (e : Edge) :
    surplus h s + (-1) ≤ surplus h (e :: s) := by
  cases eq : positive h e with
  | some x => have := add_some h s eq; omega
  | none => simp [surplus,seen,corrupt,eq]; omega

private theorem rivals {h g : Support} (apart : disjointHoles h g)
    (holes : List Nat) (bound : ∀ x, g x = false → x ∈ holes) (s : List Edge) :
    (seen h s).length ≤ holes.length + corrupt g s := by
  -- Keep one positive per rival violation. A true-positive absent from this
  -- list must be a rival hole, since the other endpoint belongs to the rival.
  let bad := fun e : Edge => if (positive g e).isNone then positive h e else none
  have num (ss : List Edge) : (ss.filterMap bad).length ≤ corrupt g ss := by
    induction ss with
    | nil => simp [corrupt]
    | cons e ss ih =>
      cases G : positive g e <;> cases H : positive h e <;> simp_all [bad,corrupt] <;> omega
  have sub (ss : List Edge) : ∀ x ∈ seen h ss, x ∈ holes ++ ss.filterMap bad := by
    induction ss with
    | nil => simp [seen]
    | cons e ss ih =>
      intro x mem
      by_cases old : x ∈ seen h ss
      · rcases List.mem_append.mp (ih _ old) with hh | hh
        · simp [hh]
        · exact List.mem_append_right _ (List.mem_filterMap.mpr (by
            obtain ⟨v,hv,eq⟩ := List.mem_filterMap.mp hh
            exact ⟨v,by simp [hv],eq⟩))
      · cases H : positive h e with
        | none => simp [seen,H,old] at mem
        | some y =>
          have xy : x = y := by simpa [seen,H,old] using mem
          subst y
          cases G : positive g e with
          | none => exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨e,by simp,by simp [bad,G,H]⟩)
          | some y =>
            apply List.mem_append_left _ (bound _ ?_)
            have alo := apart e.lo
            have ahi := apart e.hi
            unfold positive at G H
            cases hl : h e.lo <;> cases hr : h e.hi <;>
              cases gl : g e.lo <;> cases gr : g e.hi <;> simp_all
  have le := (nodup h s).length_le_of_subset (l₂ := holes ++ s.filterMap bad) (fun x hx => sub s x hx)
  simp only [List.length_append] at le
  have := num s
  omega

private theorem leastScore (P : Nat → Prop) (ex : ∃ i, P i) :
    ∃ i, P i ∧ ∀ j, P j → i ≤ j := by
  classical
  obtain ⟨i,hi⟩ := ex
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases lower : ∃ k < i, P k
    · obtain ⟨k,hk,hp⟩ := lower
      exact ih k hk hp
    · exact ⟨i,hi,fun j hj => Nat.le_of_not_gt (fun lt => lower ⟨j,lt,hj⟩)⟩

private theorem sufficient (C : Collection) (inh : ∃ h, C h)
    (finite : ∀ h, C h → finiteHoles h)
    (apart : ∀ h, C h → ∀ g, C g → h ≠ g → disjointHoles h g) : identifiable C := by
  classical
  let holes (h : Support) := if hh : C h then (finite h hh).choose else []
  let score (h : Support) (s : List Edge) := corrupt h s + (holes h).length
  have best (s) : ∃ g, C g ∧ ∀ h, C h → score g s ≤ score h s := by
    obtain ⟨h,hh⟩ := inh
    obtain ⟨i,⟨g,hg,eq⟩,small⟩ := leastScore (fun i => ∃ g, C g ∧ score g s = i)
      ⟨_,h,hh,rfl⟩
    exact ⟨g,hg,fun h hh => eq ▸ small _ ⟨h,hh,rfl⟩⟩
  refine ⟨fun s => (best s).choose, ?_⟩
  intro h hh s legalS
  obtain ⟨N,late⟩ := legalS.2 ((holes h).length + 1)
  refine ⟨N,fun n hn => ?_⟩
  let t := history s n
  let g := (best t).choose
  have hg : C g := (best t).choose_spec.1
  have cmp := (best t).choose_spec.2 h hh
  change g = h
  apply Classical.byContradiction
  intro ne
  have bound := rivals (g := g) (apart _ hh _ hg (Ne.symm ne)) (holes g)
    (by simpa only [holes, dite_eq_left hg] using (finite g hg).choose_spec) t
  have gap := late n hn
  change (↑((holes h).length+1) : Int) ≤ (seen h t).length - (corrupt h t : Int) at gap
  change corrupt g t + (holes g).length ≤ corrupt h t + (holes h).length at cmp
  omega

/-- Infinitely many first-cut positives can occur in an observation honest for both. -/
private def common (h g : Support) :=
  ∀ b, ∃ x > b, ∃ e : Edge, positive h e = some x ∧ (positive g e).isSome

private def pair (x y : Nat) (ne : x ≠ y) : Edge :=
  if lt : x < y then ⟨x,y,lt⟩ else ⟨y,x,by omega⟩

private theorem pairPositive {h : Support} {x y} (hx : h x = true) (hy : h y = false) :
    ∃ e : Edge, positive h e = some x ∧ (e.lo = x ∧ e.hi = y ∨ e.lo = y ∧ e.hi = x) := by
  have ne : x ≠ y := by grind
  refine ⟨pair x y ne,?_⟩
  unfold pair
  split <;> simp [positive,hx,hy]

private theorem maxBound (l : List Nat) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih x hm) (Nat.le_max_right ..)

private def gainH (n : Nat) : Int :=
  if n%8 < 4 then 1 else if n%8 = 4 then 0 else -1
private def gainG (n : Nat) : Int :=
  if n%8 < 4 then 0 else if n%8 = 4 then -1 else if n%8 < 7 then 1 else 0

private def stageOK (h g : Support) (n : Nat) (s : List Edge) (e : Edge) :=
  surplus h s + gainH n ≤ surplus h (e::s) ∧
  surplus g s + gainG n ≤ surplus g (e::s) ∧
  (n%8 = 4 → h (n/8) = true → positive h e = some (n/8)) ∧
  (n%8 = 7 → g (n/8) = true → positive g e = some (n/8))

private theorem nextExists {h g : Support} (infH : infiniteSupport h)
    (infG : infiniteSupport g) (properH : proper h) (properG : proper g)
    (many : common h g) (n : Nat) (s : List Edge) : ∃ e, stageOK h g n s e := by
  obtain ⟨nh,hnh⟩ := properH
  obtain ⟨ng,hng⟩ := properG
  have designated {p : Support} (inf : infiniteSupport p) {neg} (hn : p neg = false) :
      ∃ e : Edge, (positive p e).isSome ∧
        (p (n/8) = true → positive p e = some (n/8)) := by
    cases test : p (n/8) with
    | true =>
      obtain ⟨e,ep,_⟩ := pairPositive test hn
      exact ⟨e,by simp [ep],fun _ => ep⟩
    | false =>
      obtain ⟨x,_,hx⟩ := inf 0
      obtain ⟨e,ep,_⟩ := pairPositive hx hn
      exact ⟨e,by simp [ep],by simp⟩
  by_cases a : n%8 < 4
  · obtain ⟨x,above,e,ep,eg⟩ := many ((seen h s).foldr max 0)
    obtain ⟨y,ey⟩ := Option.isSome_iff_exists.mp eg
    refine ⟨e,?_,?_,by omega,by omega⟩
    · simpa [gainH,a] using add_fresh h s ep (fun hm => by have := maxBound _ _ hm; omega)
    · simpa [gainG,a] using add_some g s ey
  by_cases b : n%8 = 4
  · obtain ⟨e,ok,cov⟩ := designated infH hnh
    obtain ⟨x,ep⟩ := Option.isSome_iff_exists.mp ok
    refine ⟨e,?_,?_,fun _ => cov,by omega⟩
    · simpa [gainH,b] using add_some h s ep
    · simpa [gainG,b] using add_any g s e
  by_cases c : n%8 < 7
  · obtain ⟨y,above,hy⟩ := infG ((seen g s).foldr max 0)
    obtain ⟨e,ep,_⟩ := pairPositive hy hng
    refine ⟨e,?_,?_,by omega,by omega⟩
    · simpa [gainH,a,b] using add_any h s e
    · simpa [gainG,a,b,c] using add_fresh g s ep (fun hm => by have := maxBound _ _ hm; omega)
  · obtain ⟨e,ok,cov⟩ := designated infG hng
    obtain ⟨y,ep⟩ := Option.isSome_iff_exists.mp ok
    refine ⟨e,?_,?_,by omega,fun _ => cov⟩
    · simpa [gainH,a,b] using add_any h s e
    · simpa [gainG,a,b,c] using add_some g s ep

private def potentialH (n : Nat) : Int := ((n/8 : Nat) : Int) +
  (if n%8 < 5 then ((n%8 : Nat) : Int) else (9 : Int) - (n%8 : Nat))
private def potentialG (n : Nat) : Int := ((n/8 : Nat) : Int) +
  (if n%8 = 5 then (-1 : Int) else if n%8 = 7 then 1 else 0)

private theorem increments (n : Nat) :
    potentialH (n+1) = potentialH n + gainH n ∧
    potentialG (n+1) = potentialG n + gainG n := by
  have opts : n%8 = 0 ∨ n%8 = 1 ∨ n%8 = 2 ∨ n%8 = 3 ∨
      n%8 = 4 ∨ n%8 = 5 ∨ n%8 = 6 ∨ n%8 = 7 := by omega
  rcases opts with h|h|h|h|h|h|h|h
  all_goals
    simp [potentialH,potentialG,gainH,gainG,Nat.add_mod n 1,h] <;> omega

private theorem commonStream {h g : Support} (ih : infiniteSupport h) (ig : infiniteSupport g)
    (ph : proper h) (pg : proper g) (many : common h g) :
    ∃ s, legal h s ∧ legal g s := by
  let step n s := (nextExists ih ig ph pg many n s).choose
  let prefixAt : Nat → List Edge := Nat.rec ([] : List Edge) (fun n s => step n s :: s)
  let stream n := step n (prefixAt n)
  have nextHistory (n) : history stream (n+1) = stream n :: history stream n := rfl
  have eq (n) : history stream n = prefixAt n := by
    induction n with
    | zero => rfl
    | succ n ind => rw [nextHistory, ind]
  have ok (n) : stageOK h g n (history stream n) (stream n) := by
    rw [eq]
    exact (nextExists ih ig ph pg many n (prefixAt n)).choose_spec
  have lower (n) : potentialH n ≤ surplus h (history stream n) ∧
      potentialG n ≤ surplus g (history stream n) := by
    induction n with
    | zero => exact ⟨Int.le_refl _,Int.le_refl _⟩
    | succ n ind =>
      have ⟨dh,dg,_,_⟩ := ok n
      have ⟨eh,eg⟩ := increments n
      rw [nextHistory, eh, eg]
      omega
  refine ⟨stream,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro x hx
    have := (ok (8*x+4)).2.2.1 (by omega)
    rw [show (8*x+4)/8 = x by omega] at this
    exact ⟨_,this hx⟩
  · intro b
    refine ⟨8*(b+1),fun n late => ?_⟩
    have := (lower n).1
    unfold potentialH at this
    split at this <;> omega
  · intro x hx
    have := (ok (8*x+7)).2.2.2 (by omega)
    rw [show (8*x+7)/8 = x by omega] at this
    exact ⟨_,this hx⟩
  · intro b
    refine ⟨8*(b+1),fun n late => ?_⟩
    have := (lower n).2
    unfold potentialG at this
    split at this
    · omega
    · split at this <;> omega

private theorem opposite {h g : Support} {x y : Nat} (hx : h x = true) (hy : h y = false)
    (diff : g x ≠ g y) : ∃ e : Edge, positive h e = some x ∧ (positive g e).isSome := by
  obtain ⟨e,ok,orientation⟩ := pairPositive hx hy
  refine ⟨e,ok,?_⟩
  rcases orientation with ⟨lo,hi⟩ | ⟨lo,hi⟩ <;>
    cases gx : g x <;> cases gy : g y <;> simp_all [positive]

/-- With a shared hole, either the intersection is unbounded, or each support
has an unbounded exclusive part. Both cases give common honest pairs. -/
private theorem overlap {h g : Support} (ih : infiniteSupport h) (ig : infiniteSupport g)
    (shared : ∃ z, h z = false ∧ g z = false) : common h g := by
  classical
  obtain ⟨z,hn,gn⟩ := shared
  by_cases both : ∀ b, ∃ x > b, h x = true ∧ g x = true
  · intro b
    obtain ⟨x,lt,hx,gx⟩ := both b
    exact ⟨x,lt,opposite hx hn (by simp [gx,gn])⟩
  · have limit : ∃ b, ∀ x > b, h x = true → g x = false := by
      apply Classical.byContradiction
      intro no
      apply both
      intro b
      apply Classical.byContradiction
      intro miss
      apply no
      refine ⟨b,fun x lt hx => ?_⟩
      cases gx : g x <;> simp_all
    obtain ⟨b,after⟩ := limit
    obtain ⟨y,ly,gy⟩ := ig b
    have hy : h y = false := by
      cases eq : h y <;> simp_all
    intro n
    obtain ⟨x,lx,hx⟩ := ih (max b n)
    have gx := after x (by omega) hx
    exact ⟨x,by omega,opposite hx hy (by simp [gx,gy])⟩

private theorem necessary (C : Collection) (multi : ∃ a b, C a ∧ C b ∧ a ≠ b)
    (inf : ∀ h, C h → infiniteSupport h) (prop : ∀ h, C h → proper h)
    (success : identifiable C) :
    (∀ h, C h → finiteHoles h) ∧
      (∀ h, C h → ∀ g, C g → h ≠ g → disjointHoles h g) := by
  classical
  obtain ⟨L,ok⟩ := success
  have avoid (h g : Support) (hh : C h) (hg : C g) (ne : h ≠ g) : ¬ common h g := by
    intro bad
    obtain ⟨s,sh,sg⟩ := commonStream (inf h hh) (inf g hg) (prop h hh) (prop g hg) bad
    obtain ⟨a,lockH⟩ := ok h hh s sh
    obtain ⟨b,lockG⟩ := ok g hg s sg
    exact ne ((lockH (max a b) (by omega)).symm.trans (lockG _ (by omega)))
  have apart (h) (hh : C h) (g) (hg : C g) (ne : h ≠ g) : disjointHoles h g := by
    intro x hx
    cases gx : g x with
    | true => rfl
    | false => exact False.elim (avoid h g hh hg ne (overlap (inf _ hh) (inf _ hg) ⟨x,hx,gx⟩))
  refine ⟨?_,apart⟩
  intro h hh
  obtain ⟨a,b,ha,hb,ab⟩ := multi
  have other : ∃ g, C g ∧ g ≠ h := by
    by_cases eq : a = h
    · exact ⟨b,hb,eq ▸ Ne.symm ab⟩
    · exact ⟨a,ha,eq⟩
  obtain ⟨g,hg,ne⟩ := other
  obtain ⟨y,gy⟩ := prop g hg
  have hy := apart g hg h hh ne y gy
  apply Classical.byContradiction
  intro infinite
  apply avoid g h hg hh ne
  intro b
  have ex : ∃ x > b, h x = false := by
    apply Classical.byContradiction
    intro no
    apply infinite
    exact ⟨List.range (b+1),fun x hx => List.mem_range.mpr
      (by apply Nat.lt_succ_of_le; exact Nat.le_of_not_gt (fun lt => no ⟨x,lt,hx⟩))⟩
  obtain ⟨x,hx,hn⟩ := ex
  have gx := apart h hh g hg (Ne.symm ne) x hn
  exact ⟨x,hx,opposite gx gy (by simp [hn,hy])⟩

/-- The progress-minus-corruption characterization. No bound on hole sizes
across targets is required. The score argument also works on uncountable
collections when the learner can output the support itself. -/
theorem identificationCriterion (C : Collection)
    (multi : ∃ a b, C a ∧ C b ∧ a ≠ b)
    (inf : ∀ h, C h → infiniteSupport h) (prop : ∀ h, C h → proper h) :
    identifiable C ↔ (∀ h, C h → finiteHoles h) ∧
      (∀ h, C h → ∀ g, C g → h ≠ g → disjointHoles h g) := by
  refine ⟨necessary C multi inf prop,?_⟩
  rintro ⟨finite,apart⟩
  obtain ⟨a,_,ha,_,_⟩ := multi
  exact sufficient C ⟨a,ha⟩ finite apart

end Progress

namespace Progress
open GenerationThreshold (Edge)

/-- The formulation for an explicitly indexed countable class from the paper.
Different indices may denote the same support. -/
theorem indexedCriterion (H : Nat → Support) (multi : ∃ i j, H i ≠ H j)
    (inf : ∀ i, infiniteSupport (H i)) (prop : ∀ i, proper (H i)) :
    indexedIdentifiable H ↔ (∀ i, finiteHoles (H i)) ∧
      (∀ i j, H i ≠ H j → disjointHoles (H i) (H j)) := by
  classical
  let C (h : Support) := ∃ i, H i = h
  obtain ⟨a,b,ab⟩ := multi
  have sc := identificationCriterion C ⟨H a,H b,⟨a,rfl⟩,⟨b,rfl⟩,ab⟩
    (fun _ ⟨i,eq⟩ => eq ▸ inf i) (fun _ ⟨i,eq⟩ => eq ▸ prop i)
  constructor
  · rintro ⟨L,ok⟩
    have semantic : identifiable C :=
      ⟨fun s => H (L s),fun _ ⟨i,eq⟩ => eq ▸ ok i⟩
    obtain ⟨finite,apart⟩ := sc.mp semantic
    exact ⟨fun i => finite _ ⟨i,rfl⟩, fun i j => apart _ ⟨i,rfl⟩ _ ⟨j,rfl⟩⟩
  · rintro ⟨finite,apart⟩
    obtain ⟨L,ok⟩ := sc.mpr ⟨fun _ ⟨i,eq⟩ => eq ▸ finite i,by
      rintro h ⟨i,rfl⟩ g ⟨j,rfl⟩
      exact apart i j⟩
    let decoder (h : Support) := if m : C h then m.choose else 0
    refine ⟨fun s => decoder (L s),?_⟩
    intro i s hs
    obtain ⟨N,stop⟩ := ok (H i) ⟨i,rfl⟩ s hs
    refine ⟨N,fun n hn => ?_⟩
    change H (decoder (L (history s n))) = H i
    rw [stop n hn]
    have mem : C (H i) := ⟨i,rfl⟩
    simpa only [decoder,dite_eq_left mem] using mem.choose_spec

end Progress
