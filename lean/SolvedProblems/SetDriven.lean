module

public import SolvedProblems.SetDrivenModel

public section

namespace SetDriven
open GenerationThreshold

private abbrev inside (s : List Edge) (P : Edges) := ∀ x ∈ s, P x
private abbrev ever (e : Nat → Edge) : Edges := fun x => ∃ k, e k = x
private abbrev late (Q : Nat → Prop) := ∃ N, ∀ n ≥ N, Q n

private theorem memObs {e n x} : x ∈ obs e n ↔ ∃ k < n, e k = x := by simp [obs]

private theorem finiteLate {xs : List α} {Q : α → Nat → Prop}
    (h : ∀ x ∈ xs, late (Q x)) : late (fun n => ∀ x ∈ xs, Q x n) := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons x xs ih =>
    obtain ⟨m,hm⟩ := h x (by simp)
    obtain ⟨s,hs⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨max m s,fun n hn y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hm n (by omega)
    · exact hs n (by omega) y hy

private theorem reaches {e : Nat → Edge} {s} (h : inside s (ever e)) :
    late (fun n => inside s (content (obs e n))) := by
  apply finiteLate
  intro x hx
  obtain ⟨k,rfl⟩ := h x hx
  exact ⟨k+1,fun n hn => memObs.mpr ⟨k,by omega,rfl⟩⟩

private theorem subsetEver {e n} : inside (obs e n) (ever e) :=
  fun _ h => let ⟨k,_,hk⟩ := memObs.mp h; ⟨k,hk⟩

private theorem realize (s : Nat → List Edge)
    (step : ∀ n, (s n).IsPrefix (s (n+1))) (long : ∀ n, n ≤ (s n).length) :
    ∃ e, ∀ n, obs e (s n).length = s n := by
  have mono {i j : Nat} (h : i ≤ j) : (s i).IsPrefix (s j) := by
    induction h with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (step _)
  let e := fun k => (s (k+1))[k]'(by have := long (k+1); omega)
  refine ⟨e, fun n => ?_⟩
  apply List.ext_getElem
  · simp [obs]
  · intro k hk hs
    simp [obs]
    exact ((mono (Nat.le_max_left (k+1) n)).getElem (by have := long (k+1); omega)).trans
      ((mono (Nat.le_max_right (k+1) n)).getElem hs).symm

/-- A locking extension exists over the actual edge alphabet after every honest prefix. -/
private theorem lockExists {G H j} (win : succeeds H G) {e : Nat → Edge}
    (he : present (H j) e) {s} (hs : inside s (ever e)) :
    ∃ u, inside u (ever e) ∧ ∀ v, inside v (ever e) →
      good (H j) ((s ++ u) ++ v) (G ((s ++ u) ++ v)) := by
  classical
  apply Classical.byContradiction
  intro no
  have bad (u) (hu : inside u (ever e)) :
      ∃ v, inside v (ever e) ∧ ¬good (H j) ((s ++ u) ++ v) (G ((s ++ u) ++ v)) := by
    apply Classical.byContradiction
    intro none
    exact no ⟨u,hu,fun v hv => Classical.byContradiction fun h => none ⟨v,hv,h⟩⟩
  let move (k) (t : {u // inside u (ever e)}) :=
    bad (t.val ++ [e k]) (by
      intro x hx
      rcases List.mem_append.mp hx with h|h
      · exact t.property x h
      · exact ⟨k,by simpa [eq_comm] using h⟩)
  let stages : Nat → {u // inside u (ever e)} := Nat.rec ⟨[],by intro p hp; simp at hp⟩
    (fun k t => ⟨(t.val ++ [e k]) ++ (move k t).choose,by
      intro x hx
      rcases List.mem_append.mp hx with h|h
      · rcases List.mem_append.mp h with ht|he
        · exact t.property x ht
        · exact ⟨k,by simpa [eq_comm] using he⟩
      · exact (move k t).choose_spec.1 x h⟩)
  let path (n) := s ++ (stages n).val
  have grow (n) : (path n ++ [e n]).IsPrefix (path (n+1)) := by
    exact ⟨(move n (stages n)).choose, by simp [path,stages,List.append_assoc]⟩
  have long (n) : n ≤ (path n).length := by
    induction n with
    | zero => omega
    | succ n ih => have h := (grow n).length_le; simp at h; omega
  obtain ⟨v,agree⟩ := realize path (fun n => (List.prefix_append ..).trans (grow n)) long
  have legal : present (H j) v := by
    constructor
    · intro k
      have hm : v k ∈ path (k+1) := by
        rw [← agree (k+1)]
        exact memObs.mpr ⟨k,by have := long (k+1); omega,rfl⟩
      obtain ⟨i,hi⟩ : ever e (v k) := (List.mem_append.mp hm).elim (hs _) ((stages (k+1)).property (v k))
      rw [← hi]
      exact he.1 i
    · intro x hx
      obtain ⟨k,hk⟩ := he.2 x hx
      have hm := (grow k).sublist.subset (a := e k) (by simp)
      rw [← agree (k+1)] at hm
      obtain ⟨i,_,hi⟩ := memObs.mp hm
      exact ⟨i,hi ▸ hk⟩
  obtain ⟨N,hN⟩ := win j v legal
  have ok := hN (path (N+1)).length (by have := long (N+1); omega)
  rw [agree (N+1)] at ok
  apply (move N (stages N)).choose_spec.2
  simpa [path,stages,List.append_assoc] using ok

/-- At priority j the virtual history can skip an inconsistent target or one
with a missing positive. Otherwise it appends a locking extension for j.
Every fixed certificate eventually has the same truth value on growing
observations as on their union (see `stableValid`). -/
private inductive Certificate where
  | rejects (edge : Edge)
  | missing (positive : Nat)
  | lock (extra : List Edge)

/-- Code certificates by natural numbers so that a chosen certificate has
only finitely many predecessors to check for stabilization. -/
private def pairCode : Nat → Nat → Nat
  | 0,b => 2*b+1
  | a+1,b => 2*pairCode a b+2

private theorem pair_inj {a b c d} (h : pairCode a b = pairCode c d) : a=c ∧ b=d := by
  induction a generalizing c with
  | zero => cases c <;> simp [pairCode] at * <;> omega
  | succ a ih =>
    cases c with
    | zero => simp [pairCode] at h; omega
    | succ c =>
      have eq : pairCode a b = pairCode c d := by simp [pairCode] at h; omega
      obtain ⟨rfl,rfl⟩ := ih eq
      exact ⟨rfl,rfl⟩

private def edgeCode (p : Edge) := pairCode p.lo p.hi
private theorem edge_inj {p q} (eq : edgeCode p = edgeCode q) : p = q := by
  obtain ⟨a,b⟩ := pair_inj eq
  cases p; cases q; congr

private def listCode : List Edge → Nat
  | [] => 0
  | p::s => pairCode (edgeCode p) (listCode s) + 1
private theorem list_inj {s t} (eq : listCode s = listCode t) : s=t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all [listCode]
  | cons p s ih =>
    cases t with
    | nil => simp [listCode] at eq
    | cons q t =>
      obtain ⟨hp,ht⟩ := pair_inj (Nat.succ.inj eq)
      rw [edge_inj hp, ih ht]

private def code : Certificate → Nat
  | .rejects e => pairCode 0 (edgeCode e)
  | .missing x => pairCode 1 x
  | .lock s => pairCode 2 (listCode s)
private theorem code_inj {c d} (h : code c = code d) : c=d := by
  cases c <;> cases d <;> obtain ⟨eq,hv⟩ := pair_inj h <;> try contradiction
  · exact congrArg _ (edge_inj hv)
  · exact congrArg _ hv
  · exact congrArg _ (list_inj hv)
private noncomputable def decode (k : Nat) : Certificate := by
  classical exact if h : ∃ c, code c = k then h.choose else .missing 0
private theorem decode_code (c) : decode (code c) = c := by
  classical
  have h : ∃ d, code d = code c := ⟨c,rfl⟩
  exact code_inj (by simp [decode,h,h.choose_spec])

private def valid (H : Language) (G : Generator) (P : Edges) (s : List Edge) : Certificate → Prop
  | .rejects p => P p ∧ ¬crosses H p
  | .missing x => H x ∧ ∀ p, P p → ¬touches p x
  | .lock u => inside u P ∧ ∀ v, inside v P → good H (s++u++v) (G (s++u++v))

private theorem existsValid {H G} (win : succeeds H G) (j) (e : Nat → Edge) (s)
    (hs : inside s (ever e)) : ∃ c, valid (H j) G (ever e) s c := by
  classical
  by_cases r : ∃ k, ¬crosses (H j) (e k)
  · obtain ⟨k,hk⟩ := r
    exact ⟨.rejects (e k),⟨k,rfl⟩,hk⟩
  by_cases m : ∃ x, H j x ∧ ∀ k, ¬touches (e k) x
  · obtain ⟨x,hx,no⟩ := m
    exact ⟨.missing x,hx,fun _ ⟨k,hk⟩ => hk ▸ no k⟩
  have he : present (H j) e := by
    refine ⟨fun k => Classical.byContradiction fun h => r ⟨k,h⟩,fun x hx => ?_⟩
    exact Classical.byContradiction fun h => m ⟨x,hx,fun k hk => h ⟨k,hk⟩⟩
  obtain ⟨u,hu,lock⟩ := lockExists win he hs
  exact ⟨.lock u,hu,lock⟩

private theorem presenceStable (e : Nat → Edge) (p : Edge) :
    late (fun n => content (obs e n) p ↔ ever e p) := by
  by_cases h : ever e p
  · obtain ⟨k,rfl⟩ := h
    exact ⟨k+1,fun n hn => ⟨fun _ => ⟨k,rfl⟩,fun _ => memObs.mpr ⟨k,by omega,rfl⟩⟩⟩
  · exact ⟨0,fun _ _ => ⟨fun hm => subsetEver _ hm,fun he => False.elim (h he)⟩⟩

private theorem stableValid (H G e s c) :
    late (fun n => valid H G (content (obs e n)) s c ↔ valid H G (ever e) s c) := by
  classical
  cases c with
  | rejects p =>
    obtain ⟨N,hN⟩ := presenceStable e p
    exact ⟨N,fun n hn => and_congr_left fun _ => hN n hn⟩
  | missing x =>
    by_cases ex : ∃ p, ever e p ∧ touches p x
    · obtain ⟨p,hp,hit⟩ := ex
      obtain ⟨N,hN⟩ := presenceStable e p
      exact ⟨N,fun n hn => ⟨fun h => False.elim (h.2 p ((hN n hn).mpr hp) hit),
        fun h => False.elim (h.2 p hp hit)⟩⟩
    · have absent (p) (hp : ever e p) : ¬touches p x := fun hit => ex ⟨p,hp,hit⟩
      exact ⟨0,fun _ _ => ⟨fun h => ⟨h.1,absent⟩,fun h =>
        ⟨h.1,fun p hp => absent p (subsetEver p hp)⟩⟩⟩
  | lock u =>
    by_cases hu : inside u (ever e)
    · obtain ⟨N,hN⟩ := reaches hu
      by_cases ok : ∀ v, inside v (ever e) → good H (s++u++v) (G (s++u++v))
      · exact ⟨N,fun n hn => ⟨fun _ => ⟨hu,ok⟩,fun _ => ⟨hN n hn,fun v hv =>
          ok v (fun p hp => subsetEver p (hv p hp))⟩⟩⟩
      · have ex : ∃ v, inside v (ever e) ∧ ¬good H (s++u++v) (G (s++u++v)) := by
          apply Classical.byContradiction
          intro h
          exact ok (fun v hv => Classical.byContradiction fun f => h ⟨v,hv,f⟩)
        obtain ⟨v,hv,bad⟩ := ex
        obtain ⟨M,hM⟩ := reaches hv
        exact ⟨M,fun n hn => ⟨fun h => False.elim (bad (h.2 v (hM n hn))),
          fun h => False.elim (ok h.2)⟩⟩
    · exact ⟨0,fun _ _ => ⟨fun h => False.elim (hu (fun p hp => subsetEver p (h.1 p hp))),
        fun h => False.elim (hu h.1)⟩⟩

private theorem least {P : Nat → Prop} (ex : ∃ k, P k) :
    ∃ k, P k ∧ ∀ l, P l → k ≤ l := by
  classical
  obtain ⟨k,hk⟩ := ex
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : ∃ l < k, P l
    · obtain ⟨l,hl,hp⟩ := h
      exact ih l hl hp
    · exact ⟨k,hk,fun l hl => Nat.le_of_not_gt fun hlt => h ⟨l,hlt,hl⟩⟩

private noncomputable def select (P : Nat → Prop) : Certificate := by
  classical exact if h : ∃ i, P i then decode (least h).choose else .missing 0

private theorem selectStable {p : Nat → Prop} {q : Nat → Nat → Prop}
    (ex : ∃ k, p k) (stable : ∀ k, late fun n => q n k ↔ p k) :
    late fun n => select (q n) = select p := by
  classical
  let b := (least ex).choose
  have B := (least ex).choose_spec
  obtain ⟨N,hN⟩ := finiteLate (xs := List.range (b+1)) (fun i _ => stable i)
  refine ⟨N,fun n hn => ?_⟩
  have same (k) (hk : k ≤ b) := hN n hn k (List.mem_range.mpr (by omega))
  have qb := (same b (Nat.le_refl _)).mpr B.1
  have qex := Exists.intro b qb
  have Q := (least qex).choose_spec
  have small := Q.2 b qb
  have big := B.2 _ ((same _ small).mp Q.1)
  have eq : (least qex).choose = b := Nat.le_antisymm small big
  simp only [select, dite_eq_left qex, dite_eq_left ex, eq,b]

private def extension : Certificate → List Edge
  | .lock u => u
  | _ => []

private noncomputable def step (H : Family) (G : Generator) (j : Nat) (P : Edges)
    (s : List Edge) := select (fun k => valid (H j) G P s (decode k))

private theorem selected {H G j P s} (h : ∃ c, valid (H j) G P s c) :
    valid (H j) G P s (step H G j P s) := by
  classical
  obtain ⟨c,hc⟩ := h
  have ex : ∃ k, valid (H j) G P s (decode k) := ⟨code c, by simpa [decode_code] using hc⟩
  simpa [step,select,ex] using (least ex).choose_spec.1

private theorem extInside {H G j P s} : inside (extension (step H G j P s)) P := by
  classical
  by_cases ex : ∃ k, valid (H j) G P s (decode k)
  · obtain ⟨k,hk⟩ := ex
    have ok := selected (Exists.intro (decode k) hk)
    cases hs : step H G j P s with
    | lock u => rw [hs] at ok; exact ok.1
    | rejects p => simp [extension,inside]
    | missing p => simp [extension,inside]
  · simp [step,select,ex,extension,inside]

/-- Each priority extends one common virtual history. Once a priority has
locked a target, later priorities retain its entire history as a prefix. -/
private noncomputable def stage (H : Family) (G : Generator) (P : Edges) : Nat → List Edge
  | 0 => []
  | j+1 => let s := stage H G P j
           s ++ extension (step H G j P s)

private theorem stageInside (H G P j) : inside (stage H G P j) P := by
  induction j with
  | zero => simp [stage,inside]
  | succ j ih =>
    intro p hp
    exact (List.mem_append.mp hp).elim (ih p) (extInside p)

private theorem prefixStage (H G P) {j m : Nat} (le : j ≤ m) :
    (stage H G P j).IsPrefix (stage H G P m) := by
  induction le with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (List.prefix_append ..)

private theorem stageStable {H G} (win : succeeds H G) (e j) :
    late fun n => stage H G (content (obs e n)) j = stage H G (ever e) j := by
  classical
  induction j with
  | zero => exact ⟨0,fun _ _ => rfl⟩
  | succ j ih =>
    let s := stage H G (ever e) j
    obtain ⟨c,hc⟩ := existsValid win j e s (stageInside H G (ever e) j)
    have ex : ∃ k, valid (H j) G (ever e) s (decode k) :=
      ⟨code c,by simpa [decode_code] using hc⟩
    obtain ⟨M,hM⟩ := selectStable ex (fun k => stableValid (H j) G e s (decode k))
    obtain ⟨N,hN⟩ := ih
    refine ⟨max M N,fun n hn => ?_⟩
    simp only [stage,hN n (by omega)]
    rw [show step H G j (content (obs e n)) s = step H G j (ever e) s from hM n (by omega)]

private noncomputable def listing (P : Edges) : List Edge := by
  classical exact if h : ∃ s : List Edge, ∀ p, p ∈ s ↔ P p then h.choose else []

private theorem list_spec (s : List Edge) (p) : p ∈ listing (content s) ↔ p ∈ s := by
  classical
  have ex : ∃ u : List Edge, ∀ p, p ∈ u ↔ content s p := ⟨s,fun _ => Iff.rfl⟩
  simp only [listing, dite_eq_left ex]
  exact ex.choose_spec p

private def cap (s : List Edge) := s.foldr (fun p a => max p.hi a) 0

private theorem bound {s : List Edge} {p} (hp : p ∈ s) : p.hi ≤ cap s := by
  induction s with
  | nil => simp at hp
  | cons a s ih =>
    rcases List.mem_cons.mp hp with rfl | h
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

/-- An arbitrary successful deterministic generator can be replaced by a function
of the set of distinct observed edges. There is no effectiveness assumption. -/
theorem setDrivenGeneration (H : Family) (inf : ∀ j b, ∃ x > b, H j x) :
    (∃ G, succeeds H G) ↔ ∃ F : Edges → Nat, succeeds H (fun s => F (content s)) := by
  classical
  constructor
  · rintro ⟨G,win⟩
    -- The largest endpoint in the input tends to infinity on every legal
    -- stream. Appending a fixed listing at the end enforces actual freshness.
    let F (P : Edges) := G (stage H G P (cap (listing P)) ++ listing P)
    refine ⟨F,fun j e legal => ?_⟩
    let P := ever e
    let s := stage H G P j
    have sel := selected (existsValid win j e s (stageInside H G (ever e) j))
    have lock : ∀ v, inside v P →
        good (H j) (stage H G P (j+1) ++ v) (G (stage H G P (j+1) ++ v)) := by
      cases hs : step H G j P s with
      | lock u =>
        rw [hs] at sel
        simpa only [stage,show stage H G P j = s from rfl,hs,extension] using sel.2
      | rejects p =>
        rw [hs] at sel
        obtain ⟨k,hk⟩ := sel.1
        exact False.elim (sel.2 (hk ▸ legal.1 k))
      | missing x =>
        rw [hs] at sel
        obtain ⟨k,hk⟩ := legal.2 x sel.1
        exact False.elim (sel.2 _ ⟨k,rfl⟩ hk)
    obtain ⟨M,hM⟩ := stageStable win e (j+1)
    obtain ⟨x,hx,px⟩ := inf j j
    obtain ⟨k,hit⟩ := legal.2 x px
    refine ⟨max M (k+1),fun n hn => ?_⟩
    let E := content (obs e n)
    let u := listing E
    have hu : e k ∈ u := (list_spec _ _).mpr (memObs.mpr ⟨k,by omega,rfl⟩)
    have large : j+1 ≤ cap u := by
      have := bound hu
      have := (e k).ordered
      rcases hit with h|h <;> omega
    obtain ⟨rest,eq⟩ := prefixStage H G E large
    have small : stage H G E (j+1) = stage H G P (j+1) := hM n (by omega)
    rw [small] at eq
    have rr : inside rest P := by
      intro p hp
      apply subsetEver (e := e) (n := n)
      apply stageInside H G E (cap u)
      rw [← eq]
      exact List.mem_append_right _ hp
    have lu : inside u P := fun p hp => subsetEver p ((list_spec _ p).mp hp)
    have ok := lock (rest++u) (fun p hp => (List.mem_append.mp hp).elim (rr p) (lu p))
    rw [← List.append_assoc,eq] at ok
    refine ⟨ok.1,fun p hp => ok.2 p (List.mem_append_right _ ((list_spec _ _).mpr hp))⟩
  · exact fun ⟨F,win⟩ => ⟨_,win⟩


private theorem enumerate (P : Edges) (nonempty : ∃ p, P p) :
    ∃ e : Nat → Edge, ∀ p, ever e p ↔ P p := by
  classical
  let e (k : Nat) := match decode k with
    | .rejects p => if P p then p else nonempty.choose
    | _ => nonempty.choose
  refine ⟨e,fun p => ⟨?_,?_⟩⟩
  · rintro ⟨k,rfl⟩
    dsimp [e]
    split
    · split <;> first | assumption | exact nonempty.choose_spec
    all_goals exact nonempty.choose_spec
  · intro hp
    exact ⟨code (.rejects p),by simp [e,decode_code,hp]⟩

/-- Locking finite edge sets suffice exactly when every nonempty active family
shares a fresh positive. Witnesses may depend on the full honest edge set. -/
theorem witnessCriterion (H : Family) (inf : ∀ j b, ∃ x > b, H j x) :
    (∃ G, succeeds H G) ↔ compatibleWitnesses H := by
  classical
  constructor
  · intro solvable
    obtain ⟨F,hF⟩ := (setDrivenGeneration H inf).mp solvable
    let legal (j : Nat) (P : Edges) := (∀ p, P p → crosses (H j) p) ∧
      ∀ x, H j x → ∃ p, P p ∧ touches p x
    have lock (j P) (hp : legal j P) : ∃ u : List Edge, inside u P ∧
        ∀ s, inside s P → (∀ p ∈ u, p ∈ s) → good (H j) s (F (content s)) := by
      obtain ⟨x,_,hx⟩ := inf j 0
      obtain ⟨p,pp,_⟩ := hp.2 x hx
      obtain ⟨e,same⟩ := enumerate P ⟨p,pp⟩
      have pres : present (H j) e := by
        refine ⟨fun k => hp.1 _ ((same _).mp ⟨k,rfl⟩),fun x hx => ?_⟩
        obtain ⟨q,hq,touch⟩ := hp.2 x hx
        obtain ⟨k,hk⟩ := (same q).mpr hq
        exact ⟨k,hk ▸ touch⟩
      obtain ⟨u,hu,hlock⟩ := lockExists (s := []) hF pres (by intro q hq; simp at hq)
      refine ⟨u,fun q hq => (same q).mp (hu q hq),fun s hs cover => ?_⟩
      have ans := hlock s (fun q hq => (same q).mpr (hs q hq))
      simp only [List.nil_append] at ans
      have eq : content (u++s) = content s := by
        funext p
        exact propext ⟨fun hm => (List.mem_append.mp hm).elim (cover p) id,
          fun hm => List.mem_append_right _ hm⟩
      rw [eq] at ans
      exact ⟨ans.1,fun p hm => ans.2 p (List.mem_append_right _ hm)⟩
    let W (j P) := if h : legal j P then (lock j P h).choose else []
    refine ⟨W,?_,fun s => ⟨F (content s),?_⟩⟩
    · intro j P honest full
      have h : legal j P := ⟨honest,full⟩
      simpa only [W,dite_eq_left h] using (lock j P h).choose_spec.1
    · intro j P honest full inc hs
      have h : legal j P := ⟨honest,full⟩
      exact (lock j P h).choose_spec.2 s hs (by simpa only [W,dite_eq_left h] using inc)
  · rintro ⟨W,hW,safe⟩
    refine ⟨fun s => (safe s).choose,fun j e pres => ?_⟩
    let P := ever e
    have honest : ∀ p, P p → crosses (H j) p := fun p ⟨k,eq⟩ => eq ▸ pres.1 k
    have cover : ∀ x, H j x → ∃ p, P p ∧ touches p x := by
      intro x hx
      obtain ⟨k,hk⟩ := pres.2 x hx
      exact ⟨e k,⟨k,rfl⟩,hk⟩
    obtain ⟨N,hN⟩ := reaches (e := e) (hW j P honest cover)
    exact ⟨N,fun n hn => (safe _).choose_spec j P honest cover (hN n hn) subsetEver⟩

end SetDriven
