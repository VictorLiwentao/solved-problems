module

public import SolvedProblems.SetDensityModel
import SolvedProblems.Displacement

public section

namespace SetDensity
open Displacement

private theorem densityMono {A B : Output} {K p q} (sub : ∀ x, A x → B x)
    (good : AtLeast A K p q) : AtLeast B K p q := by
  intro a d hd less
  obtain ⟨R,hR⟩ := good a d hd less
  refine ⟨R,fun r hr => ?_⟩
  obtain ⟨w,nd,ok,bound⟩ := hR r hr
  exact ⟨w,nd,fun x hx => ⟨sub x (ok x hx).1, (ok x hx).2⟩,bound⟩

private theorem positiveInfinite {A : Output} {K p q} (good : AtLeast A K (p+1) (q+1))
    (f : List Nat) : ∃ x, A x ∧ x ∉ f := by
  classical
  have h : 1*(q+1) < (p+1)*(q+2) := by simp only [Nat.one_mul, Nat.succ_mul p]; omega
  obtain ⟨R,hR⟩ := good 1 (q+2) (by omega) h
  let r := max R ((q+2)*f.length+1)
  obtain ⟨w,nd,inside,large⟩ := hR r (Nat.le_max_left ..)
  apply Classical.byContradiction
  intro no
  have sub : w ⊆ f := fun x hx => Classical.byContradiction fun hn => no ⟨x,(inside x hx).1,hn⟩
  have := Nat.mul_le_mul_left (q+2) (nd.length_le_of_subset sub)
  have := Nat.le_max_right R ((q+2)*f.length+1)
  dsimp [r] at large
  simp only [Nat.one_mul] at large
  omega

private theorem necessity {L D level} (growth : ∀ t, t ≤ D t)
    {G} (good : Succeeds L D level G) : Witnesses L D level := by
  classical
  intro i b p q threshold
  let bad (J : Language) := (∃ j, J = L j) ∧ ¬ AtLeast J.Has (L i) (p+1) (q+1)
  obtain ⟨T,inside,h⟩ := lockingWitness growth (b+1) (K := L i) (bad := bad)
    (P := fun s => AtLeast (G s) (L i) (p+1) (q+1)) (fun e txt => (good.2 i e txt).2 p q threshold)
    (by
      rintro J ⟨⟨j,rfl⟩,sparse⟩ e txt
      obtain ⟨N,hN⟩ := (good.2 j e txt).1
      exact ⟨N, fun n hn dense => sparse (densityMono (hN n hn) dense)⟩)
  exact ⟨T, inside, fun j hj sub fits => Classical.byContradiction fun no =>
    h (L j) hj sub fits ⟨⟨j,rfl⟩,no⟩⟩

private structure Demand where
  i : Nat
  b : Nat
  p : Nat
  q : Nat
  deriving DecidableEq

private def batch (n : Nat) : List Demand :=
  let r := List.range (n+1)
  r.flatMap fun i => r.flatMap fun b => r.flatMap fun p => r.map fun q => ⟨i,b,p,q⟩

private def tasks : Nat → List Demand
  | 0 => batch 0
  | n+1 => tasks n ++ batch (n+1)

private theorem occurs (d : Demand) : ∃ k, d ∈ tasks k := by
  obtain ⟨i,b,p,q⟩ := d
  let k := i+b+p+q+1
  refine ⟨k, List.mem_append_right _ ?_⟩
  simp only [batch, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨i,by omega,b,by omega,p,by omega,q,by omega,rfl⟩

private theorem tasksPrefix {k n} (le : k ≤ n) : (tasks k).IsPrefix (tasks n) := by
  induction le with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (List.prefix_append ..)

private def Window (S : Output) (K : Language) (D : Nat → Nat) (t : Nat) :=
  ∃ w : List Nat, w.Nodup ∧ w.length = t ∧ (∀ x ∈ w, S x) ∧ ∀ x ∈ w, K.Has x ∧ x < K.word (D t)

private def Eligible (L : Nat → Language) (D : Nat → Nat) (level : Levels)
    (T : Demand → List Nat) (S : Output) (n : Nat) (d : Demand) :=
  level d.i (d.p+1) (d.q+1) ∧ (∀ x ∈ T d, S x) ∧ (∀ x, S x → (L d.i).Has x) ∧
    ∀ t, d.b+1 ≤ t → t ≤ n → Window S (L d.i) D t

private def Compatible (L : Nat → Language) (J : Language) (d : Demand) :=
  Sub J (L d.i) ∧ AtLeast J.Has (L d.i) (d.p+1) (d.q+1)

private theorem eventuallyCompatible {L D level} {T : Demand → List Nat}
    (tells : ∀ d, level d.i (d.p+1) (d.q+1) → ∀ j, Inside (T d) (L j) →
      Sub (L j) (L d.i) → Fits (L j) (L d.i) D (d.b+1) → AtLeast (L j).Has (L d.i) (d.p+1) (d.q+1))
    {j e} (txt : Text D (L j) e) (d : Demand) :
    ∃ N, ∀ n ≥ N, Eligible L D level T (fun x => x ∈ history e n) n d → Compatible L (L j) d := by
  classical
  by_cases sub : Sub (L j) (L d.i)
  · by_cases fit : Fits (L j) (L d.i) D (d.b+1)
    · exact ⟨0, fun n _ h => ⟨sub, tells d h.1 j (fun x hx => histInside txt n x (h.2.1 x hx)) sub fit⟩⟩
    · have misses : ∃ t, d.b+1 ≤ t ∧ ¬ Window (L j).Has (L d.i) D t := by
        exact Classical.byContradiction fun no => fit (fun t ht => Classical.byContradiction
          fun bad => no ⟨t, ht, bad⟩)
      obtain ⟨t,ht,bad⟩ := misses
      refine ⟨t, fun n hn h => False.elim (bad ?_)⟩
      obtain ⟨w,nd,len,inside,cut⟩ := h.2.2.2 t ht hn
      exact ⟨w,nd,len,fun x hx => histInside txt n x (inside x hx),cut⟩
  · have misses : ∃ x, (L j).Has x ∧ ¬ (L d.i).Has x :=
      Classical.byContradiction fun no => sub (fun x hx => Classical.byContradiction fun h => no ⟨x,hx,h⟩)
    obtain ⟨x,hj,hi⟩ := misses
    obtain ⟨k,hk⟩ := (txt.2.1 x).mp hj
    exact ⟨k+1,fun n hn h => False.elim (hi (h.2.2.1 x (memHist.mpr ⟨k,by omega,hk⟩)))⟩

private theorem trueEligible {L D level} {T : Demand → List Nat}
    (own : ∀ d, level d.i (d.p+1) (d.q+1) → Inside (T d) (L d.i))
    (mono : ∀ i j, i ≤ j → D i ≤ D j) (growth : ∀ t, t ≤ D t)
    {j e} (txt : Text D (L j) e) {p q} (target : level j (p+1) (q+1)) :
    ∃ d : Demand, d.i = j ∧ d.p = p ∧ d.q = q ∧
      ∃ N, ∀ n ≥ N, Eligible L D level T (fun x => x ∈ history e n) n d := by
  obtain ⟨b',pos,hb⟩ := eventualPrefixDeadlines mono growth txt
  let d : Demand := ⟨j,b'-1,p,q⟩
  obtain ⟨N,hN⟩ := seen txt (own d target)
  refine ⟨d,rfl,rfl,rfl,N, fun n hn => ⟨target,fun _ hx => hN _ hn hx,histInside txt n,?_⟩⟩
  intro t ht le
  refine ⟨history e t,nodupHist txt.1 _,by simp [history],?_,?_⟩
  · intro x hx
    obtain ⟨k,hk,eq⟩ := memHist.mp hx
    exact memHist.mpr ⟨k,by omega,eq⟩
  · exact fun x hx => ⟨histInside txt t x hx,hb t (by dsimp [d] at ht; omega) x hx⟩

private def common (L : Nat → Language) (picked : List Demand) : Output :=
  fun x => ∀ d ∈ picked, (L d.i).Has x

private def meets (L : Nat → Language) (picked : List Demand) :=
  ∀ d ∈ picked, AtLeast (common L picked) (L d.i) (d.p+1) (d.q+1)

private noncomputable def insertIf (L : Nat → Language) (eligible : Demand → Prop)
    (picked : List Demand) (d : Demand) : List Demand := by
  classical exact if eligible d ∧ meets L (d::picked) then d::picked else picked

private theorem scanValid {L eligible} (ds ps : List Demand) (ok : meets L ps) :
    meets L (ds.foldl (insertIf L eligible) ps) := by
  classical
  induction ds generalizing ps with
  | nil => exact ok
  | cons d ds ih =>
    apply ih
    unfold insertIf
    split <;> rename_i h
    · exact h.2
    · exact ok

private theorem scanKeeps {L eligible} (ds ps : List Demand) :
    ps ⊆ ds.foldl (insertIf L eligible) ps := by
  classical
  induction ds generalizing ps with
  | nil => exact fun _ h => h
  | cons d ds ih =>
    intro x h
    apply ih
    unfold insertIf
    split
    · exact List.mem_cons_of_mem _ h
    · exact h

private theorem scanChosen {L eligible} (ds ps : List Demand) {x : Demand}
    (h : x ∈ ds.foldl (insertIf L eligible) ps) : x ∈ ps ∨ x ∈ ds ∧ eligible x := by
  classical
  induction ds generalizing ps with
  | nil => exact Or.inl h
  | cons d ds ih =>
    rcases ih (insertIf L eligible ps d) h with picked | ⟨mem,ok⟩
    · unfold insertIf at picked
      split at picked
      · rename_i added
        rcases List.mem_cons.mp picked with rfl | prior
        · exact Or.inr ⟨by simp,added.1⟩
        · exact Or.inl prior
      · exact Or.inl picked
    · exact Or.inr ⟨List.mem_cons_of_mem _ mem,ok⟩

private theorem forceEntry {L eligible} {d : Demand} {pre post : List Demand}
    (yes : eligible d)
    (safe : ∀ x ∈ pre ++ [d], eligible x → Compatible L (L d.i) x) :
    d ∈ (pre ++ d::post).foldl (insertIf L eligible) [] := by
  classical
  let picked := pre.foldl (insertIf L eligible) []
  have comp (x) (hx : x ∈ d::picked) : Compatible L (L d.i) x := by
    rcases List.mem_cons.mp hx with rfl | mem
    · exact safe x (by simp) yes
    · rcases scanChosen pre [] mem with h | ⟨h,ok⟩
      · simp at h
      · exact safe x (List.mem_append_left _ h) ok
  have pass : meets L (d::picked) := fun x hx =>
    densityMono (fun y hy z hz => (comp z hz).1 y hy) (comp x hx).2
  have inserted : insertIf L eligible picked d = d::picked := by simp [insertIf,yes,pass]
  rw [List.foldl_append]
  change d ∈ post.foldl _ (insertIf L eligible picked d)
  rw [inserted]
  exact scanKeeps post (d::picked) (by simp)

private theorem eventuallyList {P : Demand → Nat → Prop} (ds : List Demand)
    (one : ∀ d, ∃ N, ∀ n ≥ N, P d n) :
    ∃ N, ∀ n ≥ N, ∀ d ∈ ds, P d n := by
  induction ds with
  | nil => exact ⟨0,by simp⟩
  | cons d ds ih =>
    obtain ⟨A,hA⟩ := one d
    obtain ⟨B,hB⟩ := ih
    refine ⟨max A B, fun n hn x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | h
    · exact hA n (by omega)
    · exact hB n (by omega) x h

private def repr (S : Output) (l : List Nat) := l.Nodup ∧ ∀ x, S x ↔ x ∈ l

private noncomputable def size (S : Output) : Nat := by
  classical exact if h : ∃ l, repr S l then h.choose.length else 0

private theorem sizeHistory {L D e} (txt : Text D L e) (n) : size (fun x => x ∈ history e n) = n := by
  classical
  let S (x) := x ∈ history e n
  have h : ∃ l, repr S l := ⟨history e n, nodupHist txt.1 n, fun _ => Iff.rfl⟩
  have left := h.choose_spec.1.length_le_of_subset (fun x hx => (h.choose_spec.2 x).mpr hx)
  have right := (nodupHist txt.1 n).length_le_of_subset (fun x hx => (h.choose_spec.2 x).mp hx)
  change size S = n
  simp [size,h]
  simp only [history,List.length_map,List.length_range] at left right
  omega

private noncomputable def picks (L D level T) (S : Output) :=
  (tasks (size S)).foldl (insertIf L (Eligible L D level T S (size S))) []

private theorem eventualPick {L D level} {T : Demand → List Nat}
    (own : ∀ d, level d.i (d.p+1) (d.q+1) → Inside (T d) (L d.i))
    (tells : ∀ d, level d.i (d.p+1) (d.q+1) → ∀ j, Inside (T d) (L j) →
      Sub (L j) (L d.i) → Fits (L j) (L d.i) D (d.b+1) → AtLeast (L j).Has (L d.i) (d.p+1) (d.q+1))
    (mono : ∀ i j, i ≤ j → D i ≤ D j) (growth : ∀ t, t ≤ D t)
    {j e} (txt : Text D (L j) e) {p q} (threshold : level j (p+1) (q+1)) :
    ∃ N, ∀ n ≥ N, ∃ d ∈ picks L D level T (fun x => x ∈ history e n), d.i=j ∧ d.p=p ∧ d.q=q := by
  obtain ⟨d,di,dp,dq,H,hH⟩ := trueEligible own mono growth txt threshold
  obtain ⟨k,hk⟩ := occurs d
  obtain ⟨pre,post,parts⟩ := List.append_of_mem hk
  obtain ⟨A,hA⟩ := eventuallyList (pre ++ [d]) (eventuallyCompatible tells txt)
  refine ⟨max A (max H k), fun n hn => ⟨d,?_,di,dp,dq⟩⟩
  obtain ⟨rest,eq⟩ := tasksPrefix (show k ≤ n by omega)
  have tasksEq : tasks n = pre ++ d :: (post ++ rest) := by rw [← eq,parts]; simp
  unfold picks
  rw [sizeHistory txt, tasksEq]
  exact forceEntry (hH n (by omega)) (by rw [di]; exact hA n (by omega))

private theorem universeInfinite (f : List Nat) : ∃ x, x ∉ f := by
  classical
  apply Classical.byContradiction
  intro h
  have le := (List.nodup_range (n := f.length+1)).length_le_of_subset
    (l₂ := f) (fun x _ => Classical.byContradiction fun miss => h ⟨x,miss⟩)
  simp at le
  omega

private theorem commonInfinite {L D level T S} (f : List Nat) :
    ∃ x, common L (picks L D level T S) x ∧ x ∉ f := by
  have valid : meets L (picks L D level T S) := scanValid _ _ (by simp [meets])
  cases h : picks L D level T S with
  | nil =>
    obtain ⟨x,out⟩ := universeInfinite f
    exact ⟨x,by simp [common],out⟩
  | cons d ds =>
    rw [h] at valid
    exact positiveInfinite (valid d (by simp)) f

private theorem sufficient {L D level}
    (mono : ∀ i j, i ≤ j → D i ≤ D j) (growth : ∀ t, t ≤ D t)
    (positive : ∀ i, ∃ p q, level i (p+1) (q+1))
    (w : Witnesses L D level) :
    ∃ F : Output → Output, Succeeds L D level (fun s => F (fun x => x ∈ s)) := by
  classical
  let T (d : Demand) := if h : level d.i (d.p+1) (d.q+1) then (w _ d.b _ _ h).choose else []
  have own d (h : level d.i (d.p+1) (d.q+1)) : Inside (T d) (L d.i) := by
    simpa [T,h] using (w _ d.b _ _ h).choose_spec.1
  have tells (d : Demand) (h : level d.i (d.p+1) (d.q+1)) := (w _ d.b _ _ h).choose_spec.2
  let F (S : Output) := common L (picks L D level T S)
  refine ⟨F, (fun _ _ => commonInfinite _), fun i e txt => ?_⟩
  have found p q (target : level i (p+1) (q+1)) := eventualPick own
    (fun d h => by simpa [T,h] using tells d h) mono growth txt target
  constructor
  · obtain ⟨p,q,h⟩ := positive i
    obtain ⟨N,hN⟩ := found _ _ h
    refine ⟨N,fun n hn x hx => ?_⟩
    obtain ⟨d,mem,eq,_,_⟩ := hN n hn
    exact eq ▸ hx d mem
  · intro p q target
    obtain ⟨N,hN⟩ := found _ _ target
    refine ⟨N,fun n hn => ?_⟩
    obtain ⟨d,mem,di,dp,dq⟩ := hN n hn
    have valid : meets L (picks L D level T (fun x => x ∈ history e n)) :=
      scanValid _ _ (by simp [meets])
    simpa only [F,di,dp,dq] using valid d mem

private theorem margin {a d p q r m k lost : Nat}
    (gap : a*q < p*d) (hd : 0 < d)
    (count : (a+p)*r ≤ (d+q)*m) (parts : m ≤ k+lost)
    (large : d*(d+q)*lost ≤ r) : a*r ≤ d*k := by
  have slack : a*(d+q)+1 ≤ (a+p)*d := by
    simp only [Nat.mul_add,Nat.add_mul] at *
    omega
  have lower := Nat.mul_le_mul_right r slack
  have mid := Nat.mul_le_mul_left d count
  have upper := Nat.mul_le_mul_left (d*(d+q)) parts
  apply Nat.le_of_mul_le_mul_left (c := d+q) _ (by omega)
  simp only [Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm] at *
  omega

private theorem omitFinite {A : Output} {K p q} (good : AtLeast A K p q) (f : List Nat) :
    AtLeast (fun x => A x ∧ x ∉ f) K p q := by
  classical
  intro a d hd gap
  have mediant : (a+p)*q < p*(d+q) := by simp only [Nat.add_mul, Nat.mul_add]; omega
  obtain ⟨R,hR⟩ := good (a+p) (d+q) (by omega) mediant
  refine ⟨max R (d*(d+q)*f.length), fun r hr => ?_⟩
  obtain ⟨w,nd,inside,count⟩ := hR r (by omega)
  let keep := w.filter (fun x => decide (x ∉ f))
  let lost := w.filter (fun x => decide (x ∈ f))
  have lostnd : lost.Nodup := nd.sublist List.filter_sublist
  have short : lost.length ≤ f.length := lostnd.length_le_of_subset (fun x hx => by
    simpa [lost] using (List.mem_filter.mp hx).2)
  have parts : w.length = lost.length + keep.length := by
    simpa [lost,keep,List.countP_eq_length_filter] using
      (List.length_eq_countP_add_countP (fun x => decide (x ∈ f)) (l := w))
  refine ⟨keep,nd.sublist List.filter_sublist,?_,margin (lost := f.length) gap hd count (by omega) (by omega)⟩
  intro x hx
  obtain ⟨hw,hf⟩ := List.mem_filter.mp hx
  exact ⟨⟨(inside x hw).1,by simpa using hf⟩,(inside x hw).2⟩

/-- Removing the finite observed set preserves lower density in each round. -/
private theorem freshen {L D level} {F : Output → Output}
    (good : Succeeds L D level (fun s => F (fun x => x ∈ s))) :
    ∃ H : Output → Output, (∀ S x, H S x → ¬ S x) ∧
      Succeeds L D level (fun s => H (fun x => x ∈ s)) := by
  let H (S : Output) (x : Nat) := F S x ∧ ¬ S x
  refine ⟨H,fun _ _ hx => hx.2,?_,?_⟩
  · intro s f
    obtain ⟨x,hx,fresh⟩ := good.1 s (s++f)
    exact ⟨x,⟨hx,fun h => fresh (List.mem_append_left _ h)⟩,fun h => fresh (List.mem_append_right _ h)⟩
  · intro i e txt
    obtain ⟨⟨N,hN⟩,density⟩ := good.2 i e txt
    refine ⟨⟨N,fun n hn x hx => hN n hn x hx.1⟩,?_⟩
    intro p q h
    obtain ⟨M,hM⟩ := density p q h
    exact ⟨M,fun n hn => omitFinite (hM n hn) (history e n)⟩

/-- Full bounded-displacement texts admit set-valued generation at the prescribed
target-specific lower densities exactly when all rational thresholds have finite witnesses.
Whenever attainable, these guarantees can be attained from the current seen set alone, with every output disjoint from that set. -/
theorem densityCriterion (L : Nat → Language) (D : Nat → Nat) (level : Levels)
    (nondecreasing : ∀ i j, i ≤ j → D i ≤ D j) (growth : ∀ t, t ≤ D t)
    (positive : ∀ i, ∃ p q, level i (p+1) (q+1)) :
    ((∃ G, Succeeds L D level G) ↔ SetDensity.Witnesses L D level) ∧
    (SetDensity.Witnesses L D level ↔
      ∃ F : Output → Output, (∀ S x, F S x → ¬ S x) ∧
        Succeeds L D level (fun s => F (fun x => x ∈ s))) := by
  have suf := sufficient (L := L) nondecreasing growth positive
  exact ⟨⟨fun ⟨_,good⟩ => necessity growth good, fun w =>
    let ⟨F,good⟩ := suf w
    ⟨fun s => F (fun x => x ∈ s),good⟩⟩,
    ⟨fun w => let ⟨_,good⟩ := suf w; freshen good, fun ⟨_,_,good⟩ => necessity growth good⟩⟩

end SetDensity
