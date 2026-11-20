module

public import SolvedProblems.DisplacementModel

public section

namespace Displacement

private theorem orderLe (K : Language) {i j : Nat} (h : i ≤ j) : K.word i ≤ K.word j := by
  rcases Nat.eq_or_lt_of_le h with rfl | lt
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (K.ordered lt)

private theorem inj (K : Language) {i j} (h : K.word i = K.word j) : i = j := by
  by_cases lt : i < j
  · have := K.ordered lt; omega
  by_cases gt : j < i
  · have := K.ordered gt; omega
  omega

private theorem least {P : Nat → Prop} (ex : ∃ n, P n) : ∃ n, P n ∧ ∀ k, P k → n ≤ k := by
  classical
  obtain ⟨n,hn⟩ := ex
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases low : ∃ k < n, P k
    · obtain ⟨k,hk,h⟩ := low; exact ih k hk h
    · exact ⟨n,hn,fun k h => Nat.le_of_not_gt (fun hk => low ⟨k,hk,h⟩)⟩

private theorem len (e : Nat → Nat) (n) : (history e n).length = n := by simp [history]

theorem memHist {e : Nat → Nat} {n x} : x ∈ history e n ↔ ∃ k < n, e k = x := by simp [history]

theorem nodupHist {e : Nat → Nat} (h : ∀ a b, e a = e b → a=b) (n) :
    (history e n).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  exact h i j (by simpa [history] using eq)

theorem histInside {e D K} (txt : Text D K e) (n) : Inside (history e n) K := by
  intro x hx
  obtain ⟨k,_,hk⟩ := memHist.mp hx
  exact (txt.2.1 x).mpr ⟨k,hk⟩

private theorem allBound {P : Nat → Nat → Prop} (B : Nat)
    (one : ∀ i < B, ∃ N, ∀ n ≥ N, P i n) :
    ∃ N, ∀ n ≥ N, ∀ i < B, P i n := by
  induction B with
  | zero => exact ⟨0,by intros; omega⟩
  | succ B ih =>
    obtain ⟨M,hm⟩ := ih (fun i hi => one i (by omega))
    obtain ⟨K,hk⟩ := one B (by omega)
    refine ⟨max M K, fun n hn i hi => ?_⟩
    by_cases eq : i=B
    · exact eq ▸ hk n (by omega)
    · exact hm n (by omega) i (by omega)

theorem seen {D K e} (txt : Text D K e) {s} (hs : Inside s K) :
    ∃ N, ∀ n ≥ N, s ⊆ history e n := by
  induction s with
  | nil => exact ⟨0,by simp⟩
  | cons x xs ih =>
    obtain ⟨k,hk⟩ := (txt.2.1 x).mp (hs x (by simp))
    obtain ⟨M,hm⟩ := ih (fun y hy => hs y (by simp [hy]))
    refine ⟨max M (k+1),fun n hn y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | h
    · exact memHist.mpr ⟨k,by omega,hk⟩
    · exact hm n (by omega) h

private def Whole (s : List Nat) (K : Language) (D : Nat → Nat) (b : Nat) :=
  ∀ t, b ≤ t → t ≤ s.length → ∀ x ∈ s.take t, x < K.word (D t)

private theorem takeHist (e : Nat → Nat) {t n} (h : t ≤ n) :
    (history e n).take t = history e t := by
  apply List.ext_getElem <;> simp [history, Nat.min_eq_left h]

private theorem wholeEventually {D K e} (mono : ∀ i j, i ≤ j → D i ≤ D j)
    (atLeast : ∀ n, n ≤ D n) (txt : Text D K e) :
    ∃ b, 1 ≤ b ∧ ∀ n, Whole (history e n) K D b := by
  obtain ⟨B,hB⟩ := txt.2.2
  obtain ⟨M,hM⟩ := allBound (P := fun k t => e k < K.word (D t)) B (by
    intro i _
    obtain ⟨r,hr⟩ := (txt.2.1 _).mpr ⟨i,rfl⟩
    exact ⟨r+1,fun t ht => hr ▸ K.ordered (by have := atLeast t; omega)⟩)
  refine ⟨M+1,by omega,?_⟩
  intro n t ht hn x hx
  rw [len] at hn
  rw [takeHist e hn] at hx
  obtain ⟨i,hi,rfl⟩ := memHist.mp hx
  by_cases small : i < B
  · exact hM t (by omega) i small
  · exact Nat.lt_of_lt_of_le (hB i (by omega)) (orderLe K (mono _ _ hi))

/-- Eventually the entire prefix of each length meets that length's deadline. -/
theorem eventualPrefixDeadlines {D K e} (mono : ∀ i j, i ≤ j → D i ≤ D j)
    (atLeast : ∀ n, n ≤ D n) (txt : Text D K e) :
    ∃ b, 1 ≤ b ∧ ∀ t ≥ b, ∀ x ∈ history e t, x < K.word (D t) := by
  obtain ⟨b, hb, whole⟩ := wholeEventually mono atLeast txt
  refine ⟨b, hb, fun t ht x hx => whole t t ht (by simp [len]) x ?_⟩
  rwa [takeHist e (Nat.le_refl t)]

private theorem sufficient {L D} (mono : ∀ i j, i ≤ j → D i ≤ D j)
    (atLeast : ∀ n, n ≤ D n) (w : Witnesses L D) : Identifiable L D := by
  classical
  let T (i b : Nat) := (w i (b+1) (by omega)).choose
  let ok (s : List Nat) (i b : Nat) :=
    T i b ⊆ s ∧ Inside s (L i) ∧ Whole s (L i) D (b+1)
  let cost (s : List Nat) (c : Nat) := ∃ i b, i+b=c ∧ ok s i b
  let G (s : List Nat) := if h : ∃ c, cost s c then (least h).choose_spec.1.choose else 0
  refine ⟨G, ?_⟩
  intro j e txt
  obtain ⟨b',pos,hb⟩ := wholeEventually mono atLeast txt
  obtain ⟨b,rfl⟩ : ∃ b, b' = b+1 := ⟨b'-1,by omega⟩
  obtain ⟨M,hM⟩ := seen txt (w j (b+1) (by omega)).choose_spec.1
  let B := j+b+1
  have stabilizes (i a : Nat) :
      ∃ N, ∀ n ≥ N, ok (history e n) i a → Same (L i) (L j) := by
    by_cases same : Same (L i) (L j)
    · exact ⟨0,fun _ _ _ => same⟩
    by_cases sub : Sub (L j) (L i)
    · by_cases trigger : Inside (T i a) (L j)
      · have fails : ¬ Fits (L j) (L i) D (a+1) := fun fit =>
          same (fun x => ((w i (a+1) (by omega)).choose_spec.2 j trigger sub fit x).symm)
        have bad : ∃ t, a+1 ≤ t ∧ ¬ ∃ l : List Nat, l.Nodup ∧ l.length=t ∧ Inside l (L j) ∧
            ∀ x ∈ l, (L i).Has x ∧ x < (L i).word (D t) := by
          exact Classical.byContradiction fun no => fails (fun t ht => Classical.byContradiction
            fun h => no ⟨t,ht,h⟩)
        obtain ⟨t,ht,none⟩ := bad
        refine ⟨t,fun n hn elig => False.elim (none ⟨history e t,
          nodupHist txt.1 _,len e t,histInside txt _,?_⟩)⟩
        intro x hx
        exact ⟨sub x (histInside txt t x hx),elig.2.2 t ht (by rwa [len])
          x (by rwa [takeHist e hn])⟩
      · exact ⟨0,fun n _ elig => False.elim (trigger (fun x hx => histInside txt n x (elig.1 hx)))⟩
    · have bad : ∃ x, (L j).Has x ∧ ¬ (L i).Has x :=
        Classical.byContradiction fun no => sub (fun x hx => Classical.byContradiction
          fun h => no ⟨x,hx,h⟩)
      obtain ⟨x,hj,hi⟩ := bad
      obtain ⟨k,hk⟩ := (txt.2.1 x).mp hj
      exact ⟨k+1,fun n hn elig => False.elim (hi (elig.2.1 x (memHist.mpr ⟨k,by omega,hk⟩)))⟩
  obtain ⟨K,hK⟩ := allBound B (fun i _ => allBound B (fun a _ => stabilizes i a))
  refine ⟨max M K,fun n hn => ?_⟩
  let s := history e n
  have truth : cost s (j+b) := ⟨j,b,rfl,hM n (by omega),histInside txt n,hb n⟩
  have ex : ∃ c, cost s c := ⟨_,truth⟩
  have le := (least ex).choose_spec.2 _ truth
  let i := (least ex).choose_spec.1.choose
  obtain ⟨a,ha,sel⟩ := (least ex).choose_spec.1.choose_spec
  have ib : i < B := by dsimp [i,B]; omega
  have ab : a < B := by dsimp [B]; omega
  have good := hK n (by omega) i ib a ab sel
  change Same (L (G s)) _
  simpa [G,ex,i] using good


private theorem unused {w s : List Nat} (hw : w.Nodup) (hs : s.length < w.length) :
    ∃ x ∈ w, x ∉ s := by
  classical
  exact Classical.byContradiction fun no => Nat.not_le_of_gt hs
    (hw.length_le_of_subset (fun x hx => Classical.byContradiction fun hn => no ⟨x,hx,hn⟩))

private theorem missing (K : Language) (s : List Nat) : ∃ r, K.word r ∉ s := by
  let w := history K.word (s.length+1)
  have h := unused (s := s) (w := w) (nodupHist (fun _ _ => inj K) _) (by simp [w,len])
  obtain ⟨x,hx,hfresh⟩ := h
  obtain ⟨r,_,rfl⟩ := memHist.mp hx
  exact ⟨r,hfresh⟩

private noncomputable def rank (K : Language) (s : List Nat) :=
  (least (missing K s)).choose
private theorem rank_fresh (K : Language) (s : List Nat) : K.word (rank K s) ∉ s :=
  (least (missing K s)).choose_spec.1
private theorem rank_le {K : Language} {s : List Nat} {r} (h : K.word r ∉ s) :
    rank K s ≤ r := (least (missing K s)).choose_spec.2 r h

private theorem rank_bound (K : Language) (s : List Nat) : rank K s ≤ s.length := by
  obtain ⟨x,hx,hfresh⟩ := unused (s := s) (w := history K.word (s.length+1))
    (nodupHist (fun _ _ => inj K) _) (by simp [len])
  obtain ⟨r,hr,rfl⟩ := memHist.mp hx
  have := rank_le hfresh
  omega

private noncomputable def appendNext (K : Language) (s : List Nat) :=
  s ++ [K.word (rank K s)]

private theorem advance {K : Language} {s : List Nat} {n}
    (h : ∀ r < n, K.word r ∈ s) : ∀ r < n+1, K.word r ∈ appendNext K s := by
  intro r hr
  by_cases done : K.word r ∈ s
  · simp [appendNext,done]
  · have le := rank_le done
    have notlt : ¬rank K s < n := fun lt => rank_fresh K s (h _ lt)
    have eq : rank K s = r := by omega
    simp [appendNext,eq]

private def Sound (D : Nat → Nat) (K : Language) (s : List Nat) :=
  s.Nodup ∧ Inside s K ∧ ∀ k (hk : k < s.length), s[k] < K.word (D (k+1))

private theorem appendSound {D K s} (hs : Sound D K s) {x}
    (fresh : x ∉ s) (inK : K.Has x) (bound : x < K.word (D (s.length+1))) :
    Sound D K (s ++ [x]) := by
  refine ⟨by simp [List.nodup_append,hs.1]; grind,?_,?_⟩
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact hs.2.1 _ h
    · have eq := List.mem_singleton.mp h; exact eq ▸ inK
  · intro k hk
    by_cases h : k < s.length
    · simpa [List.getElem_append_left h] using hs.2.2 k h
    · have eq : k=s.length := by simp at hk; omega
      subst k
      simpa using bound

private theorem ownBound (D : Nat → Nat) (atLeast : ∀ n, n ≤ D n) (K : Language) (s : List Nat) :
    K.word (rank K s) < K.word (D (s.length+1)) := by
  apply K.ordered
  have := rank_bound K s
  have := atLeast (s.length+1)
  omega

private theorem appendInside {K s} (h : Inside s K) : Inside (appendNext K s) K := by
  intro x hx
  rcases List.mem_append.mp hx with hm | hm
  · exact h _ hm
  · have eq := List.mem_singleton.mp hm
    exact ⟨_,eq.symm⟩

private theorem fitsBound {D J K s b} (fits : Fits J K D b) (bt : b ≤ s.length+1) :
    J.word (rank J s) < K.word (D (s.length+1)) := by
  obtain ⟨w,hw,len,inside,cut⟩ := fits _ bt
  obtain ⟨x,hx,hn⟩ := unused (s := s) hw (by omega)
  obtain ⟨r,rfl⟩ := inside x hx
  exact Nat.lt_of_le_of_lt (orderLe J (rank_le hn)) (cut _ hx).2

private noncomputable def fill (J : Language) (s : List Nat) : Nat → List Nat
  | 0 => s
  | n+1 => appendNext J (fill J s n)

private theorem fillLen (J : Language) (s : List Nat) (n) :
    (fill J s n).length = s.length+n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fill,appendNext,ih,Nat.add_assoc]

private theorem fillPref (J : Language) (s : List Nat) (n) : s.IsPrefix (fill J s n) := by
  induction n with
  | zero => exact List.prefix_refl _
  | succ n ih => exact ih.trans (List.prefix_append ..)

private theorem fillInside {J : Language} {s : List Nat} (h : Inside s J) (n) :
    Inside (fill J s n) J := by
  induction n with
  | zero => exact h
  | succ n ih => exact appendInside ih

private theorem fillCovers (J : Language) (s : List Nat) (n) :
    ∀ r < n, J.word r ∈ fill J s n := by
  induction n with
  | zero => intros; omega
  | succ n ih => exact advance ih

private theorem fillSound {D K J b s} (hs : Sound D K s) (hb : b ≤ s.length+1)
    (sub : Sub J K) (fits : Fits J K D b) (n) : Sound D K (fill J s n) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact appendSound ih (rank_fresh J _) (sub _ ⟨_,rfl⟩) (fitsBound fits (by rw [fillLen]; omega))

/-- Read the unique stream determined by nested finite lists of increasing length. -/
private theorem realize (s : Nat → List Nat) (step : ∀ n, (s n).IsPrefix (s (n+1)))
    (long : ∀ n, n ≤ (s n).length) : ∃ e, ∀ n, history e (s n).length = s n := by
  have mono {i j} (h : i ≤ j) : (s i).IsPrefix (s j) := by
    induction h with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (step _)
  let e := fun k => (s (k+1))[k]'(by have := long (k+1); omega)
  refine ⟨e, fun n => ?_⟩
  apply List.ext_getElem
  · simp [history]
  · intro k hk hs
    simp [history]
    exact ((mono (Nat.le_max_left (k+1) n)).getElem (by have := long (k+1); omega)).trans
      ((mono (Nat.le_max_right (k+1) n)).getElem hs).symm

private theorem lookup {e s} (agrees : history e s.length = s) {k} (hk : k < s.length) :
    s[k] = e k := by
  have eq := congrArg (fun l : List Nat => l[k]?) agrees
  simpa [history,hk,List.getElem?_eq_getElem] using eq.symm

private theorem realizedText {D K} {s : Nat → List Nat} {e}
    (agrees : ∀ n, history e (s n).length = s n) (long : ∀ n, n ≤ (s n).length)
    (nd : ∀ n, (s n).Nodup) (inside : ∀ n, Inside (s n) K)
    (covers : ∀ r, ∃ n, K.word r ∈ s n)
    (legal : ∃ b, ∀ k ≥ b, e k < K.word (D (k+1))) : Text D K e := by
  refine ⟨?_,?_,legal⟩
  · intro i j eq
    let n := max i j + 1
    have hi : i < (s n).length := by have := long n; dsimp [n] at *; omega
    have hj : j < (s n).length := by have := long n; dsimp [n] at *; omega
    exact List.nodup_iff_eq_of_getElem_eq.mp (nd n) i j hi hj
      ((lookup (agrees n) hi).trans (eq.trans (lookup (agrees n) hj).symm))
  · intro x
    constructor
    · rintro ⟨r,rfl⟩
      obtain ⟨n,hm⟩ := covers r
      rw [← agrees n] at hm
      obtain ⟨k,_,hk⟩ := memHist.mp hm
      exact ⟨k,hk⟩
    · rintro ⟨k,rfl⟩
      apply inside (k+1)
      rw [← agrees (k+1)]
      apply memHist.mpr
      exact ⟨k,by have := long (k+1); omega,rfl⟩

private theorem growStage {D : Nat → Nat} (atLeast : ∀ n, n ≤ D n)
    {K J : Language} {P : List Nat → Prop}
    (bad : ∀ e, Text D J e → ∃ N, ∀ n ≥ N, ¬ P (history e n))
    {b s} (hs : Sound D K s) (bt : b ≤ s.length+1)
    (inside : Inside s J) (sub : Sub J K) (fits : Fits J K D b) :
    ∃ u, s.IsPrefix u ∧ Sound D K u ∧ ¬ P u := by
  let seq := fill J s
  have long (n) : n ≤ (seq n).length := by simp [seq,fillLen]
  obtain ⟨e,agree⟩ := realize seq (fun _ => List.prefix_append ..) long
  have sound (n) := fillSound hs bt sub fits n
  have legal : ∀ k ≥ s.length, e k < J.word (D (k+1)) := by
    intro k hk
    let n := k - s.length
    have len0 : (seq n).length = k := by simp [seq,n,fillLen]; omega
    have eq : (seq (n+1)) = (seq n) ++ [J.word (rank J (seq n))] := rfl
    have len1 : k < (seq (n+1)).length := by simp [eq,len0]
    have point := lookup (agree (n+1)) len1
    have hp : (seq (n+1))[k] = J.word (rank J (seq n)) := by
      simp [eq,List.getElem_append_right (by omega : (seq n).length ≤ k),len0]
    rw [← point,hp,← len0]
    exact ownBound _ atLeast _ _
  have text := realizedText agree long (fun n => (sound n).1) (fillInside inside)
    (fun r => ⟨r+1,fillCovers _ _ _ r (by omega)⟩) ⟨_,legal⟩
  obtain ⟨N,hN⟩ := bad e text
  refine ⟨seq N, fillPref _ _ _, sound N, ?_⟩
  simpa only [agree N] using hN _ (long N)

/-- On a full bounded-displacement text, an eventual property of the observed histories
has a finite witness excluding every feasible sublanguage on whose texts its negation
eventually holds. -/
theorem lockingWitness {D : Nat → Nat} (atLeast : ∀ n, n ≤ D n)
    {K : Language} (b : Nat) {P : List Nat → Prop} {bad : Language → Prop}
    (stable : ∀ e, Text D K e → ∃ N, ∀ n ≥ N, P (history e n))
    (unstable : ∀ J, bad J → ∀ e, Text D J e → ∃ N, ∀ n ≥ N, ¬ P (history e n)) :
    ∃ T, Inside T K ∧ ∀ J, Inside T J → Sub J K → Fits J K D b → ¬ bad J := by
  classical
  apply Classical.byContradiction
  intro none
  have rival (s : List Nat) (inside : Inside s K) :
      ∃ J, Inside s J ∧ Sub J K ∧ Fits J K D b ∧ bad J := by
    exact Classical.byContradiction fun no => none ⟨s, inside, fun J hj sub fits diff =>
      no ⟨J, hj, sub, fits, diff⟩⟩
  let Node := {s : List Nat // Sound D K s ∧ b ≤ s.length}
  let init := history K.word b
  have hinit : Sound D K init := by
    refine ⟨nodupHist (fun _ _ => inj _) _,?_,?_⟩
    · intro x hx
      obtain ⟨r,_,hr⟩ := memHist.mp hx
      exact ⟨r,hr⟩
    · intro k hk
      simp only [init,history,List.getElem_map,List.getElem_range]
      exact K.ordered (atLeast (k+1))
  have step (p : Node) : ∃ u, (appendNext K p.val).IsPrefix u ∧
        Sound D K u ∧ ¬ P u := by
    have hs := appendSound p.property.1 (rank_fresh K p.val)
      (show K.Has (K.word (rank K p.val)) from ⟨_,rfl⟩)
      (ownBound D atLeast K p.val)
    obtain ⟨j,hj,sub,fits,diff⟩ := rival _ hs.2.1
    exact growStage atLeast (unstable j diff) hs (by have := p.property.2; simp [appendNext]; omega) hj sub fits
  let grow (p : Node) : Node := ⟨(step p).choose, (step p).choose_spec.2.1, by
    have h := (step p).choose_spec.1.length_le
    exact Nat.le_trans p.property.2 (Nat.le_trans (by simp [appendNext]) h)⟩
  let nodes : Nat → Node := Nat.rec ⟨init,hinit,by simp [init,len]⟩ (fun _ p => grow p)
  let s (n : Nat) := (nodes n).val
  have extn (n) : (appendNext K (s n)).IsPrefix (s (n+1)) ∧ ¬ P (s (n+1)) :=
    ⟨(step (nodes n)).choose_spec.1,(step (nodes n)).choose_spec.2.2⟩
  have long (n) : n ≤ (s n).length := by
    induction n with
    | zero => omega
    | succ n ih =>
      have h := (extn n).1.length_le
      simp [appendNext] at h
      omega
  obtain ⟨e,agree⟩ := realize s (fun n => (List.prefix_append ..).trans (extn n).1) long
  have cover (n) : ∀ r < n, K.word r ∈ s n := by
    induction n with
    | zero => intros; omega
    | succ n ih => exact fun r hr => (extn n).1.sublist.subset (advance ih r hr)
  have valid := realizedText agree long (fun n => (nodes n).property.1.1)
    (fun n => (nodes n).property.1.2.1) (fun r => ⟨r+1,cover (r+1) r (by omega)⟩)
    (D := D) ⟨0,fun k _ => by
      have hk : k < (s (k+1)).length := by have := long (k+1); omega
      rw [← lookup (agree (k+1)) hk]
      exact (nodes (k+1)).property.1.2.2 k hk⟩
  obtain ⟨N,hN⟩ := stable e valid
  have got := hN _ (show N ≤ (s (N+1)).length by have := long (N+1); omega)
  rw [agree (N+1)] at got
  exact (extn N).2 got

private theorem necessary {L D} (atLeast : ∀ n, n ≤ D n) (learner : Identifiable L D) :
    Witnesses L D := by
  classical
  obtain ⟨G, learn⟩ := learner
  intro i b _
  let bad (J : Language) := ∃ j, J = L j ∧ ¬ Same J (L i)
  obtain ⟨T, inside, locks⟩ := lockingWitness atLeast b (P := fun s => Same (L (G s)) (L i))
    (bad := bad) (learn i) (by
      rintro J ⟨j, rfl, diff⟩ e txt
      obtain ⟨N, h⟩ := learn j e txt
      exact ⟨N, fun n hn h' => diff (fun x => ((h n hn x).symm.trans (h' x)))⟩)
  exact ⟨T, inside, fun j hj sub fits => Classical.byContradiction fun diff =>
    locks _ hj sub fits ⟨j, rfl, diff⟩⟩

/-- The bounded-displacement telltale criterion. Taking D(t) = floor(M t),
M ≥ 1, recovers the rank bound in the paper. -/
theorem finiteWitnessCriterion (L : Nat → Language) (D : Nat → Nat)
    (nondecreasing : ∀ i j, i ≤ j → D i ≤ D j) (atLeast : ∀ t, t ≤ D t) :
    Identifiable L D ↔ Witnesses L D :=
  ⟨necessary atLeast,sufficient nondecreasing atLeast⟩

end Displacement
