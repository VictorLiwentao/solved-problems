module

public import SolvedProblems.SingletonDensityBlocks

public section

namespace SingletonDensity

private theorem start_step (j : Nat) : start (j+1) = start j + j + 3 := rfl

private theorem le_start (j : Nat) : j ≤ start j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => rw [start_step]; omega

private theorem start_mono {i j : Nat} (h : i ≤ j) : start i ≤ start j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => rw [start_step]; omega

private theorem in_block {x j} : x ∈ block j ↔ start j ≤ x ∧ x < start (j+1) := by
  simp [block, and_comm]

private theorem cell_unique {x j k} (hj : x ∈ block j) (hk : x ∈ block k) : j = k := by
  have ⟨a,b⟩ := in_block.mp hj
  have ⟨c,d⟩ := in_block.mp hk
  rcases lt_trichotomy j k with lt|eq|gt
  · have : start (j+1) ≤ start k := start_mono lt; omega
  · exact eq
  · have : start (k+1) ≤ start j := start_mono gt; omega

private theorem block_size (j : Nat) : (block j).card = j+3 := by
  unfold block
  rw [Finset.card_sdiff_of_subset (Finset.range_mono (start_mono (Nat.le_succ _)))]
  simp [start_step]; omega

/-- Snapshot immediately after an adversary move. The newest response is processed
when choosing the following adversary move. -/
private structure State where
  hist : List Nat
  used : Finset Nat

private def marks (s : State) := s.hist.toFinset
private def mass (v : Finset Nat) (j : Nat) := (block j ∩ v).card

private theorem mass_le (v j) : mass v j ≤ j+3 := by
  rw [← block_size]; exact Finset.card_le_card Finset.inter_subset_left

private theorem mass_mono {v w : Finset Nat} (h : v ⊆ w) (j) : mass v j ≤ mass w j :=
  Finset.card_le_card (fun _ hx => Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).1,h (Finset.mem_inter.mp hx).2⟩)

private theorem mass_insert (v j x) :
    mass (insert x v) j = mass v j + if x ∈ block j ∧ x ∉ v then 1 else 0 := by
  classical
  by_cases h : x ∈ block j
  · have eq : block j ∩ insert x v = insert x (block j ∩ v) := by ext y; simp; grind
    unfold mass
    rw [eq]
    by_cases hx : x ∈ v <;> simp [h,hx]
  · have eq : block j ∩ insert x v = block j ∩ v := by ext y; simp; grind
    simp [mass,eq,h]

private def pending (G : Strategy) (s : State) : Option Nat :=
  if s.hist.isEmpty then none else G s.hist

private def deny (s : State) (p : Option Nat) := p.elim s.used (fun x => insert x s.used)

private def step (s : State) (p : Option Nat) (x : Nat) : State :=
  ⟨x :: s.hist, insert x (deny s p)⟩

private theorem old_deny (s p) : s.used ⊆ deny s p := by
  cases p with
  | none => exact fun _ h => h
  | some x => exact Finset.subset_insert _ _

private theorem mass_deny (s : State) (p : Option Nat) (j) :
    mass (deny s p) j ≤ mass s.used j + 1 := by
  cases p with
  | none => exact Nat.le_succ _
  | some x =>
    change mass (insert x s.used) j ≤ _
    rw [mass_insert]; split <;> omega

/-- The slack inequality expresses that the unclaimed part of each block contains
at least twice the number of adversary moves still required there. -/
private structure Valid (q : Nat → Nat) (s : State) : Prop where
  list : s.hist.Nodup
  subset : marks s ⊆ s.used
  cap : ∀ j, mass (marks s) j ≤ q j
  slack : ∀ j, mass s.used j + 2*q j ≤ j+3 + 2 * mass (marks s) j

private def bad (q : Nat → Nat) (s : State) (p : Option Nat) (j : Nat) :=
  j+3 + 2*mass (marks s) j < mass (deny s p) j + 2*q j

private theorem bad_new {q s p j} (v : Valid q s) (h : bad q s p j) :
    ∃ y, p = some y ∧ y ∈ block j ∧ y ∉ s.used := by
  have old := v.slack j
  unfold bad at h
  cases p with
  | none => exact False.elim ((Nat.not_lt_of_ge old) h)
  | some y =>
    refine ⟨y,rfl,?_⟩
    change _ < mass (insert y s.used) j + _ at h
    rw [mass_insert] at h
    split at h <;> first | assumption | omega

private theorem bad_unique {q s p j k} (v : Valid q s) (a : bad q s p j) (b : bad q s p k) :
    j = k := by
  obtain ⟨x,rfl,h,_⟩ := bad_new v a
  obtain ⟨y,eq,g,_⟩ := bad_new v b
  cases eq
  exact cell_unique h g

private theorem boundFin (v : Finset Nat) : ∃ N, ∀ x ∈ v, x < start N := by
  refine ⟨(v.toList.foldr max 0)+1,?_⟩
  have bound (l : List Nat) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      intro x h
      rcases List.mem_cons.mp h with rfl|hm
      · exact Nat.le_max_left ..
      · exact (ih _ hm).trans (Nat.le_max_right ..)
  intro x hx
  have h := bound v.toList x (Finset.mem_toList.mpr hx)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le h) (le_start _)

private theorem no_mass {s : Finset Nat} {j} (before : ∀ x ∈ s, x < start j) :
    mass s j = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hit
  obtain ⟨hb,hs⟩ := Finset.mem_inter.mp hit
  exact (Nat.not_lt_of_ge (in_block.mp hb).1) (before _ hs)

private theorem needs {q : Nat → Nat} (inf : ∀ n, ∃ j ≥ n, 0 < q j) (s : State) :
    ∃ j, mass (marks s) j < q j := by
  obtain ⟨N,hN⟩ := boundFin (marks s)
  obtain ⟨j,le,hq⟩ := inf N
  exact ⟨j, by rw [no_mass (fun x hx => (hN x hx).trans_le (start_mono le))]; exact hq⟩

private structure Move (q : Nat → Nat) (s : State) (p : Option Nat) where
  j : Nat
  x : Nat
  cell : x ∈ block j
  free : x ∉ deny s p
  reason : bad q s p j ∨ ∀ k, mass (marks s) k < q k → j ≤ k
  valid : Valid q (step s p x)

/-- Repair the unique block whose slack a new output has exhausted. If all blocks
have enough slack, fill the earliest unfinished block. -/
private noncomputable def chooseMove {q : Nat → Nat} (inf : ∀ n, ∃ j ≥ n, 0 < q j)
    {s : State} (v : Valid q s) (p : Option Nat) : Move q s p := by
  classical
  have pick : ∃ j, mass (marks s) j < q j ∧ (∀ k, k ≠ j → ¬bad q s p k) ∧
        (bad q s p j ∨ ∀ k, mass (marks s) k < q k → j ≤ k) := by
    by_cases danger : ∃ j, bad q s p j
    · obtain ⟨j,h⟩ := danger
      refine ⟨j,?_,fun k ne g => ne (bad_unique v g h),Or.inl h⟩
      have lim := mass_le (deny s p) j
      unfold bad at h
      omega
    · let least := Nat.find (needs inf s)
      exact ⟨least,Nat.find_spec (needs inf s),fun k _ h => danger ⟨k,h⟩,
        Or.inr (fun _ h => Nat.find_min' (needs inf s) h)⟩
  let j := pick.choose
  obtain ⟨room,others,why⟩ := pick.choose_spec
  have unused : ∃ x ∈ block j, x ∉ deny s p := by
    have reserve := v.slack j
    have one := mass_deny s p j
    have lt : mass (deny s p) j < (block j).card := by rw [block_size]; change mass (marks s) j < q j at room; omega
    obtain ⟨x,h,hx⟩ := Finset.exists_mem_notMem_of_card_lt_card lt
    exact ⟨x,h,fun hu => hx (Finset.mem_inter.mpr ⟨h,hu⟩)⟩
  let x := unused.choose
  have hblock : x ∈ block j := unused.choose_spec.1
  have free : x ∉ deny s p := unused.choose_spec.2
  have fresh : x ∉ marks s := fun hx => free (old_deny _ _ (v.subset hx))
  refine ⟨j,x,hblock,free,why,?_⟩
  have counts (k : Nat) : mass (marks (step s p x)) k =
      mass (marks s) k + if x ∈ block k then 1 else 0 := by
    change mass ((x::s.hist).toFinset) k = _
    rw [List.toFinset_cons,mass_insert]
    have h : x ∉ s.hist.toFinset := fresh
    simp only [h,not_false_eq_true, and_true]
    rfl
  refine ⟨List.nodup_cons.mpr ⟨fun h => fresh (List.mem_toFinset.mpr h),v.list⟩,?_,?_,?_⟩
  · intro y hy
    change y ∈ (x::s.hist).toFinset at hy
    rcases List.mem_cons.mp (List.mem_toFinset.mp hy) with rfl|h
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (old_deny _ _ (v.subset (List.mem_toFinset.mpr h)))
  · intro k
    rw [counts]
    split
    next hit => have eq := cell_unique hblock hit; change mass (marks s) j < q j at room; subst k; omega
    next => simpa using v.cap k
  · intro k
    rw [counts]
    change mass (insert x (deny s p)) k + _ ≤ _
    rw [mass_insert]
    by_cases hit : x ∈ block k
    · have eq := cell_unique hblock hit
      subst k
      simp [hit,free]
      have := v.slack j; have := mass_deny s p j; omega
    · simp [hit]
      have ne : k ≠ j := fun eq => hit (eq ▸ hblock)
      exact Nat.le_of_not_lt (others k ne)

private def emptyState : State := ⟨[],∅⟩

private structure Run (G : Strategy) (q : Nat → Nat) where
  st : Nat → State
  init : st 0 = emptyState
  valid : ∀ n, Valid q (st n)
  move : ∀ n, Move q (st n) (pending G (st n))
  advance : ∀ n, st (n+1) = step (st n) (pending G (st n)) (move n).x

private noncomputable def makeRun {q : Nat → Nat} (size : ∀ j, 2*q j+1 ≤ j+3)
    (inf : ∀ n, ∃ j ≥ n, 0 < q j) (G : Strategy) : Run G q := by
  have initial : Valid q emptyState := by
    refine ⟨by simp [emptyState], by simp [emptyState,marks], by simp [emptyState,mass,marks], ?_⟩
    intro j
    simpa [emptyState,mass,marks] using (Nat.le_trans (Nat.le_succ _) (size j))
  let iter : Nat → {s // Valid q s} := Nat.rec ⟨emptyState,initial⟩ (fun _ s =>
    let m := chooseMove inf s.property (pending G s.val)
    ⟨step s.val (pending G s.val) m.x, m.valid⟩)
  exact ⟨fun n => (iter n).val,rfl,fun n => (iter n).property,
    fun n => chooseMove inf (iter n).property (pending G (iter n).val),fun _ => rfl⟩

private def played {G q} (r : Run G q) (n : Nat) := (r.move n).x

private theorem hist_eq {G q} (r : Run G q) (n : Nat) :
    (r.st n).hist = seenPrefix (played r) n := by
  induction n with
  | zero => rw [r.init]; rfl
  | succ n ih =>
    rw [r.advance]
    change played r n :: (r.st n).hist = played r n :: seenPrefix (played r) n
    rw [ih]

/-- A rank occurs in the observed history exactly when it was enumerated before round n. -/
theorem mem_seenPrefix {e : Nat → Nat} {x n} :
    x ∈ seenPrefix e n ↔ ∃ t < n, e t = x := by
  induction n with
  | zero => simp [seenPrefix]
  | succ n ih =>
    change x ∈ e n :: seenPrefix e n ↔ _
    rw [List.mem_cons,ih]
    constructor
    · rintro (rfl|⟨t,lt,rfl⟩)
      · exact ⟨n,Nat.lt_succ_self _,rfl⟩
      · exact ⟨t,by omega,rfl⟩
    · rintro ⟨t,lt,rfl⟩
      by_cases h : t = n
      · simp [h]
      · exact Or.inr ⟨t,by omega,rfl⟩

private theorem played_inj {G q} (r : Run G q) : Function.Injective (played r) := by
  have neq {i j} (h : i < j) : played r i ≠ played r j := by
    intro eq
    have hm : played r j ∈ (r.st j).hist := (hist_eq r j) ▸ mem_seenPrefix.mpr ⟨i,h,eq⟩
    exact (r.move j).free (old_deny _ _ ((r.valid j).subset (List.mem_toFinset.mpr hm)))
  intro i j eq
  rcases lt_trichotomy i j with h|h|h
  · exact (neq h eq).elim
  · exact h
  · exact (neq h eq.symm).elim

private theorem escapes {e : Nat → Nat} (inj : Function.Injective e) (B : Nat) :
    ∃ n, ∀ t ≥ n, B ≤ e t := by
  induction B with
  | zero => exact ⟨0, fun _ _ => Nat.zero_le _⟩
  | succ B ih =>
    obtain ⟨n,hn⟩ := ih
    by_cases hit : ∃ i, e i = B
    · obtain ⟨i,hi⟩ := hit
      refine ⟨max n (i+1),fun t ht => ?_⟩
      have := hn t ((Nat.le_max_left ..).trans ht)
      have ne : e t ≠ B := fun h => by have eq := inj (h.trans hi.symm); omega
      omega
    · refine ⟨n, fun t ht => ?_⟩
      have := hn t ht
      have : e t ≠ B := fun h => hit ⟨t,h⟩
      omega

/-- A forced repair keeps all touched ranks below the old block boundary. A block
that was previously untouched has at least one extra unit of slack. -/
private theorem repair_bound {q s p} (size : ∀ j, 2*q j+1 ≤ j+3)
    (v : Valid q s) (m : Move q s p) (h : bad q s p m.j) {B}
    (old : ∀ y ∈ s.used, y < start B) :
    ∀ y ∈ (step s p m.x).used, y < start B := by
  have lt : m.j < B := by
    by_contra! le
    have zero := no_mass (fun y hy => (old y hy).trans_le (start_mono le))
    have inc := mass_deny s p m.j
    have cap := size m.j
    unfold bad at h
    omega
  have under : ∀ x ∈ block m.j, x < start B := fun _ hb =>
    (in_block.mp hb).2.trans_le (start_mono lt)
  obtain ⟨z,hp,hz,_⟩ := bad_new v h
  intro y hy
  change y ∈ insert m.x (deny s p) at hy
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact under _ m.cell
  rw [hp] at hy
  change y ∈ insert z s.used at hy
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact under _ hz
  · exact old _ hy

/-- If a block stayed unfinished, all sufficiently late moves would be repairs:
injectivity eventually takes the play past the block. Repeated repairs can only
use a bounded set of ranks, contradicting injectivity again. -/
private theorem filled {q G} (size : ∀ j, 2*q j+1 ≤ j+3) (r : Run G q) (j : Nat) :
    ∃ n, mass (marks (r.st n)) j = q j := by
  by_contra! no
  have openCell (n) : mass (marks (r.st n)) j < q j :=
    Nat.lt_of_le_of_ne ((r.valid n).cap j) (no n)
  obtain ⟨N,esc⟩ := escapes (played_inj r) (start (j+1))
  have forced (n) (hn : N ≤ n) : bad q (r.st n) (pending G (r.st n)) (r.move n).j := by
    rcases (r.move n).reason with h|priority
    · exact h
    · have before := priority j (openCell n)
      have low := esc n hn
      have high := (in_block.mp (r.move n).cell).2
      have hbound : start ((r.move n).j+1) ≤ start (j+1) := start_mono (by omega)
      change start (j+1) ≤ (r.move n).x at low
      omega
  obtain ⟨B,finite⟩ := boundFin (r.st N).used
  have stays (k) : ∀ y ∈ (r.st (N+k)).used, y < start B := by
    induction k with
    | zero => exact finite
    | succ k ih =>
      rw [Nat.add_succ,r.advance]
      exact repair_bound size (r.valid _) (r.move _) (forced _ (by omega)) ih
  obtain ⟨M,escB⟩ := escapes (played_inj r) (start B)
  have lt := stays (M+1) (played r (N+M)) (by
    rw [Nat.add_succ,r.advance]
    exact Finset.mem_insert_self ..)
  have ge := escB (N+M) (by omega)
  omega

private theorem appeared (e : Nat → Nat) (f : Finset Nat) :
    ∃ N, ∀ x ∈ f, x ∈ Set.range e → ∃ t < N, e t = x := by
  induction f using Finset.induction_on with
  | empty => simp
  | @insert a f ha ih =>
    obtain ⟨N,old⟩ := ih
    by_cases hit : a ∈ Set.range e
    · obtain ⟨i,hi⟩ := hit
      refine ⟨max N (i+1),fun x hx ran => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact ⟨i,by omega,hi⟩
      · obtain ⟨t,lt,ht⟩ := old _ hx ran
        exact ⟨t,by omega,ht⟩
    · refine ⟨N,fun x hx ran => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact (hit ran).elim
      · exact old _ hx ran

private theorem marked {q G} (r : Run G q) (n x) :
    x ∈ marks (r.st n) ↔ ∃ t < n, played r t = x := by
  unfold marks
  rw [List.mem_toFinset,hist_eq,mem_seenPrefix]

private theorem quota_filled {q G} (size : ∀ j, 2*q j+1 ≤ j+3) (r : Run G q) (j) :
    blockCount (Set.range (played r)) j = q j := by
  classical
  obtain ⟨N,ev⟩ := appeared (played r) (block j)
  obtain ⟨M,eq⟩ := filled size r j
  let K := max N M
  have hm : marks (r.st M) ⊆ marks (r.st K) := by
    intro x hx
    obtain ⟨t,lt,ht⟩ := (marked r _ _).mp hx
    exact (marked r _ _).mpr ⟨t,lt.trans_le (Nat.le_max_right ..),ht⟩
  have mass_eq : mass (marks (r.st K)) j = q j :=
    Nat.le_antisymm ((r.valid K).cap j) (eq ▸ mass_mono hm j)
  have sets : (block j).filter (fun x => x ∈ Set.range (played r)) = block j ∩ marks (r.st K) := by
    ext x
    rw [Finset.mem_filter,Finset.mem_inter,marked]
    constructor
    · rintro ⟨hb,hr⟩
      obtain ⟨t,lt,ht⟩ := ev _ hb hr
      exact ⟨hb,t,lt.trans_le (Nat.le_max_left ..),ht⟩
    · rintro ⟨hb,t,_,ht⟩
      exact ⟨hb,t,ht⟩
  unfold blockCount
  rw [sets]
  exact mass_eq

private theorem used_mono {q G} (r : Run G q) {i j} (h : i ≤ j) : (r.st i).used ⊆ (r.st j).used := by
  induction h with
  | refl => exact fun _ h => h
  | @step n h ih =>
    rw [r.advance]
    exact fun _ hx => Finset.mem_insert_of_mem (old_deny _ _ (ih hx))

private theorem excludes {q G} (r : Run G q) (legal : Legal G) :
    ∀ x ∈ Set.range (played r), x ∉ Outputs G (played r) := by
  rintro x ⟨j,rfl⟩ ⟨t,hit⟩
  have one : pending G (r.st (t+1)) = some (played r j) := by
    unfold pending
    rw [hist_eq]
    change (if (played r t :: seenPrefix (played r) t).isEmpty = true then _ else _) = _
    simpa using hit
  by_cases early : j < t+1
  · have seen := mem_seenPrefix.mpr (show ∃ i < t+1, played r i = played r j from ⟨j,early,rfl⟩)
    have ok := (r.valid (t+1)).list
    rw [hist_eq] at ok
    exact legal _ ok _ seen hit
  · have stored : played r j ∈ deny (r.st (t+1)) (pending G (r.st (t+1))) := by
      rw [one]
      exact Finset.mem_insert_self ..
    by_cases eq : j = t+1
    · subst j
      exact (r.move _).free stored
    · have hs : played r j ∈ (r.st (t+1+1)).used := by
        rw [r.advance]
        exact Finset.mem_insert_of_mem stored
      exact (r.move j).free (old_deny _ _ (used_mono r (show t+1+1 ≤ j by omega) hs))

/-- An online adversary meets every block quota while avoiding every output of the generator. -/
theorem quotaPlay {q : Nat → Nat} (size : ∀ j, 2*q j+1 ≤ j+3)
    (inf : ∀ n, ∃ j ≥ n, 0 < q j) (G : Strategy) (legal : Legal G) :
    ∃ e : Nat → Nat, Function.Injective e ∧
      (∀ j, blockCount (Set.range e) j = q j) ∧ ∀ x ∈ Set.range e, x ∉ Outputs G e := by
  let r := makeRun size inf G
  exact ⟨played r,played_inj r,quota_filled size r,excludes r legal⟩

end SingletonDensity
