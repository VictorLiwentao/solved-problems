module

public import SolvedProblems.GenerationThresholdModel

public section

namespace GenerationThreshold

@[simp] private theorem mem_distinct [DecidableEq α] (x : α) (s : List α) :
    x ∈ distinct s ↔ x ∈ s := by
  induction s with
  | nil => simp [distinct]
  | cons a s ih =>
    by_cases h : a ∈ s <;> simp [distinct, h, ih] <;> grind

private theorem simple [DecidableEq α] (s : List α) : (distinct s).Nodup := by
  induction s with
  | nil => simp [distinct]
  | cons a s ih => by_cases h : a ∈ s <;> simp [distinct, h, ih]

private theorem fixed [DecidableEq α] {s : List α} (h : s.Nodup) : distinct s = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp_all [List.nodup_cons, distinct]

private theorem fewer (H : Language) (s : List Edge) :
    violations H (distinct s) ≤ violations H s := by
  classical
  induction s with
  | nil => exact Nat.le_refl _
  | cons a s ih =>
    by_cases h : a ∈ s <;> by_cases c : crosses H a <;>
      simp_all [distinct, violations] <;> omega

private theorem sameFresh (s : List Edge) (x : Nat) : fresh (distinct s) x ↔ fresh s x := by
  simp [fresh]

/-- Every prefix within budget for a nonempty proper support is extendible.
The tail adds no violations and covers every positive, even if the prefix
covered none of them. This justifies testing the lower bound on finite inputs. -/
theorem honestContinuation (H : Language) (pos : ∃ x, H x) (neg : ∃ y, ¬ H y) :
    ∃ tail : Nat → Edge, (∀ i, crosses H (tail i)) ∧
      ∀ x, H x → ∃ i, (tail i).lo = x ∨ (tail i).hi = x := by
  classical
  obtain ⟨p,hp⟩ := pos
  obtain ⟨q,hq⟩ := neg
  let a (i : Nat) := if H i then i else p
  have good (i) : H (a i) := by unfold a; split <;> assumption
  let tail (i : Nat) : Edge := if h : a i < q then ⟨a i,q,h⟩ else
    ⟨q,a i,by
      have ne : a i ≠ q := fun eq => hq (eq ▸ good i)
      omega⟩
  refine ⟨tail,fun i => ?_,fun x hx => ⟨x,?_⟩⟩
  · dsimp [tail]
    split <;> simp [crosses,good,hq]
  · dsimp [tail]
    split <;> simp [a,hx]

/-- Characterizes *each* admissible threshold, including zero and the unbounded case. -/
theorem uniformCriterion (C : Class) (k t : Nat) :
    uniform C k t ↔ ∀ E, E.Nodup → obstruction C k E → E.length < t := by
  classical
  constructor
  · rintro ⟨G,hG⟩ E hE ⟨⟨H,hH,hv⟩,no⟩
    apply Nat.lt_of_not_ge
    intro size
    have big : t ≤ (distinct E).length := by rwa [fixed hE]
    exact no ⟨G E, (hG H hH E big hv).1, fun J hj hjv => (hG J hj E big hjv).2⟩
  · intro no
    let safe (s : List Edge) (x : Nat) :=
      fresh s x ∧ ∀ H, C H → violations H (distinct s) ≤ k → H x
    let G (s : List Edge) := if h : ∃ x, safe s x then h.choose else 0
    refine ⟨G, fun H hH s big budget => ?_⟩
    have hv := Nat.le_trans (fewer H s) budget
    have ex : ∃ x, safe s x := by
      apply Classical.byContradiction
      intro h
      apply Nat.not_lt_of_ge big
      apply no _ (simple s)
      refine ⟨⟨H,hH,hv⟩, ?_⟩
      rintro ⟨x,hx,good⟩
      exact h ⟨x,(sameFresh s x).mp hx,good⟩
    simpa [G, ex] using And.intro ex.choose_spec.1 (ex.choose_spec.2 H hH hv)

/-- A finite deletion budget is equivalent to admitting a clean remainder. -/
theorem deletionCriterion (H : Language) (E : List Edge) (k : Nat) (simpleE : E.Nodup) :
    violations H E ≤ k ↔ ∃ D : List Edge, D.Sublist E ∧ D.length ≤ k ∧
      ∀ e ∈ E, e ∉ D → crosses H e := by
  classical
  constructor
  · intro h
    exact ⟨_, List.filter_sublist, h, fun e he hn => Classical.byContradiction fun hc =>
      hn (List.mem_filter.mpr ⟨he, by simpa using hc⟩)⟩
  · rintro ⟨D,hd,hk,clean⟩
    apply Nat.le_trans _ hk
    apply List.Nodup.length_le_of_subset (simpleE.filter _)
    intro e he
    obtain ⟨hm,hbad⟩ := List.mem_filter.mp he
    exact Classical.byContradiction fun hn => (of_decide_eq_true hbad) (clean e hm hn)

/-- Largest eligible index at a finite stage, when one exists. -/
private theorem greatest (P : Nat → Prop) (m : Nat) (ex : ∃ j ≤ m, P j) :
    ∃ j, j ≤ m ∧ P j ∧ ∀ i ≤ m, P i → i ≤ j := by
  classical
  induction m with
  | zero =>
    obtain ⟨j,h,hj⟩ := ex
    exact ⟨j,h,hj,fun i hi _ => by omega⟩
  | succ m ih =>
    by_cases h : P (m+1)
    · exact ⟨_,Nat.le_refl _,h,fun _ hi _ => hi⟩
    · obtain ⟨j,hj,hp⟩ := ex
      have ne : j ≠ m+1 := fun e => h (e ▸ hp)
      obtain ⟨i,hi,pi,top⟩ := ih ⟨j,by omega,hp⟩
      refine ⟨i,by omega,pi,fun l hl pl => top l ?_ pl⟩
      have ne' : l ≠ m+1 := fun e => h (e ▸ pl)
      omega

/-- One rule with target-dependent thresholds exactly characterizes increasing
unions of classes with a finite uniform threshold. -/
theorem nonuniformCriterion (C : Class) (k : Nat) :
    (∃ G, ∀ H, C H → ∃ t, works G H k t) ↔
    ∃ A : Nat → Class, (∀ i j, i ≤ j → ∀ H, A i H → A j H) ∧
      (∀ H, C H ↔ ∃ i, A i H) ∧ ∀ i, ∃ t, uniform (A i) k t := by
  classical
  constructor
  · rintro ⟨G,hG⟩
    let A (i : Nat) (H : Language) := C H ∧ ∃ t ≤ i, works G H k t
    refine ⟨A, ?_, ?_, ?_⟩
    · rintro i j hij H ⟨hH,t,ht,good⟩
      exact ⟨hH,t,Nat.le_trans ht hij,good⟩
    · intro H
      exact ⟨fun h => let ⟨t,ht⟩ := hG H h; ⟨t,h,t,Nat.le_refl _,ht⟩,
        fun ⟨_,h,_⟩ => h⟩
    · intro i
      refine ⟨i,G,?_⟩
      rintro H ⟨_,t,ht,good⟩ s hs
      exact good s (Nat.le_trans ht hs)
  · rintro ⟨A,mono,cover,avail⟩
    let d (i) := (avail i).choose
    let rule (i) := (avail i).choose_spec.choose
    let pick (m : Nat) := greatest (fun i => d i ≤ m) m
    let G (s : List Edge) := let m := (distinct s).length
      if h : ∃ i ≤ m, d i ≤ m then rule ((pick m h).choose) s else 0
    refine ⟨G, ?_⟩
    intro H hH
    obtain ⟨i,hi⟩ := (cover H).mp hH
    refine ⟨max i (d i), ?_⟩
    intro s size legal
    let m := (distinct s).length
    have im : i ≤ m := Nat.le_trans (Nat.le_max_left ..) size
    have dm : d i ≤ m := Nat.le_trans (Nat.le_max_right ..) size
    have ex : ∃ j ≤ m, d j ≤ m := ⟨i,im,dm⟩
    let j := (pick m ex).choose
    have hj := (pick m ex).choose_spec
    have ok := (avail j).choose_spec.choose_spec H (mono i j (hj.2.2 i im dm) H hi)
      s hj.2.1 legal
    simpa [G, m, ex, rule, j] using ok

/-- A finite threshold works iff every exhausted common intersection of that
size has a fresh transversal of at most k words. -/
theorem listThresholdCriterion (C : Class) (k t : Nat) (positive : 0 < k) :
    listUniform C k t ↔ ∀ I, I.Nodup → listObstruction C k I → I.length < t := by
  classical
  constructor
  · rintro ⟨G,hG⟩ I hI ⟨F,_,sub,inter,blocked⟩
    apply Nat.lt_of_not_ge
    intro big
    apply blocked
    refine ⟨G I,(hG I).1,fun H hH => (hG I).2 H (sub H hH) ?_ ?_⟩
    · exact fun x hx => (inter x).mp hx H hH
    · simpa [fixed hI] using big
  · intro bound
    have possible (s : List Nat) :
        ∃ a : List Nat, a.length ≤ k ∧ ∀ H, C H → (∀ x ∈ s, H x) →
          t ≤ (distinct s).length → hits a s H := by
      let F (H : Language) := C H ∧ ∀ x ∈ s, H x
      by_cases active : ∃ H, F H
      · by_cases bigger : ∃ x, x ∉ s ∧ ∀ H, F H → H x
        · obtain ⟨x,hx,all⟩ := bigger
          exact ⟨[x],positive,fun H hC hs _ => ⟨x,by simp,hx,all H ⟨hC,hs⟩⟩⟩
        · by_cases trans : ∃ a : List Nat, a.length ≤ k ∧ ∀ H, F H → hits a (distinct s) H
          · obtain ⟨a,ha,hit⟩ := trans
            exact ⟨a,ha,fun H hC hs _ => by simpa [hits] using hit H ⟨hC,hs⟩⟩
          · have small := bound (distinct s) (simple s)
            have inter (x) : x ∈ distinct s ↔ ∀ H, F H → H x := by
              rw [mem_distinct]
              exact ⟨fun hx H h => h.2 x hx,fun h => Classical.byContradiction
                fun hx => bigger ⟨x,hx,h⟩⟩
            have lt := small ⟨F,active,fun _ h => h.1,inter,trans⟩
            exact ⟨[],by simp,fun _ _ _ h => False.elim (by omega)⟩
      · exact ⟨[],by simp,fun H hC hs _ => False.elim (active ⟨H,hC,hs⟩)⟩
    exact ⟨fun s => (possible s).choose,fun s => (possible s).choose_spec⟩

end GenerationThreshold
