module

public import SolvedProblems.PromptModel
public import SolvedProblems.SoundCoverage
public import Std

public section

namespace PromptGeneration
open SoundCoverage

private theorem mem_trace {e : Nat → α} {n x} :
    x ∈ trace e n ↔ ∃ i ≤ n, e i = x := by simp [trace, Nat.lt_succ_iff]

/-- Replace off-label rounds by the first observed on-label word. Keeping repetitions
preserves the round clock and gives an ordinary full positive text. -/
private noncomputable def projected {Y} (rs : List (Round Y)) (y : Y) : List Nat := by
  classical
  let first := (rs.find? (fun r => decide (r.label = y))).map Round.word
  exact rs.map (fun r => if r.label = y then r.word else first.getD 0)

theorem fiberReduction {Y : Type} (C : (Nat → Y) → Prop)
    (inhabitedFiber : ∀ h, C h → ∀ y, ∃ x, h x = y) :
    prompted C ↔ ∀ y, ordinary (fun A => ∃ h, C h ∧ A = fiber h y) := by
  classical
  constructor
  · rintro ⟨G,good⟩ y
    let lift (x : Nat) : Round Y := ⟨x,y,y⟩
    refine ⟨fun xs => G (xs.map lift) y, ?_⟩
    rintro A ⟨h,hC,rfl⟩ e he
    let stream i := lift (e i)
    have labels (i) : (stream i).label = h (stream i).word :=
      ((he _).mpr ⟨i,rfl⟩).symm
    obtain ⟨N,hN⟩ := good h hC stream labels y (fun x hx => (he x).mp hx)
    refine ⟨N,fun n hn => ?_⟩
    have ok := hN n hn rfl
    have eq : trace stream n = (trace e n).map lift := by simp [trace,stream,Function.comp_def]
    rw [eq] at ok
    exact ⟨ok.1,fun mem => let ⟨i,hi,hw⟩ := mem_trace.mp mem; ok.2 i hi hw⟩
  · intro generators
    let G (y : Y) := (generators y).choose
    refine ⟨fun rs y => G y (projected rs y), ?_⟩
    intro h hC e labels y exhaust
    obtain ⟨p,hp⟩ := inhabitedFiber h hC y
    obtain ⟨t,ht⟩ := exhaust p hp
    let pred := fun r : Round Y => decide (r.label = y)
    have found : (trace e t).any pred := List.any_eq_true.mpr
      ⟨e t,mem_trace.mpr ⟨t,Nat.le_refl _,rfl⟩,by simp [pred,labels,ht,hp]⟩
    obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp (by simpa using found :
      ((trace e t).find? pred).isSome)
    have ry : r.label = y := by simpa [pred] using List.find?_some hr
    let f (i) := if (e i).label = y then (e i).word else r.word
    have rmem := List.mem_of_find?_eq_some hr
    obtain ⟨u,_,hu⟩ := mem_trace.mp rmem
    have trueR : h r.word = y := by simpa [← hu, ← labels] using ry
    have full : Enumerates f (fiber h y) := by
      intro x
      constructor
      · intro hx
        change h x = y at hx
        obtain ⟨i,hi⟩ := exhaust x hx
        exact ⟨i,by simp [f,labels,hi,hx]⟩
      · rintro ⟨i,rfl⟩
        simp only [fiber,f]
        split <;> grind
    obtain ⟨N,hN⟩ := (generators y).choose_spec _ ⟨h,hC,rfl⟩ f full
    refine ⟨max N t,fun n hn _ => ?_⟩
    have pref : (trace e t).IsPrefix (trace e n) := by
      apply List.IsPrefix.map
      apply List.prefix_iff_getElem.mpr
      exact ⟨by simp; omega, by simp⟩
    obtain ⟨tail,htail⟩ := pref
    have still : (trace e n).find? pred = some r := by rw [← htail]; simp [hr]
    have proj : projected (trace e n) y = trace f n := by
      unfold projected
      simp only [show (trace e n).find? (fun r => decide (r.label = y)) = some r from still,
        Option.map_some, Option.getD_some]
      simp [trace,f,Function.comp_def]
    dsimp only
    rw [proj]
    obtain ⟨positive,fresh⟩ := hN n (by omega)
    refine ⟨positive,fun i hi eq => ?_⟩
    apply fresh
    have hy : (e i).label = y := (labels i).trans (by rw [eq]; exact positive)
    exact mem_trace.mpr ⟨i,hi,by change (if (e i).label = y then _ else _) = _; simpa only [hy, ↓reduceIte] using eq⟩


/-- Search from the largest prefix of the indexed family down. Stop once all
consistent candidates in that prefix share an unseen point. -/
private noncomputable def search (P : Nat → Nat → Prop) : Nat → Nat := by
  classical
  exact Nat.rec (if h : ∃ x, P 0 x then h.choose else 0)
    (fun i old => if h : ∃ x, P (i+1) x then h.choose else old)

private theorem search_spec {P : Nat → Nat → Prop}
    (mono : ∀ i j, i ≤ j → ∀ x, P j x → P i x) {i m : Nat}
    (le : i ≤ m) (ex : ∃ x, P i x) : P i (search P m) := by
  classical
  induction m with
  | zero =>
    have := Nat.eq_zero_of_le_zero le
    subst i
    change P 0 (if h : ∃ x, P 0 x then h.choose else 0)
    simpa only [dite_eq_left ex] using ex.choose_spec
  | succ m ih =>
    by_cases h : ∃ x, P (m+1) x
    · simpa [search,h] using mono i (m+1) le _ h.choose_spec
    · have ne : i ≠ m+1 := fun he => h (he ▸ ex)
      simpa [search,h] using ih (by omega)

private theorem ordinary_countable (A : Family) (inf : ∀ i, unbounded (A i)) :
    ordinary (fun H => ∃ i, H = A i) := by
  classical
  let P (s : List Nat) (j x : Nat) := x ∉ s ∧ ∀ i ≤ j, Inside s (A i) → A i x
  let G (s : List Nat) := search (P s) s.length
  refine ⟨G,?_⟩
  rintro H ⟨i,rfl⟩ e he
  obtain ⟨N,hN⟩ := SoundCoverage.eliminate he (i+1)
  refine ⟨max N i,fun n hn => ?_⟩
  let s := trace e n
  have valid : Inside s (A i) := by
    intro x hx
    obtain ⟨k,_,hk⟩ := mem_trace.mp hx
    exact (he _).mpr ⟨k,hk⟩
  obtain ⟨w,hw,aw⟩ := inf i (s.foldr max 0)
  have upper (l : List Nat) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih x hx) (Nat.le_max_right ..)
  have safe : P s i w := ⟨fun mem => Nat.not_le_of_gt hw (upper s _ mem),
    fun j hj hs => hN (n+1) (by omega) j (by omega) hs w aw⟩
  have ok := search_spec (P := P s)
    (fun a b hab x h => ⟨h.1,fun j hj => h.2 j (Nat.le_trans hj hab)⟩)
    (i := i) (m := s.length) (by simp [s,trace]; omega) ⟨w,safe⟩
  exact ⟨ok.2 i (Nat.le_refl _) valid,ok.1⟩

/-- Countably many hypotheses suffice for arbitrary prompt alphabets. -/
theorem countablePrompts {Y : Type} (H : Nat → Nat → Y)
    (inf : ∀ i y, unbounded (fiber (H i) y)) :
    prompted (fun h => ∃ i, h = H i) := by
  apply (fiberReduction _ ?_).mpr
  · intro y
    have gen := ordinary_countable (fun i => fiber (H i) y) (fun i => inf i y)
    obtain ⟨G,hG⟩ := gen
    refine ⟨G,?_⟩
    rintro A ⟨h,⟨i,rfl⟩,rfl⟩
    exact hG _ ⟨i,rfl⟩
  · rintro h ⟨i,rfl⟩ y
    obtain ⟨x,_,hx⟩ := inf i y 0
    exact ⟨x,hx⟩

end PromptGeneration
