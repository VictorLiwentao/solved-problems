module

public import SolvedProblems.LastGuessModel
public import Std

public section

namespace LastGuess

private def row : Word → Nat
  | .marker => 0
  | .column _ r => r

private theorem rowBound (ws : List Word) :
    ∃ b, ∀ w ∈ ws, row w ≤ b := by
  induction ws with
  | nil => exact ⟨0, by simp⟩
  | cons w ws ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨max (row w) b, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (hb x hx) (Nat.le_max_right ..)

/-- Distinct thresholds disagree on a whole infinite column. -/
theorem approx_iff_eq {i j : Nat} : Approx i j ↔ i = j := by
  constructor
  · rintro ⟨ws, agree⟩
    obtain ⟨b, hb⟩ := rowBound ws
    have test (m) : i ≤ m ↔ j ≤ m := by
      apply agree (.column m (b+1))
      intro hm
      have h := hb _ hm
      change b+1 ≤ b at h
      omega
    have := (test i).mp (Nat.le_refl _)
    have := (test j).mpr (Nat.le_refl _)
    omega
  · rintro rfl
    exact ⟨[], fun _ _ => Iff.rfl⟩

/-- Walk through pairs by diagonals of constant m+r. -/
private def next : Nat × Nat → Nat × Nat
  | (0,r) => (r+1,0)
  | (m+1,r) => (m,r+1)

private def pairAt : Nat → Nat × Nat
  | 0 => (0,0)
  | k+1 => next (pairAt k)

private def index : Nat → Nat → Nat
  | 0, 0 => 0
  | m+1, 0 => index 0 m + 1
  | m, r+1 => index (m+1) r + 1
termination_by m r => (m+r,r)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · rw [show m + 1 + r = m + r.succ by omega]
    apply Prod.Lex.right
    omega

private theorem pairAt_index (m r) : pairAt (index m r) = (m,r) := by
  fun_induction index m r <;> simp_all [pairAt, next]

private theorem index_pairAt (k) : index (pairAt k).1 (pairAt k).2 = k := by
  induction k with
  | zero => simp [pairAt, index]
  | succ k ih =>
    generalize he : pairAt k = p at *
    obtain ⟨m,r⟩ := p
    cases m <;> simpa [pairAt, he, next, index] using congrArg Nat.succ ih

private theorem diagonal_bound (k) : (pairAt k).1 + (pairAt k).2 ≤ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    generalize he : pairAt k = p at ih
    obtain ⟨m,r⟩ := p
    cases m <;> simp [pairAt, he, next] at * <;> omega

private def canonical (n : Nat) : Nat → Word
  | 0 => .marker
  | k+1 => .column (n + (pairAt k).1) (pairAt k).2

private theorem canonical_text (n) : Text n (canonical n) := by
  intro w
  constructor
  · intro hw
    cases w with
    | marker => exact ⟨0,rfl⟩
    | column m r =>
      change n ≤ m at hw
      exact ⟨index (m-n) r + 1, by simp [canonical, pairAt_index]; omega⟩
  · rintro ⟨k,rfl⟩
    cases k <;> simp [canonical, target]

private theorem canonical_unique (n) : NoRepeats (canonical n) := by
  intro i j h
  cases i <;> cases j <;> simp_all [canonical]
  rename_i i j
  obtain ⟨h₁,h₂⟩ := h
  rw [← index_pairAt i, h₁, h₂, index_pairAt]

private theorem impossible (first : Word → Nat) (update : Nat → Word → Nat) :
    ∃ n e, Text n e ∧ NoRepeats e ∧ ¬ Eventually (fun k => Approx (run first update e k) n) := by
  classical
  apply Classical.byContradiction
  intro none
  have settles (n) : Eventually (fun k => run first update (canonical n) k = n) := by
    have h : Eventually (fun k => Approx (run first update (canonical n) k) n) :=
      Classical.byContradiction fun hn =>
        none ⟨n, canonical n, canonical_text n, canonical_unique n, hn⟩
    obtain ⟨N,hN⟩ := h
    exact ⟨N, fun k hk => approx_iff_eq.mp (hN k hk)⟩
  let j := first .marker
  obtain ⟨N,hN⟩ := settles j
  let n := j+N+1
  -- Every column at or above n first occurs beyond stabilization on the text for j.
  have absorbs (m r) (hm : n ≤ m) : update j (.column m r) = j := by
    let k := index (m-j) r
    have hp : pairAt k = (m-j,r) := pairAt_index ..
    have bound := diagonal_bound k
    rw [hp] at bound
    simp at bound
    have late : N ≤ k := by dsimp [n] at hm; omega
    have h := hN (k+1) (by omega)
    change update (run first update (canonical j) k) (canonical j (k+1)) = j at h
    rw [hN k late] at h
    simpa [canonical, hp, Nat.add_sub_cancel' (show j ≤ m by dsimp [n] at hm; omega)] using h
  have stuck (k) : run first update (canonical n) k = j := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [run, ih]
      exact absorbs _ _ (Nat.le_add_right ..)
  obtain ⟨K,hK⟩ := settles n
  have eq := (stuck K).symm.trans (hK K (Nat.le_refl _))
  dsimp [n] at eq
  omega

private def remember (s : Nat × Bool) : Word → Nat × Bool
  | .marker => s
  | .column m _ => (if s.2 then min s.1 m else m, true)

private theorem oneBitWorks (n) (e : Nat → Word) (he : Text n e) :
    Eventually (fun k => (run (remember (0,false)) remember e k).1 = n) := by
  let state := run (remember (0,false)) remember e
  have valid (k) : target n (e k) := (he _).mpr ⟨k,rfl⟩
  have lower (s : Nat × Bool) (hs : s.2 = true → n ≤ s.1) (w) (hw : target n w) :
      (remember s w).2 = true → n ≤ (remember s w).1 := by
    cases w with
    | marker => exact hs
    | column m r =>
      cases hb : s.2 <;> simp_all [remember, target] <;> omega
  have inv (k) : (state k).2 = true → n ≤ (state k).1 := by
    induction k with
    | zero => exact lower (0,false) (by simp) _ (valid 0)
    | succ k ih => exact lower _ ih _ (valid (k+1))
  obtain ⟨N,hN⟩ := (he (.column n 0)).mp (Nat.le_refl _)
  have hit : state N = (n,true) := by
    cases N with
    | zero => simp [state, run, hN, remember]
    | succ k =>
      change remember (state k) (e (k+1)) = _
      rw [hN]
      cases hb : (state k).2 <;> simp_all [remember]
  have stays (k) (hk : N ≤ k) : state k = (n,true) := by
    induction hk with
    | refl => exact hit
    | @step k hk ih =>
      change remember (state _) (e _) = _
      rw [ih]
      generalize hw : e _ = w
      have legal := valid (k+1)
      rw [hw] at legal
      cases w <;> simp_all [remember, target]
  exact ⟨N, fun k hk => congrArg Prod.fst (stays k hk)⟩

/-- The deterministic main theorem. -/
theorem oneBitSeparation :
    (∀ (first : Word → Nat) (update : Nat → Word → Nat),
      ∃ n e, Text n e ∧ NoRepeats e ∧
        ¬ Eventually (fun k => Approx (run first update e k) n)) ∧
    (∃ (first : Word → Nat × Bool) (update : Nat × Bool → Word → Nat × Bool),
      ∀ n e, Text n e → Eventually (fun k => (run first update e k).1 = n)) := by
  exact ⟨impossible, remember (0,false), remember, oneBitWorks⟩


/-- The single word in column n with suffix length zero distinguishes every
strict sublanguage of target n in this family. -/
theorem singletonTelltale (n : Nat) :
    ∃ w, target n w ∧ ∀ j, target j w →
      (∀ x, target j x → target n x) → j = n := by
  refine ⟨.column n 0, Nat.le_refl _, ?_⟩
  intro j hw sub
  have h := sub (.column j 0) (Nat.le_refl _)
  exact Nat.le_antisymm hw h

end LastGuess
