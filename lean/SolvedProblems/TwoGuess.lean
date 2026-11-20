module

public import SolvedProblems.TwoGuessModel
public import Std

public section

namespace TwoGuess

private def height : Word → Nat
  | .privateWord _ r => r
  | .edgeWord _ _ _ r => r

private def guesses (s : List Word) : List Word :=
  let r := 1 + (s.map height).foldr max 0
  match s with
  | [] => []
  | .privateWord u _ :: _ => [.privateWord u r]
  | .edgeWord n a b _ :: _ => [.privateWord (n,a) r,.privateWord (n,b) r]

private theorem maxBound (s : List Nat) : ∀ x ∈ s, x ≤ s.foldr max 0 := by
  induction s with
  | nil => simp
  | cons a s ih =>
    intro x mem
    rcases List.mem_cons.mp mem with rfl | hm
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih x hm) (Nat.le_max_right ..)

private theorem generate (s : List Word) : (guesses s).length ≤ 2 ∧
    ∀ v, s ≠ [] → (∀ x ∈ s, belongs v x) →
      ∃ x ∈ guesses s, x ∉ s ∧ belongs v x := by
  let r := 1 + (s.map height).foldr max 0
  have fresh (v) : Word.privateWord v r ∉ s := by
    intro h
    have := maxBound _ _ (List.mem_map.mpr ⟨_,h,rfl⟩ :
      height (.privateWord v r) ∈ s.map height)
    change r ≤ (s.map height).foldr max 0 at this
    dsimp [r] at this
    omega
  cases s with
  | nil => simp [guesses]
  | cons w s =>
    cases w with
    | privateWord u h =>
      refine ⟨by simp [guesses], fun v _ good => ?_⟩
      have eq := good (.privateWord u h) (by simp)
      exact ⟨.privateWord u r,by simp [guesses,r],fresh u,eq⟩
    | edgeWord n a b z =>
      refine ⟨by simp [guesses],fun v _ good => ?_⟩
      have hv := good (.edgeWord n a b z) (by simp)
      rcases hv.2.2.2 with rfl | rfl <;>
        exact ⟨.privateWord _ r,by simp [guesses,r],fresh _,rfl⟩

private theorem sameColour {q n : Nat} (c : Nat → Fin q) (hn : q < n) :
    ∃ a b, a < b ∧ b < n ∧ c a = c b := by
  classical
  apply Classical.byContradiction
  intro none
  let colors := (List.range n).map (fun i => (c i).val)
  have nd : colors.Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj eq
    simp [colors] at hi hj eq
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro h
      exact none ⟨j,i,h,hi,Fin.ext eq.symm⟩
    · apply Nat.le_of_not_gt
      intro h
      exact none ⟨i,j,h,hj,Fin.ext eq⟩
  have le := nd.length_le_of_subset (l₂ := List.range q) (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    simp)
  simp [colors] at le
  omega

private def shared (n a b : Nat) := (List.range n).map (Word.edgeWord n a b)

private theorem blocks (q : Nat) (colour : Vertex → Fin q) (limit : Nat) :
    ∃ u v : Vertex, u ≠ v ∧ colour u = colour v ∧ ∃ s : List Word,
      s.Nodup ∧ limit ≤ s.length ∧ ∀ x, x ∈ s ↔ belongs u x ∧ belongs v x := by
  let n := max q limit + 1
  obtain ⟨a,b,lt,bn,same⟩ := sameColour (n := n) (fun k => colour (n,k)) (by dsimp [n]; omega)
  refine ⟨(n,a),(n,b),by simp; omega,same,shared n a b,?_,?_,?_⟩
  · apply List.nodup_iff_eq_of_getElem_eq.mpr
    simp [shared]
  · simp [shared,n]
    omega
  · intro x
    cases x with
    | privateWord u h => simp [shared,belongs]; grind
    | edgeWord m c d h =>
      simp [shared,belongs]
      constructor
      · rintro ⟨i,hi,rfl,rfl,rfl,rfl⟩
        simp [lt,bn,hi]
      · rintro ⟨⟨cd,dm,hm,u⟩,⟨_,_,_,v⟩⟩
        refine ⟨h,?_,?_,?_,?_,rfl⟩ <;> grind

/-- Two guesses suffice after one observation. Every finite colouring has a
single colour with arbitrarily large exhausted intersections of two targets. -/
theorem twoGuessSeparation :
    (∃ G : List Word → List Word, ∀ s, (G s).length ≤ 2 ∧
      ∀ v, s ≠ [] → (∀ x ∈ s, belongs v x) →
        ∃ x ∈ G s, x ∉ s ∧ belongs v x) ∧
    (∀ q (colour : Vertex → Fin q), ∃ c, ∀ t, ∃ u v : Vertex,
      u ≠ v ∧ colour u = c ∧ colour v = c ∧ ∃ s : List Word,
        s.Nodup ∧ t ≤ s.length ∧ ∀ x, x ∈ s ↔ belongs u x ∧ belongs v x) := by
  classical
  refine ⟨⟨guesses,generate⟩,fun q colour => ?_⟩
  apply Classical.byContradiction
  intro none
  let good (c : Fin q) (t : Nat) := ∃ u v : Vertex,
    u ≠ v ∧ colour u = c ∧ colour v = c ∧ ∃ s : List Word,
      s.Nodup ∧ t ≤ s.length ∧ ∀ x, x ∈ s ↔ belongs u x ∧ belongs v x
  have stops (c : Fin q) : ∃ t, ¬ good c t := by
    apply Classical.byContradiction
    intro h
    exact none ⟨c,fun t => Classical.byContradiction fun bad => h ⟨t,bad⟩⟩
  let limits := List.ofFn (fun c => (stops c).choose)
  obtain ⟨u,v,ne,same,s,nd,len,inter⟩ := blocks q colour (limits.foldr max 0)
  apply (stops (colour u)).choose_spec
  exact ⟨u,v,ne,rfl,same.symm,s,nd,Nat.le_trans (maxBound limits _ (List.mem_ofFn.mpr ⟨colour u,rfl⟩)) len,inter⟩

end TwoGuess
