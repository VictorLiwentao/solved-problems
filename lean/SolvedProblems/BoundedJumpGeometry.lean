module

public import SolvedProblems.BoundedJumpRelations
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Preorder.Finite

public section

namespace BoundedJump

private def Next (p : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  (p i).val + 1 = (p j).val

private theorem reach_refl (w : Fin n → Letter m) (x : Fin n) : Reach w x x :=
  fun _ h _ => h

private theorem reach_trans {w : Fin n → Letter m} {x y z : Fin n}
    (h : Reach w x y) (k : Reach w y z) : Reach w x z :=
  fun s hs closed => k s (h s hs closed) closed

private theorem enumerate (α : Type) [Fintype α] (r : α → α → Prop) [IsStrictTotalOrder α r]
    (hc : Fintype.card α = n) : ∃ p : α ≃ Fin n, ∀ i j, r i j ↔ p i < p j := by
  classical
  letI : LinearOrder α := linearOrderOfSTO r
  let e := Fintype.orderIsoFinOfCardEq α hc
  exact ⟨e.symm.toEquiv, fun i j => e.symm.lt_iff_lt.symm⟩

/-- Rank a finite strict total order by its unique increasing enumeration. -/
private theorem rank_exists (w : Fin n → Letter m) (hw : Valid w) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j, Strict w i j ↔ p i < p j := by
  classical
  let : IsStrictTotalOrder (Fin n) (Strict w) := {
    irrefl := fun x h => h.2 rfl
    trans := fun x y z h k => ⟨reach_trans h.1 k.1, fun he => h.2 (hw.2.1 _ _ h.1 (he ▸ k.1))⟩
    trichotomous := fun x y h k => by
      by_contra ne
      exact (hw.2.2.1 x y).elim (fun r => h ⟨r,ne⟩) (fun r => k ⟨r,Ne.symm ne⟩) }
  exact enumerate _ (Strict w) (Fintype.card_fin n)

private theorem rank_unique (p q : Equiv.Perm (Fin n))
    (h : ∀ i j, p i < p j ↔ q i < q j) : p = q := by
  have mono : StrictMono (fun i => q (p.symm i)) := by
    intro i j hij
    exact (h _ _).mp (by simpa using hij)
  apply Equiv.ext
  intro i
  simpa using (congrFun mono.eq_id (p i)).symm

private theorem next_cover (p : Equiv.Perm (Fin n)) (i j : Fin n) :
    Next p i j ↔ p i < p j ∧ ¬ ∃ z, p i < p z ∧ p z < p j := by
  unfold Next
  constructor
  · intro h
    exact ⟨show (p i).val < (p j).val by omega, fun ⟨z,a,b⟩ => by
      change (p i).val < (p z).val at a
      change (p z).val < (p j).val at b
      omega⟩
  · rintro ⟨h,hn⟩
    change (p i).val < (p j).val at h
    by_contra he
    let x : Fin n := ⟨(p i).val+1, by have := (p j).isLt; omega⟩
    apply hn
    refine ⟨p.symm x, ?_, ?_⟩ <;> rw [p.apply_symm_apply]
    · exact show (p i).val < (p i).val+1 by omega
    · exact show (p i).val+1 < (p j).val by omega

private theorem ranked_edges {w : Fin n → Letter m} (hw : Valid w) (p : Equiv.Perm (Fin n))
    (hr : ∀ i j, Strict w i j ↔ p i < p j) (i j : Fin n) :
    Edge w i j ↔ Next p i j := by
  rw [hw.2.2.2 i j, next_cover]
  simp only [hr]

private theorem edge_bound {w : Fin n → Letter m} {i j : Fin n}
    (h : Edge w i j) : Nat.dist i.val j.val ≤ m := by
  unfold Edge at h
  cases e : w i with
  | none => simp [e] at h
  | some a =>
    obtain ⟨b,k⟩ := a
    have := k.isLt
    cases b <;> simp [e] at h <;> unfold Nat.dist <;> omega

/-- Signed successor offsets for the permutation whose value i occurs at position p i. -/
private def encodeWord (p : Equiv.Perm (Fin n)) (bounded : ∀ i j, Next p i j →
    Nat.dist i.val j.val ≤ m) (i : Fin n) : Letter m :=
  if h : (p i).val+1 < n then
    let j := p.symm ⟨(p i).val+1,h⟩
    have hn : Next p i j := by simp [Next,j]
    have hd := bounded i j hn
    have ne : i.val ≠ j.val := by
      intro eq
      have same : i = j := Fin.ext eq
      unfold Next at hn
      rw [← same] at hn
      omega
    some (decide (i.val < j.val), ⟨Nat.dist i.val j.val - 1, by unfold Nat.dist at *; omega⟩)
  else none

private theorem encode_laws (p : Equiv.Perm (Fin n)) (bound : ∀ i j, Next p i j →
    Nat.dist i.val j.val ≤ m) :
    (∀ i, encodeWord p bound i ≠ none → ∃ j, Edge (encodeWord p bound) i j) ∧
    ∀ i j, Edge (encodeWord p bound) i j ↔ Next p i j := by
  have aux (i : Fin n) (h : (p i).val+1 < n) :
      ∀ j, Edge (encodeWord p bound) i j ↔ p.symm ⟨(p i).val+1,h⟩ = j := by
    let u := p.symm ⟨(p i).val+1,h⟩
    have ne : i.val ≠ u.val := by
      intro e
      have eq : i = u := Fin.ext e
      have pu : p u = ⟨(p i).val+1,h⟩ := p.apply_symm_apply _
      have hh : (p u).val = (p i).val+1 := congrArg Fin.val pu
      rw [← eq] at hh
      omega
    intro j
    simp only [encodeWord, dite_eq_left h, Edge]
    by_cases hi : i.val < u.val
    · rw [show decide (i.val < u.val) = true by simp [hi]]
      change (i.val + (Nat.dist i.val u.val - 1 + 1) = j.val) ↔ u = j
      rw [Fin.ext_iff, Nat.dist]; omega
    · rw [show decide (i.val < u.val) = false by simp [hi]]
      change (j.val + (Nat.dist i.val u.val - 1 + 1) = i.val) ↔ u = j
      rw [Fin.ext_iff, Nat.dist]; omega
  constructor
  · intro i hn
    by_cases hi : (p i).val+1 < n
    · exact ⟨_, (aux i hi _).mpr rfl⟩
    · simp [encodeWord, hi] at hn
  · intro i j
    by_cases hi : (p i).val+1 < n
    · rw [aux i hi, Equiv.symm_apply_eq]
      exact Fin.ext_iff
    · simp [Edge, encodeWord, hi, Next]
      have := (p j).isLt
      omega

private theorem reach_ranked {w : Fin n → Letter m} (p : Equiv.Perm (Fin n))
    (he : ∀ i j, Edge w i j ↔ Next p i j) (i j : Fin n) :
    Reach w i j ↔ p i ≤ p j := by
  constructor
  · intro h
    let s (x : Fin n) := decide (p i ≤ p x)
    have hj := h s (by simp [s]) (by
      intro x y hx hxy
      have h := (he x y).mp hxy
      change (p x).val + 1 = (p y).val at h
      simp [s] at hx ⊢
      exact hx.trans (Fin.le_def.mpr (by omega)))
    simpa [s] using hj
  · intro hij s hs closed
    have walk (d : Nat) : ∀ (x : Fin n), (p x).val = (p i).val+d → s x = true := by
      induction d with
      | zero =>
        intro x h
        have eq : x = i := p.injective (Fin.ext (by simpa using h))
        simpa [eq] using hs
      | succ d ih =>
        intro x h
        have hx := (p x).isLt
        let a : Fin n := ⟨(p i).val+d, by omega⟩
        refine closed (p.symm a) x (ih _ (by simp [a])) ((he _ _).mpr ?_)
        simp [Next, a, h, Nat.add_assoc]
    exact walk ((p j).val-(p i).val) j (by change (p i).val ≤ (p j).val at hij; omega)

private theorem encode_valid (p : Equiv.Perm (Fin n)) (bound : ∀ i j, Next p i j →
    Nat.dist i.val j.val ≤ m) :
    Valid (encodeWord p bound) ∧ ∀ i j, Strict (encodeWord p bound) i j ↔ p i < p j := by
  obtain ⟨hlegal,he⟩ := encode_laws p bound
  have hr := reach_ranked p he
  have hs (i j : Fin n) : Strict (encodeWord p bound) i j ↔ p i < p j := by
    rw [Strict, hr, lt_iff_le_and_ne, p.injective.ne_iff]
  refine ⟨⟨hlegal, fun i j a b => p.injective (le_antisymm ((hr _ _).mp a) ((hr _ _).mp b)),
    fun i j => (le_total (p i) (p j)).imp (hr _ _).mpr (hr _ _).mpr, fun i j => ?_⟩,hs⟩
  rw [he, next_cover]
  simp only [hs]

private theorem words_unique {w v : Fin n → Letter m} (hw : Valid w) (hv : Valid v)
    (he : ∀ i j, Edge w i j ↔ Edge v i j) : w = v := by
  funext i
  cases a : w i with
  | none =>
    by_contra h
    obtain ⟨j,hj⟩ := hv.1 i (Ne.symm h)
    have := (he i j).mpr hj
    simp [Edge,a] at this
  | some a' =>
    obtain ⟨j,hj⟩ := hw.1 i (by simp [a])
    have hk := (he i j).mp hj
    cases b : v i with
    | none => simp [Edge,b] at hk
    | some b' =>
      obtain ⟨d,r⟩ := a'
      obtain ⟨e,t⟩ := b'
      cases d <;> cases e <;> simp [Edge,a,b] at hj hk ⊢ <;> omega

/-- Reading successor offsets in increasing order of values gives exactly one word for
each bounded-jump permutation, including the empty permutation. -/
noncomputable def wordEquiv (m : Nat) (B : List (List Nat)) (n : Nat) :
    {w : Fin n → Letter m // Valid w ∧ Avoid B (Strict w)} ≃
    {p : Equiv.Perm (Fin n) // Counted m B p} := by
  classical
  let rank (w : {w : Fin n → Letter m // Valid w ∧ Avoid B (Strict w)}) :=
    (rank_exists w.1 w.2.1).choose
  have hr (w : {w : Fin n → Letter m // Valid w ∧ Avoid B (Strict w)}) :=
    (rank_exists w.1 w.2.1).choose_spec
  let decode (w : {w : Fin n → Letter m // Valid w ∧ Avoid B (Strict w)}) :
      {p : Equiv.Perm (Fin n) // Counted m B p} :=
    ⟨rank w, fun i j h => edge_bound ((ranked_edges w.2.1 (rank w) (hr w) i j).mpr h), by
      simpa only [← show Strict w.1 = (fun i j => rank w i < rank w j) from
        funext fun i => funext fun j => propext (hr w i j)] using w.2.2⟩
  apply Equiv.ofBijective decode
  constructor
  · intro w v eq
    have eqp : rank w = rank v := congrArg Subtype.val eq
    apply Subtype.ext
    apply words_unique w.2.1 v.2.1
    intro i j
    rw [ranked_edges w.2.1 (rank w) (hr w), ranked_edges v.2.1 (rank v) (hr v), eqp]
  · intro p
    obtain ⟨valid, spec⟩ := encode_valid p.val p.property.1
    let w : {w : Fin n → Letter m // Valid w ∧ Avoid B (Strict w)} :=
      ⟨encodeWord p.val p.property.1, valid, by
        simpa only [show Strict (encodeWord p.val p.property.1) = (fun i j => p.val i < p.val j)
          from funext fun i => funext fun j => propext (spec i j)] using p.property.2⟩
    exact ⟨w, Subtype.ext (rank_unique _ _ (fun i j => (hr w i j).symm.trans (spec i j)))⟩

end BoundedJump
