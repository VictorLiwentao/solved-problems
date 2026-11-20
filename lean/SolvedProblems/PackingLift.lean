module

public import SolvedProblems.PackingLiftModel

public section

namespace PackingLift

private theorem Reaches.edge {e : α → α → Prop} {x y} (h : e x y) : Reaches e x y :=
  .snoc (.refl x) h

private theorem Reaches.trans {e : α → α → Prop} {x y z}
    (h : Reaches e x y) (g : Reaches e y z) : Reaches e x z := by
  induction g with
  | refl => exact h
  | snoc _ last ih => exact .snoc ih last

private theorem ordinal_trans {p j t h} {x y z : Lifted p j t h}
    (a : Ordinal p x y) (b : Ordinal p y z) : Ordinal p x z := by
  cases x <;> cases y <;> cases z <;> simp_all [Ordinal]
  · omega
  · exact a.trans b

private theorem sound {p j t h} {x y : Lifted p j t h}
    (g : Reaches (LiftEdge p j t h) x y) : Ordinal p x y := by
  induction g with
  | refl =>
    cases x <;> simp [Ordinal,Reaches.refl]
  | snoc _ last ih =>
    apply ordinal_trans ih
    obtain ⟨i,a,b,rfl,rfl,rank⟩ := last
    cases a with
    | inl a =>
      cases b with
      | inl b => exact Nat.add_le_add_left rank _
      | inr b => trivial
    | inr a =>
      cases b with
      | inl b =>
        change (t+h)+t+(p.rank a).val ≤ b.val at rank
        have := b.isLt
        omega
      | inr b =>
        exact Reaches.edge ⟨i,a,b,rfl,rfl,Nat.le_of_add_le_add_left rank⟩

/-- A position belongs to a window of length d+w and stride d. -/
private theorem window {d w j k : Nat} (copies : 0 < j) (inside : k < j*d+w) :
    ∃ i < j, i*d ≤ k ∧ k < i*d+d+w := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [Nat.succ_mul] at inside
    by_cases start : j*d ≤ k
    · exact ⟨j,by omega,start,inside⟩
    · have pos : 0 < j := by cases j <;> simp_all
      obtain ⟨i,hi,lo,up⟩ := ih pos (by omega)
      exact ⟨i,by omega,lo,up⟩

private theorem adjacent {p j t h} (hj : 0 < j) (ht : 0 < t)
    (a b : Fresh j t h) (adj : b.val = a.val+1) :
    LiftEdge p j t h (.inl a) (.inl b) := by
  let d := t+h
  have bnd : b.val < j*d+t := b.isLt
  obtain ⟨i,hi,lo,up⟩ := window (d := d) (w := t-1) hj
    (show a.val < j*d+(t-1) by omega)
  let w : Fin j := ⟨j-1-i,by omega⟩
  have rev : j-1-w.val = i := by dsimp [w]; omega
  let offsetA : Fin (d+t) := ⟨a.val-i*d,by omega⟩
  let offsetB : Fin (d+t) := ⟨b.val-i*d,by omega⟩
  refine ⟨w,.inl offsetA,.inl offsetB,?_,?_,?_⟩
  · apply congrArg Sum.inl
    apply Fin.ext
    change a.val = (j-1-w.val)*d + (a.val-i*d)
    rw [rev]; omega
  · apply congrArg Sum.inl
    apply Fin.ext
    change b.val = (j-1-w.val)*d + (b.val-i*d)
    rw [rev]; omega
  · change a.val-i*d ≤ b.val-i*d
    omega

private theorem chain {p j t h} (hj : 0 < j) (ht : 0 < t) (a b : Fresh j t h)
    (le : a.val ≤ b.val) : Reaches (LiftEdge p j t h) (.inl a) (.inl b) := by
  obtain ⟨b,bnd⟩ := b
  change a.val ≤ b at le
  induction le with
  | refl => exact .refl _
  | @step k _ ih =>
    have bound : k < j*(t+h)+t := by omega
    exact .snoc (ih bound) (adjacent hj ht ⟨k,bound⟩ ⟨k+1,bnd⟩ rfl)

private theorem oldPath {p j t h} {x y : Old p j} (g : Reaches (OldEdge p j) x y) :
    Reaches (LiftEdge p j t h) (.inr x) (.inr y) := by
  induction g with
  | refl => exact .refl _
  | snoc _ last ih =>
    obtain ⟨i,a,b,rfl,rfl,rank⟩ := last
    exact .snoc ih ⟨i,.inr a,.inr b,rfl,rfl,Nat.add_le_add_left rank _⟩

/-- The minimum of each window is shared with its predecessor, except at
the first window. This puts every original position above the fresh chain. -/
private theorem chainBelow {p j t h} (hj : 0 < j) (ht : 0 < t)
    (x : Fresh j t h) (y : Old p j) : Reaches (LiftEdge p j t h) (.inl x) (.inr y) := by
  obtain ⟨a,minimum⟩ := p.minimumInPrefix
  let m : Slot p := ⟨a,by have := a.isLt; omega⟩
  have least (z : Slot p) : p.rank m ≤ p.rank z := by
    change (p.rank m).val ≤ _
    change (p.rank m).val = 0 at minimum
    omega
  have below (n : Nat) (hn : n < j) (z : Slot p) :
      Reaches (LiftEdge p j t h) (.inl x) (.inr (oldAt p ⟨n,hn⟩ z)) := by
    induction n generalizing z with
    | zero =>
      let i : Fin j := ⟨0,hj⟩
      let top : Fin ((t+h)+t) := ⟨(t+h)+t-1,by omega⟩
      have endLe : x.val ≤ (newAt i top).val := by
        have total := Nat.succ_mul (j-1) (t+h)
        rw [show (j-1).succ=j by omega] at total
        have := x.isLt
        change x.val ≤ (j-1)*(t+h)+((t+h)+t-1)
        omega
      apply Reaches.snoc (chain hj ht x _ endLe)
      refine ⟨i,.inl top,.inr z,rfl,rfl,?_⟩
      change (t+h)+t-1 ≤ ((t+h)+t)+(p.rank z).val
      omega
    | succ n ih =>
      let prev : Slot p := ⟨p.stride+a.val,by have := a.isLt; omega⟩
      have eq : oldAt p (j := j) ⟨n,by omega⟩ prev = oldAt p ⟨n+1,hn⟩ m := by
        apply Fin.ext
        simp [oldAt,prev,m,Nat.succ_mul,Nat.add_assoc]
      have before := ih (by omega) prev
      rw [eq] at before
      exact .snoc before ⟨⟨n+1,hn⟩,.inr m,.inr z,rfl,rfl,Nat.add_le_add_left (least z) _⟩
  obtain ⟨n,hn,lo,up⟩ := window hj y.isLt
  let z : Slot p := ⟨y.val-n*p.stride,by omega⟩
  have eq : y = oldAt p ⟨n,hn⟩ z := by apply Fin.ext; change y.val = n*p.stride+(y.val-n*p.stride); omega
  rw [eq]
  exact below n hn z

/-- In physical position coordinates, the lifted window constraints generate
exactly the ordinal sum of the fresh chain and the original packing order. -/
theorem ordinalSum (p : Seed) (j t h : Nat) (copies : 0 < j) (width : 0 < t)
    (x y : Lifted p j t h) : Reaches (LiftEdge p j t h) x y ↔ Ordinal p x y := by
  refine ⟨sound,?_⟩
  cases x with
  | inl x =>
    cases y with
    | inl y => exact chain copies width x y
    | inr y => exact fun _ => chainBelow copies width x y
  | inr x =>
    cases y with
    | inl y => exact False.elim
    | inr y => exact oldPath

end PackingLift

namespace PackingLift

private theorem ranking_ext {α n le} {x y : Ranking α n le} (eq : ∀ a, x.rank a = y.rank a) :
    x = y := by
  cases x; cases y
  congr
  exact funext eq

private def extendRanking {p j t h} (hj : 0 < j) (ht : 0 < t) (r : OldRanking p j) :
    LiftRanking p j t h where
  rank := insertChain _ r.rank
  injective x y hxy := by
    have e := congrArg Fin.val hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Fin.ext e)
      | inr y => have := x.isLt; simp [insertChain] at e; omega
    | inr x =>
      cases y with
      | inl y => have := y.isLt; simp [insertChain] at e; omega
      | inr y =>
        simp [insertChain] at e
        exact congrArg Sum.inr (r.injective _ _ (Fin.ext e))
  onto v := by
    by_cases small : v.val < j*(t+h)+t
    · exact ⟨.inl ⟨v,small⟩,rfl⟩
    · let k : Fin (j*p.stride+p.overlap) := ⟨v.val-(j*(t+h)+t),by have := v.isLt; omega⟩
      obtain ⟨x,hx⟩ := r.onto k
      refine ⟨.inr x,Fin.ext ?_⟩
      change j*(t+h)+t+(r.rank x).val = v.val
      rw [hx]; dsimp [k]; omega
  respects x y hxy := by
    have o := (ordinalSum p j t h hj ht x y).mp hxy
    cases x with
    | inl a =>
      cases y with
      | inl b => exact o
      | inr b =>
        change a.val ≤ j*(t+h)+t+(r.rank b).val
        have := a.isLt; omega
    | inr a =>
      cases y with
      | inl b => exact False.elim o
      | inr b => exact Nat.add_le_add_left (r.respects a b o) _

private theorem freshRanks {p j t h} (hj : 0 < j) (ht : 0 < t) (z : LiftRanking p j t h)
    (a : Fresh j t h) : (z.rank (.inl a)).val = a.val := by
  have mono (x y : Fresh j t h) (le : x.val ≤ y.val) :
      (z.rank (.inl x)).val ≤ (z.rank (.inl y)).val :=
    z.respects _ _ (chain hj ht x y le)
  have strict (x y : Fresh j t h) (lt : x.val < y.val) :
      (z.rank (.inl x)).val < (z.rank (.inl y)).val := by
    have weak := mono x y (by omega)
    have neq : (z.rank (.inl x)).val ≠ (z.rank (.inl y)).val := by
      intro eq
      have same := z.injective _ _ (Fin.ext eq)
      cases same
      omega
    omega
  obtain ⟨k,bound⟩ := a
  induction k using Nat.strongRecOn with
  | ind k ih =>
    let a : Fresh j t h := ⟨k,bound⟩
    have low : k ≤ (z.rank (.inl a)).val := by
      cases k with
      | zero => omega
      | succ k =>
        let b : Fresh j t h := ⟨k,by omega⟩
        have eq := ih k (by omega) b.isLt
        have lt := strict b a (by exact Nat.lt_succ_self _)
        change (z.rank (.inl b)).val = k at eq
        omega
    obtain ⟨u,hu⟩ := z.onto ⟨k,by omega⟩
    have eq : (z.rank u).val = k := congrArg Fin.val hu
    change (z.rank (.inl a)).val = k
    cases u with
    | inl x =>
      by_cases earlier : x.val < k
      · have hx := ih x.val earlier x.isLt
        change (z.rank (.inl x)).val = x.val at hx
        omega
      · have := mono a x (by change k ≤ x.val; omega)
        omega
    | inr x =>
      have before := z.respects _ _ (chainBelow hj ht a x)
      change (z.rank (.inl a)).val ≤ (z.rank (.inr x)).val at before
      omega

/-- The bijection on actual packing permutations assigns the fresh chain the
initial consecutive ranks and shifts every original rank by its size. -/
theorem preservesCounts (p : Seed) (j t h : Nat) (hj : 0 < j) (ht : 0 < t) :
    PreservesCounts p j t h := by
  refine ⟨extendRanking hj ht,fun _ => rfl,?_,?_⟩
  · intro r s eq
    apply ranking_ext
    intro x
    have h := congrArg (fun z : LiftRanking p j t h => (z.rank (.inr x)).val) eq
    exact Fin.ext (Nat.add_left_cancel h)
  · intro z
    let size := j*(t+h)+t
    have large (x : Old p j) : size ≤ (z.rank (.inr x)).val := by
      apply Nat.le_of_not_gt
      intro small
      let a : Fresh j t h := ⟨(z.rank (.inr x)).val,small⟩
      have same := z.injective (.inl a) (.inr x) (Fin.ext (freshRanks hj ht z a))
      cases same
    let f (x : Old p j) : Fin (j*p.stride + p.overlap) :=
      ⟨(z.rank (.inr x)).val-size,by have := (z.rank (.inr x)).isLt; have lo := large x; dsimp [size] at *; omega⟩
    have shifted (x) : size + (f x).val = (z.rank (.inr x)).val := by
      have := large x; dsimp [f]; omega
    let r : OldRanking p j := {
      rank := f
      injective := by
        intro x y eq
        have ev := congrArg Fin.val eq
        have ranks : (z.rank (.inr x)).val = (z.rank (.inr y)).val := by
          rw [← shifted x,← shifted y,ev]
        exact Sum.inr.inj (z.injective _ _ (Fin.ext ranks))
      onto := by
        intro k
        obtain ⟨u,hu⟩ := z.onto ⟨size+k.val,by have := k.isLt; dsimp [size]; omega⟩
        have ev := congrArg Fin.val hu
        change (z.rank u).val = size+k.val at ev
        cases u with
        | inl a =>
          rw [freshRanks hj ht z a] at ev
          have := a.isLt; dsimp [size] at ev; omega
        | inr x => exact ⟨x,Fin.ext (Nat.add_left_cancel ((shifted x).trans ev))⟩
      respects := by
        intro x y old
        have le := z.respects _ _ (oldPath old)
        exact Nat.sub_le_sub_right le size }
    refine ⟨r,ranking_ext ?_⟩
    intro u
    cases u with
    | inl a => exact Fin.ext (freshRanks hj ht z a).symm
    | inr x => exact Fin.ext (shifted x)

end PackingLift
