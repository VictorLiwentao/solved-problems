module

public import SolvedProblems.FactorPackingModel
public import SolvedProblems.FactorProfiles

@[expose] public section

namespace PackingFactorization

def bucket (g : Nat → Fin 3) (j : Fin 3) (xs : List Nat) := xs.filter (fun t => g t == j)

private theorem bucket_cons (g : Nat → Fin 3) (j x xs) :
    bucket g j (x::xs) = if g x=j then x::bucket g j xs else bucket g j xs := by
  by_cases h : g x=j <;> simp [bucket,h]

def reorder (g : Nat → Fin 3) (xs : List Nat) := bucket g 0 xs ++ bucket g 1 xs ++ bucket g 2 xs

private theorem gradeCases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  rcases (show i.val=0 ∨ i.val=1 ∨ i.val=2 by have := i.isLt; omega) with h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem reorder_perm (g : Nat → Fin 3) (xs) : (reorder g xs).Perm xs := by
  induction xs with
  | nil => simp [reorder,bucket]
  | cons x xs ih =>
    rcases gradeCases (g x) with h|h|h
    · simpa [reorder,bucket,h] using List.Perm.cons x ih
    · simp only [reorder,bucket,List.filter_cons,h] at *
      simp at *
      exact (List.perm_middle ..).trans (ih.cons x)
    · simp only [reorder,bucket,List.filter_cons,h] at *
      simp at *
      have move := List.perm_middle (l₁ := (bucket g 0 xs ++ bucket g 1 xs))
        (l₂ := bucket g 2 xs) (a := x)
      have dest : (x::((bucket g 0 xs++bucket g 1 xs)++bucket g 2 xs)).Perm (x::xs) := by
        simpa [bucket,List.append_assoc] using ih.cons x
      simpa [bucket,List.append_assoc] using move.trans dest

private theorem bucket_nil_of_lt {g : Nat → Fin 3} {j k : Fin 3} {xs : List Nat}
    (lo : ∀ y ∈ xs, k ≤ g y) (lt : j < k) : bucket g j xs = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro y hy
  have ne : g y ≠ j := ne_of_gt (lt_of_lt_of_le lt (lo y hy))
  simp [ne]

theorem ordered_reorder {g : Nat → Fin 3} {xs : List Nat} (order : xs.Pairwise (fun x y => g x ≤ g y)) :
    reorder g xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨all,tail⟩ := List.pairwise_cons.mp order
    have prev := ih tail
    rcases gradeCases (g x) with h|h|h
    · simpa [reorder,bucket_cons,h] using congrArg (x::·) prev
    · rw [h] at all
      have z := bucket_nil_of_lt (j := 0) all (by decide)
      simpa [reorder,bucket_cons,h,z] using congrArg (x::·) prev
    · rw [h] at all
      have z := bucket_nil_of_lt (j := 0) all (by decide)
      have o := bucket_nil_of_lt (j := 1) all (by decide)
      simpa [reorder,bucket_cons,h,z,o] using congrArg (x::·) prev

theorem reorder_packs {ws xs} (pack : Packs ws xs) (g : Nat → Fin 3)
    (ordered : ∀ w ∈ ws, w.Pairwise (fun x y => g x ≤ g y)) : Packs ws (reorder g xs) := by
  have perm := reorder_perm g xs
  refine ⟨perm.nodup_iff.mpr pack.1,fun x => perm.mem_iff.trans (pack.2.1 x),?_⟩
  intro w hw
  have sub := pack.2.2 w hw
  have h : (reorder g w).Sublist (reorder g xs) :=
    ((sub.filter _).append (sub.filter _)).append (sub.filter _)
  rwa [ordered_reorder (ordered w hw)] at h

noncomputable def grade (P Q : Nat → Prop) (x : Nat) : Fin 3 := by
  classical
  exact if P x ∧ Q x then 0 else if P x ∨ Q x then 1 else 2

theorem grade_zero {P Q x} : grade P Q x = 0 ↔ P x ∧ Q x := by
  classical
  by_cases h : P x <;> by_cases k : Q x <;> simp [grade,h,k]

theorem grade_one {P Q x} : grade P Q x = 1 ↔ ¬(P x ↔ Q x) := by
  classical
  by_cases h : P x <;> by_cases k : Q x <;> simp [grade,h,k]

theorem aligned_order {K} (p : Pattern K) {P Q v c d}
    (one : Aligned p P v c) (two : Aligned p Q v d) :
    (rankOrder p v).Pairwise (fun x y => grade P Q x ≤ grade P Q y) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ij
  simp only [rankOrder,List.getElem_ofFn]
  let I := (p.symm ⟨i,by simpa [rankOrder] using hi⟩)
  let J := (p.symm ⟨j,by simpa [rankOrder] using hj⟩)
  change grade P Q (v I) ≤ grade P Q (v J)
  have pg : P (v J) → P (v I) := by
    intro h; apply (one I).mpr
    have le := (one J).mp h
    simp [I,J] at le ⊢
    omega
  have qg : Q (v J) → Q (v I) := by
    intro h; apply (two I).mpr
    have le := (two J).mp h
    simp [I,J] at le ⊢
    omega
  classical
  by_cases a : P (v I) <;> by_cases b : Q (v I) <;> by_cases c : P (v J) <;>
    by_cases d : Q (v J) <;> simp_all [grade]

end PackingFactorization
