module

public import SolvedProblems.PromptBoundEffective

public section
namespace PromptBound
namespace Selector

/-- Insert a word in its canonical encoding position, discarding duplicates. -/
def insertWord {q} (w : Word q) (l : List (Word q)) : List (Word q) :=
  l.filter (fun u ↦ decide (Encodable.encode u < Encodable.encode w)) ++
    w :: l.filter (fun u ↦ decide (Encodable.encode w < Encodable.encode u))

def canonical {q} (S : List (Word q)) := S.foldr insertWord []

theorem mem_insertWord {q} (x w : Word q) (l : List (Word q)) :
    x ∈ insertWord w l ↔ x = w ∨ x ∈ l := by
  simp only [insertWord, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  by_cases h : x=w
  · simp [h]
  · have ne : Encodable.encode x ≠ Encodable.encode w := fun e ↦ h (Encodable.encode_injective e)
    rcases lt_or_gt_of_ne ne with lt|gt <;> simp_all

theorem mem_canonical {q} (x : Word q) (S : List (Word q)) :
    x ∈ canonical S ↔ x ∈ S := by
  induction S with
  | nil => rfl
  | cons w l ih => change x ∈ insertWord w (canonical l) ↔ _; rw [mem_insertWord, ih, List.mem_cons]

theorem canon_insertWord {q} (w : Word q) {l : List (Word q)} (hl : Canon l) :
    Canon (insertWord w l) := by
  unfold Canon at *
  unfold insertWord
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hl.filter _, ⟨?_,hl.filter _⟩,?_⟩
  · intro x hx; exact of_decide_eq_true (List.mem_filter.mp hx).2
  · intro x hx y hy
    have lt := of_decide_eq_true (List.mem_filter.mp hx).2
    rcases List.mem_cons.mp hy with rfl|hy
    · exact lt
    · exact lt.trans (of_decide_eq_true (List.mem_filter.mp hy).2)

theorem canon_canonical {q} (S : List (Word q)) : Canon (canonical S) := by
  induction S with
  | nil => exact .nil
  | cons w l ih => exact canon_insertWord w ih

/-- A finite list containing every word whose length is within the bound. -/
def words (q : ℕ) : ℕ → List (Word q)
  | 0 => [[]]
  | n+1 => [] :: ((List.finRange q).map (fun a ↦ (words q n).map (a :: ·))).flatten

theorem mem_words (q b : ℕ) (w : Word q) : w ∈ words q b ↔ w.length ≤ b := by
  induction b generalizing w with
  | zero => simp [words]
  | succ b ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      simp [words,List.mem_flatten,List.mem_map,ih]

variable {X : Oracle}
@[fun_prop] theorem eff_insertWord {q} :
    Effective X (fun i : Word q × List (Word q) ↦ insertWord i.1 i.2) := by
  unfold insertWord
  have l : Effective X (fun i : Word q × List (Word q) ↦
       i.2.filter fun u ↦ decide (Encodable.encode u < Encodable.encode i.1)) :=
    eff_filter (f:=Prod.snd) (g:=fun z ↦ decide (Encodable.encode z.2 < Encodable.encode z.1.1)) (by fun_prop) (by fun_prop)
  have r : Effective X (fun i : Word q × List (Word q) ↦
       i.2.filter fun u ↦ decide (Encodable.encode i.1 < Encodable.encode u)) :=
    eff_filter (f:=Prod.snd) (g:=fun z ↦ decide (Encodable.encode z.1.1 < Encodable.encode z.2)) (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop] theorem eff_canonical {q : ℕ} : Effective X (@canonical q) := by
  unfold canonical
  exact .foldList (g:= fun i ↦ insertWord i.1.2 i.2) eff_id (eff_const []) (by fun_prop)

@[fun_prop] theorem eff_words (q : ℕ) : Effective X (words q) := by
  let step (W : List (Word q)) : List (Word q) := [] :: ((List.finRange q).map (fun a ↦ W.map (a :: ·))).flatten
  have inn : Effective X (fun v : List (Word q) × Fin q ↦ v.1.map (v.2 :: ·)) :=
    eff_map (f:=Prod.fst) (g:=fun z ↦ z.1.2::z.2) (by fun_prop) (by fun_prop)
  have out : Effective X (fun W : List (Word q) ↦ (List.finRange q).map (fun a ↦ W.map (a :: ·))) :=
    eff_map (eff_const _) inn
  have eff : Effective X step := by unfold step; fun_prop
  have hrec : Effective X (fun n : ℕ ↦ Nat.rec (motive:=fun _ ↦ List (Word q)) [[]] (fun _ v ↦ step v) n) :=
    .recNat (n:=fun n ↦ n) (z:=fun _ ↦ [[]]) (g:=fun i ↦ step i.2) eff_id (eff_const _) (by fun_prop)
  convert hrec using 1
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp [words,step,ih]

end Selector
end PromptBound
