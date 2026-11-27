module

public import SolvedProblems.ResistanceModel

@[expose] public section

namespace ResistanceLifts

/-- Relabeling a finite vertex set leaves its color histogram unchanged. -/
theorem histogram_perm {V A : Type*} [Fintype V] (e : V ≃ V) (f : V → A) :
    histogram (fun w => f (e w)) = histogram f := by
  change Finset.univ.val.map (f ∘ e) = _
  rw [← Multiset.map_map]
  change (Finset.univ.map e.toEmbedding).val.map f = _
  rw [Finset.map_univ_equiv]
  rfl

/-- Independently exchange the two sheets over any chosen set of base vertices. -/
def sheetPermutation (swap : Fin 39 → Bool) : Vertex ≃ Vertex where
  toFun x := (x.1, xor x.2 (swap x.1))
  invFun x := (x.1, xor x.2 (swap x.1))
  left_inv x := by rcases x with ⟨a,e⟩; cases e <;> cases h : swap a <;> simp [h]
  right_inv x := by rcases x with ⟨a,e⟩; cases e <;> cases h : swap a <;> simp [h]

/-- Paired distances suffice for every refinement depth, even starting with
arbitrary (and possibly all distinct) base-fiber colors. -/
theorem refine_of_fiber_pairs {D A : Type} (d : Bool → Vertex → Vertex → D)
    (pairs : ∀ t a b e, ∃ flip : Bool, ∀ s : Bool,
      d t (a,e) (b,s) = d false (a,false) (b,xor s flip))
    (f : Fin 39 → A) (n : ℕ) (t : Bool) (a : Fin 39) (e : Bool) :
    refine (d t) (fun x => f x.1) n (a,e) = refine (d false) (fun x => f x.1) n (a,false) := by
  classical
  induction n generalizing t a e with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext (ih _ _ _)
    let swap (b : Fin 39) := (pairs t a b e).choose
    let perm := sheetPermutation swap
    let label (w : Vertex) := (d false (a,false) w, refine (d false) (fun x => f x.1) n w)
    change histogram (fun w : Vertex => (d t (a,e) w, refine (d t) (fun x => f x.1) n w)) = histogram label
    rw [← histogram_perm perm label]
    apply congrArg histogram
    funext ⟨b,s⟩
    change (_, _) = (d false (a,false) (b,xor s (swap b)), refine _ _ n (b,xor s (swap b)))
    exact Prod.ext ((pairs t a b e).choose_spec s) ((ih t b s).trans (ih false b _).symm)

end ResistanceLifts
