module

public import SolvedProblems.RadoConverse

@[expose] public section

namespace RadoSelection
open Filter

attribute [-instance] BooleanAlgebra.toBiheytingAlgebra BooleanAlgebra.toGeneralizedBooleanAlgebra

abbrev Comparisons (A : Type u) := A × A → Bool

/-- A constraint on pairwise comparisons is eventually true if every assignment
that orders some fixed finite sample satisfies the constraint. -/
def orderFilter (A : Type u) : Filter (Comparisons A) where
  sets p := ∃ l : List A, ∀ c : Comparisons A, StrictOn (· ∈ l) (fun x y => c (x,y) = true) → p c
  univ_sets := ⟨[],fun _ _ => trivial⟩
  sets_of_superset := fun ⟨l,hl⟩ h => ⟨l,fun c hc => h (hl c hc)⟩
  inter_sets := by
    rintro p q ⟨l, hl⟩ ⟨w,hw⟩
    refine ⟨l ++ w, fun c hc => ⟨hl c ?_, hw c ?_⟩⟩
    · have inc (x : A) := @List.mem_append_left A x l w
      exact ⟨fun x hx => hc.irrefl x (inc _ hx),
        fun hx hy hz => hc.trans (inc _ hx) (inc _ hy) (inc _ hz),
        fun hx hy => hc.compare (inc _ hx) (inc _ hy)⟩
    · have inc (x : A) := @List.mem_append_right A x l w
      exact ⟨fun x hx => hc.irrefl x (inc _ hx),
        fun hx hy hz => hc.trans (inc _ hx) (inc _ hy) (inc _ hz),
        fun hx hy => hc.compare (inc _ hx) (inc _ hy)⟩

theorem firstIndex_injective {A : Type u} [∀ p : Prop, Decidable p] (l : List A)
    {x y : A} (hx : x ∈ l) (eq : l.idxOf x = l.idxOf y) : x = y := by
  let i : Fin l.length := ⟨l.idxOf x, List.idxOf_lt_length_of_mem hx⟩
  let j : Fin l.length := ⟨l.idxOf y, eq ▸ i.isLt⟩
  exact (List.getElem_idxOf i.isLt).symm.trans
    ((congrArg l.get (show i = j from Fin.ext eq)).trans (List.getElem_idxOf j.isLt))

/-- Every finite constraint has a model: compare first indices in its witnessing
finite list. The coding of a finite sample includes no global choice of lists. -/
theorem comparison_quotient_nontrivial (A : Type u) [∀ p : Prop, Decidable p] :
    Nontrivial ((orderFilter A).Germ Bool) := by
  let F := orderFilter A
  refine ⟨⟨Germ.const (l := F) false, Germ.const (l := F) true, ?_⟩⟩
  intro eq
  have ev : (fun _ : Comparisons A => false) =ᶠ[F] (fun _ => true) := Germ.coe_eq.mp eq
  obtain ⟨l,hl⟩ := ev
  let c := fun xy : A × A => decide (l.idxOf xy.1 < l.idxOf xy.2)
  apply Bool.noConfusion (hl c ?_)
  refine ⟨fun _ _ h => (lt_irrefl _) (of_decide_eq_true h), ?_, ?_⟩
  · intro x y z _ _ _ hxy hyz
    exact decide_eq_true (Nat.lt_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))
  · intro x y hx _ hn
    have e : l.idxOf x ≠ l.idxOf y := fun h => hn (firstIndex_injective l hx h)
    exact (lt_or_gt_of_ne e).imp decide_eq_true decide_eq_true

/-- A Boolean point on the comparison quotient produces an order of the whole
carrier. Each finite order axiom is enforced on its finite set of arguments. -/
theorem order_from_comparison_point (A : Type u) [∀ p : Prop, Decidable p]
    (point : @BooleanPoint ((orderFilter A).Germ Bool) (germAlgebra _)) :
    ∃ r : A → A → Prop, StrictOn (fun _ => True) r := by
  let F := orderFilter A
  let _ := germAlgebra F
  obtain ⟨f,fb,_,fi,fc⟩ := point
  let val := fun p : Comparisons A → Bool => f (Germ.ofFun (l := F) p)
  have mono (p q : Comparisons A → Bool) (h : ∀ᶠ c in F, p c = true → q c = true) :
      val p = true → val q = true := by
    intro hp
    have eq : Germ.ofFun (l := F) p ⊓ Germ.ofFun q = Germ.ofFun p := by
      apply Germ.coe_eq.mpr
      refine h.mono (fun c hc => ?_)
      change (p c && q c) = p c
      cases ep : p c with
      | false => rfl
      | true => rw [hc ep]; rfl
    have hm := fi (Germ.ofFun p) (Germ.ofFun q)
    change f (Germ.ofFun p ⊓ Germ.ofFun q) = (val p && val q) at hm
    rw [eq, show f (Germ.ofFun p) = true from hp, hp, Bool.true_and] at hm
    exact hm.symm
  let ev := fun x y (c : Comparisons A) => c (x,y)
  refine ⟨fun x y => val (ev x y) = true, ?_, ?_, ?_⟩
  · intro x _ h
    apply Bool.noConfusion ((fb.symm.trans ?_) : false = true)
    apply mono (ev x x) (fun _ => false) _ h
    exact ⟨[x],fun _ ho hx => (ho.irrefl x List.mem_cons_self hx).elim⟩
  · intro x y z _ _ _ hxy hyz
    let xy_yz := fun c => ev x y c && ev y z c
    have hh := fi (Germ.ofFun (ev x y)) (Germ.ofFun (ev y z))
    change val xy_yz = (val (ev x y) && val (ev y z)) at hh
    apply mono xy_yz (ev x z) _ (by rw [hh, hxy, hyz]; rfl)
    exact ⟨[x,y,z],fun _ ho h => ho.trans (x := x) (y := y) (z := z) (by simp) (by simp) (by simp)
      (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2⟩
  · intro x y _ _ hn
    by_cases h : val (ev x y) = true
    · exact Or.inl h
    · right
      let neg := fun c => !(ev x y c)
      have hneg := fc (Germ.ofFun (ev x y))
      change val neg = !(val (ev x y)) at hneg
      apply mono neg (ev y x) _ (by rw [hneg, Bool.eq_false_iff.mpr h]; rfl)
      refine ⟨[x,y],fun c ho hnxy => ?_⟩
      rcases ho.compare (by simp) (by simp) hn with hxy | hyx
      · change (!(c (x,y))) = true at hnxy
        simp [hxy] at hnxy
      · exact hyx

theorem order_of_boolean (A : Type u) [∀ p : Prop, Decidable p] (bpi : BooleanPrime.{u}) :
    ∃ r : A → A → Prop, StrictOn (fun _ => True) r :=
  order_from_comparison_point A (@bpi _ (germAlgebra _) (comparison_quotient_nontrivial A))

end RadoSelection
