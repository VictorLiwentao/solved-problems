module

public import SolvedProblems.BoundedJumpPredicates
public import SolvedProblems.BoundedJumpRelations

@[expose] public section

namespace BoundedJump.Formula

def edgeF (d : A → Letter m) (x y : Mark A) : Formula A :=
  anyOf (List.ofFn fun k : Fin m =>
    disj ((atLetter x (fun a => decide (d a = some (true,k)))).conj (dist (k.val+1) x y))
         ((atLetter x (fun a => decide (d a = some (false,k)))).conj (dist (k.val+1) y x)))

theorem edgeF_spec (d : A → Letter m) {x y : Mark A} {w : Fin n → A} {i j}
    (hx : At x w i) (hy : At y w j) :
    (edgeF d x y).Holds w ↔ Edge (fun t => d (w t)) i j := by
  simp [edgeF, Holds, atLetter_spec _ hx, dist_spec _ hx hy, dist_spec _ hy hx]
  cases h : d (w i) with
  | none => simp [Edge,h]
  | some e =>
    rcases e with ⟨b,k⟩
    cases b <;> simp [Edge,h]

/-- Closure of the Boolean set marked by s under the directed edges. -/
def closedF (d : A → Letter m) (s : Mark A) : Formula A :=
  allPos (allPos (impl ((eqAt (lift fresh) (lift (lift s))).conj
    (edgeF (lift (lift d)) (lift fresh) fresh)) (eqAt fresh (lift (lift s)))))

theorem closedF_spec (d : A → Letter m) (s : Mark A) (w : Fin n → A) :
    (closedF d s).Holds w ↔
      ∀ i j, s (w i) = true → Edge (fun t => d (w t)) i j → s (w j) = true := by
  simp only [closedF, allPos_spec, impl_spec, Holds]
  apply forall_congr'; intro i
  apply forall_congr'; intro j
  let wi := tag w i
  have hi := (at_tag w i).lift (fun t => decide (t=j))
  have hj := at_tag wi j
  change ((atLetter (lift fresh) (lift (lift s))).Holds (tag wi j) ∧ _ → (atLetter fresh (lift (lift s))).Holds (tag wi j)) ↔ _
  rw [atLetter_spec _ hi, edgeF_spec _ hi hj, atLetter_spec (lift (lift s)) hj]
  exact and_imp

/-- Every successor-closed set containing x contains y. -/
def reachF (d : A → Letter m) (x y : Mark A) : Formula A :=
  .neg (.track ((eqAt (lift x) fresh).conj
    ((closedF (lift d) fresh).conj (.neg (eqAt (lift y) fresh)))))

theorem reachF_spec (d : A → Letter m) {x y : Mark A} {w : Fin n → A} {i j}
    (hx : At x w i) (hy : At y w j) :
    (reachF d x y).Holds w ↔ Reach (fun t => d (w t)) i j := by
  classical
  simp only [reachF, Holds, not_exists, closedF_spec]
  unfold Reach
  apply forall_congr'; intro b
  change (¬ ((atLetter (lift x) fresh).Holds (fun t => (w t,b t)) ∧
    _ ∧ ¬ (atLetter (lift y) fresh).Holds (fun t => (w t,b t)))) ↔ _
  rw [atLetter_spec _ (hx.lift b), atLetter_spec _ (hy.lift b)]
  simp [lift, fresh]

def strictF (d : A → Letter m) (x y : Mark A) : Formula A :=
  (reachF d x y).conj (.neg (eqAt x y))

theorem strictF_spec (d : A → Letter m) {x y : Mark A} {w : Fin n → A} {i j}
    (hx : At x w i) (hy : At y w j) :
    (strictF d x y).Holds w ↔ Strict (fun t => d (w t)) i j := by
  simp [strictF, Holds, reachF_spec _ hx hy, eqAt_spec hx hy, Strict]

def landsF (d : A → Letter m) : Formula A :=
  allPos (impl (.neg (atLetter fresh (fun a => decide (d a.1 = none))))
    (exPos (edgeF (lift (lift d)) (lift fresh) fresh)))

def antisymmF (d : A → Letter m) : Formula A :=
  allPos (allPos (impl ((reachF (lift (lift d)) (lift fresh) fresh).conj
    (reachF (lift (lift d)) fresh (lift fresh))) (eqAt (lift fresh) fresh)))

def totalF (d : A → Letter m) : Formula A :=
  allPos (allPos (disj (reachF (lift (lift d)) (lift fresh) fresh)
    (reachF (lift (lift d)) fresh (lift fresh))))

def iffF (f g : Formula A) : Formula A := (impl f g).conj (impl g f)

@[simp] theorem iffF_spec (f g : Formula A) (w : Fin n → A) :
    (iffF f g).Holds w ↔ (f.Holds w ↔ g.Holds w) := by
  simp only [iffF, Holds, impl_spec, iff_iff_implies_and_implies]

def coverF (d : A → Letter m) : Formula A :=
  allPos (allPos (iffF (edgeF (lift (lift d)) (lift fresh) fresh)
    ((strictF (lift (lift d)) (lift fresh) fresh).conj (.neg (exPos
      ((strictF (lift (lift (lift d))) (lift (lift fresh)) fresh).conj
       (strictF (lift (lift (lift d))) fresh (lift fresh))))))))

def validF (d : A → Letter m) : Formula A :=
  (landsF d).conj ((antisymmF d).conj ((totalF d).conj (coverF d)))

theorem validF_spec (d : A → Letter m) (w : Fin n → A) :
    (validF d).Holds w ↔ Valid (fun t => d (w t)) := by
  classical
  simp only [validF, landsF, antisymmF, totalF, coverF, Holds, allPos_spec, impl_spec,
    exPos_spec, disj_spec, iffF_spec, Valid]
  apply and_congr
  · apply forall_congr'; intro i
    rw [atLetter_spec _ (at_tag w i)]
    simp only [decide_eq_true_eq]
    apply imp_congr_right; intro _
    apply exists_congr; intro j
    exact edgeF_spec _ ((at_tag w i).lift _) (at_tag _ _)
  apply and_congr
  · apply forall_congr'; intro i
    apply forall_congr'; intro j
    have hi := (at_tag w i).lift (fun t => decide (t=j))
    have hj := at_tag (tag w i) j
    rw [reachF_spec _ hi hj, reachF_spec _ hj hi, eqAt_spec hi hj]
    exact and_imp
  apply and_congr
  · apply forall_congr'; intro i
    apply forall_congr'; intro j
    have hi := (at_tag w i).lift (fun t => decide (t=j))
    have hj := at_tag (tag w i) j
    rw [reachF_spec _ hi hj, reachF_spec _ hj hi]
  · apply forall_congr'; intro i
    apply forall_congr'; intro j
    have hi := (at_tag w i).lift (fun t => decide (t=j))
    have hj := at_tag (tag w i) j
    rw [edgeF_spec _ hi hj, strictF_spec _ hi hj]
    apply iff_congr Iff.rfl
    apply and_congr_right; intro _
    apply not_congr
    apply exists_congr; intro k
    have hk := at_tag (tag (tag w i) j) k
    exact and_congr (strictF_spec _ (hi.lift _) hk) (strictF_spec _ hk (hj.lift _))

end BoundedJump.Formula
