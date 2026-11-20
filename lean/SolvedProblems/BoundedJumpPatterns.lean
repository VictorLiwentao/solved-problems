module

public import SolvedProblems.BoundedJumpGraph

@[expose] public section

namespace BoundedJump.Formula

def rankF (b a : Nat) (x y : Mark A) : Formula A :=
  if b < a then ordered x y else if a < b then ordered y x else verum.neg

def priorF (d : A → Letter m) (a : Nat) (prev : List (Nat × Mark A)) (y : Mark A) : Formula A :=
  allOf (prev.map fun (b,x) => (strictF d x y).conj (rankF b a x y))

def liftMarks (prev : List (Nat × Mark A)) : List (Nat × Mark (A × Bool)) :=
  prev.map fun (b,x) => (b,lift x)

def occursF : (p : List Nat) → {A : Type} → (A → Letter m) → List (Nat × Mark A) → Formula A
  | [], _, _, _ => verum
  | a :: rest, _, d, prev => exPos ((priorF (lift d) a (liftMarks prev) fresh).conj
       (occursF rest (lift d) ((a,fresh) :: liftMarks prev)))

def avoidF (d : A → Letter m) (B : List (List Nat)) : Formula A :=
  allOf (B.map fun p => (occursF p d []).neg)

def Marks (w : Fin n → A) (l : List (Nat × Mark A)) (q : List (Nat × Fin n)) :=
  List.Forall₂ (fun u v => u.1 = v.1 ∧ At u.2 w v.2) l q

theorem Marks.lifted {w : Fin n → A} {l q} (h : Marks w l q) (i : Fin n) :
    Marks (tag w i) (liftMarks l) q := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons ⟨h.1,h.2.lift _⟩ ih

theorem rankF_spec (a b : Nat) {x y : Mark A} {w : Fin n → A} {i j}
    (hx : At x w i) (hy : At y w j) :
    (rankF b a x y).Holds w ↔
       (if b < a then i < j else if a < b then j < i else False) := by
  unfold rankF
  split
  · exact ordered_spec hx hy
  · split
    · exact ordered_spec hy hx
    · simp [verum,Holds]

theorem priorF_spec (d : A → Letter m) (a : Nat) {l q} {y : Mark A} {w : Fin n → A} {j}
    (h : Marks w l q) (hy : At y w j) :
    (priorF d a l y).Holds w ↔ ∀ u ∈ q, Strict (fun t => d (w t)) u.2 j ∧
      (if u.1 < a then u.2 < j else if a < u.1 then j < u.2 else False) := by
  induction h with
  | nil => simp [priorF]
  | @cons x z xs zs h _ ih =>
    obtain ⟨e,hx⟩ := h
    simp only [priorF, List.map_cons, allOf_spec, List.mem_cons, forall_eq_or_imp, Holds]
    apply and_congr
    · simpa [e] using and_congr (strictF_spec d hx hy) (rankF_spec a x.1 hx hy)
    · simpa only [priorF,allOf_spec] using ih

theorem occursF_spec (p : List Nat) {A} (d : A → Letter m) {l q} {w : Fin n → A}
    (h : Marks w l q) :
    (occursF p d l).Holds w ↔ OccursFrom (Strict (fun t => d (w t))) p q := by
  induction p generalizing A l q with
  | nil => simp [occursF,OccursFrom,verum,Holds]
  | cons a rest ih =>
    simp only [occursF,exPos_spec,Holds,OccursFrom]
    apply exists_congr; intro j
    have h' := h.lifted j
    exact and_congr (priorF_spec _ _ h' (at_tag _ _)) (ih _ (.cons ⟨rfl,at_tag _ _⟩ h'))

theorem avoidF_spec (d : A → Letter m) (B : List (List Nat)) (w : Fin n → A) :
    (avoidF d B).Holds w ↔ Avoid B (Strict (fun t => d (w t))) := by
  simp [avoidF,Holds,occursF_spec _ _ (List.Forall₂.nil : Marks w [] []),Avoid]

end BoundedJump.Formula
