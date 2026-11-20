module

public import SolvedProblems.BoundedJumpLogic

@[expose] public section

namespace BoundedJump
namespace Formula

abbrev Mark (A : Type) := A → Bool
abbrev lift {A B : Type} (f : A → B) : A × Bool → B := fun a => f a.1
abbrev fresh {A : Type} : Mark (A × Bool) := Prod.snd

def At {A : Type} {n} (p : Mark A) (w : Fin n → A) (i : Fin n) :=
  ∀ j, p (w j) = true ↔ j = i

theorem At.lift {A : Type} {n} {p : Mark A} {w : Fin n → A} {i : Fin n}
    (h : At p w i) (b : Fin n → Bool) : At (lift p) (fun j => (w j,b j)) i := h

def single (p : Mark A) : Formula A := (someAt p).conj (.neg (.ordered p p))

def exPos (f : Formula (A × Bool)) : Formula A := .track ((single fresh).conj f)

def allPos (f : Formula (A × Bool)) : Formula A := .neg (exPos f.neg)
def impl (f g : Formula A) : Formula A := .neg (f.conj g.neg)
def disj (f g : Formula A) : Formula A := .neg (f.neg.conj g.neg)
def verum : Formula A := .neg (.someAt (fun _ => false))
def allOf (l : List (Formula A)) : Formula A := l.foldr conj verum
def anyOf (l : List (Formula A)) : Formula A := .neg (allOf (l.map neg))
def eqAt (x y : Mark A) : Formula A := .someAt (fun a => x a && y a)
def atLetter (x : Mark A) (p : A → Bool) : Formula A := eqAt x p

@[simp] theorem impl_spec (f g : Formula A) {n} (w : Fin n → A) :
    (impl f g).Holds w ↔ (f.Holds w → g.Holds w) := by
  classical
  simp [impl, Holds]

@[simp] theorem disj_spec (f g : Formula A) {n} (w : Fin n → A) :
    (disj f g).Holds w ↔ f.Holds w ∨ g.Holds w := by
  classical
  change (¬(¬_ ∧ ¬_)) ↔ _
  tauto

@[simp] theorem allOf_spec (l : List (Formula A)) {n} (w : Fin n → A) :
    (allOf l).Holds w ↔ ∀ f ∈ l, f.Holds w := by
  induction l with
  | nil => simp [allOf, verum, Holds]
  | cons x xs ih => simp [allOf, Holds, ← ih]

@[simp] theorem anyOf_spec (l : List (Formula A)) {n} (w : Fin n → A) :
    (anyOf l).Holds w ↔ ∃ f ∈ l, f.Holds w := by
  classical
  simp [anyOf, Holds]

theorem single_spec (p : Mark A) {n} (w : Fin n → A) :
    (single p).Holds w ↔ ∃ i, At p w i := by
  change ((∃ i, p (w i) = true) ∧ ¬ ∃ i j, i < j ∧ p (w i) = true ∧ p (w j) = true) ↔ _
  constructor
  · rintro ⟨⟨i,hi⟩,hn⟩
    refine ⟨i, fun j => ⟨fun hj => ?_, fun he => he ▸ hi⟩⟩
    rcases lt_trichotomy j i with h|h|h
    · exact (hn ⟨j,i,h,hj,hi⟩).elim
    · exact h
    · exact (hn ⟨i,j,h,hi,hj⟩).elim
  · rintro ⟨i,hi⟩
    exact ⟨⟨i,(hi i).mpr rfl⟩,fun ⟨x,y,h,hx,hy⟩ => (ne_of_lt h) ((hi x).mp hx |>.trans ((hi y).mp hy).symm)⟩

abbrev tag (w : Fin n → A) (i j : Fin n) := (w j, decide (j = i))

theorem at_tag (w : Fin n → A) (i : Fin n) : At fresh (tag w i) i := by
  intro j
  simp [fresh]

@[simp] theorem exPos_spec (f : Formula (A × Bool)) {n} (w : Fin n → A) :
    (exPos f).Holds w ↔ ∃ i, f.Holds (tag w i) := by
  change (∃ b : Fin n → Bool, (single fresh).Holds (fun j => (w j,b j)) ∧ _) ↔ _
  constructor
  · rintro ⟨b, hb, hf⟩
    obtain ⟨i,hi⟩ := (single_spec _ _).mp hb
    have he : b = fun j => decide (j=i) := by
      funext j
      exact Bool.eq_iff_iff.mpr ((hi j).trans (by simp))
    subst b
    exact ⟨i,hf⟩
  · rintro ⟨i,hi⟩
    exact ⟨_,(single_spec _ _).mpr ⟨i,at_tag _ _⟩,hi⟩

@[simp] theorem allPos_spec (f : Formula (A × Bool)) {n} (w : Fin n → A) :
    (allPos f).Holds w ↔ ∀ i, f.Holds (tag w i) := by
  classical
  simp [allPos, Holds, exPos_spec]

theorem atLetter_spec {x : Mark A} (p : A → Bool) {w : Fin n → A} {i} (hx : At x w i) :
    (atLetter x p).Holds w ↔ p (w i) = true := by
  change (∃ j, (x (w j) && p (w j)) = true) ↔ _
  unfold At at hx
  simp [hx]

theorem eqAt_spec {x y : Mark A} {w : Fin n → A} {i j} (hx : At x w i) (hy : At y w j) :
    (eqAt x y).Holds w ↔ i = j := (atLetter_spec _ hx).trans (hy _)

theorem ordered_spec {x y : Mark A} {w : Fin n → A} {i j} (hx : At x w i) (hy : At y w j) :
    (ordered x y).Holds w ↔ i < j := by
  unfold At at hx hy
  simp [Holds, hx, hy]

def dist : Nat → {A : Type} → Mark A → Mark A → Formula A
  | 0, _, x, y => eqAt x y
  | k+1, _, x,y => exPos ((dist k (lift x) fresh).conj
      ((ordered fresh (lift y)).conj (.neg (exPos
        ((ordered (lift fresh) fresh).conj (ordered fresh (lift (lift y))))))))

theorem dist_spec (k : Nat) {A} {x y : Mark A} {w : Fin n → A} {i j}
    (hx : At x w i) (hy : At y w j) :
    (dist k x y).Holds w ↔ i.val + k = j.val := by
  induction k generalizing A i j with
  | zero => simpa [dist, Fin.ext_iff] using eqAt_spec hx hy
  | succ k ih =>
    simp only [dist, exPos_spec, Holds]
    have ht (t : Fin n) := at_tag w t
    have hxt (t : Fin n) := hx.lift (fun s => decide (s=t))
    have hyt (t : Fin n) := hy.lift (fun s => decide (s=t))
    change (∃ t, (dist k (lift x) fresh).Holds (tag w t) ∧ _ ∧ _) ↔ _
    simp only [ih (hxt _) (ht _)]
    constructor
    · rintro ⟨t,htv,ltj,hn⟩
      have lt' := (ordered_spec (ht t) (hyt t)).mp ltj
      by_contra he
      have less : t.val + 1 < j.val := by omega
      let z : Fin n := ⟨t.val+1,by omega⟩
      apply hn
      refine ⟨z, ?_, ?_⟩
      · exact (ordered_spec ((ht t).lift _) (at_tag _ _)).mpr (show t.val < t.val+1 by omega)
      · exact (ordered_spec (at_tag _ _) ((hyt t).lift _)).mpr less
    · intro h
      let t : Fin n := ⟨i.val+k, by omega⟩
      refine ⟨t,rfl,(ordered_spec (ht t) (hyt t)).mpr (show i.val+k < j.val by omega),?_⟩
      rintro ⟨z,hz,hz'⟩
      have hl := (ordered_spec ((ht t).lift _) (at_tag _ _)).mp hz
      have hr := (ordered_spec (at_tag _ _) ((hyt t).lift _)).mp hz'
      change i.val + k < z.val at hl
      omega

end Formula
end BoundedJump
