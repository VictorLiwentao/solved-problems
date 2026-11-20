module

public import SolvedProblems.BoundedJumpModel
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace BoundedJump

/-- A letter predicate, an ordered pair of letter predicates, Boolean connectives,
and existential projection of an arbitrary Boolean track. -/
inductive Formula : Type → Type 1
  | someAt {A} (p : A → Bool) : Formula A
  | ordered {A} (p q : A → Bool) : Formula A
  | neg {A} (f : Formula A) : Formula A
  | conj {A} (f g : Formula A) : Formula A
  | track {A} (f : Formula (A × Bool)) : Formula A

def Formula.Holds : {A : Type} → Formula A → {n : Nat} → (Fin n → A) → Prop
  | _, .someAt p, _, w => ∃ i, p (w i) = true
  | _, .ordered p q, _, w => ∃ i j, i < j ∧ p (w i) = true ∧ q (w j) = true
  | _, .neg f, _, w => ¬ f.Holds w
  | _, .conj f g, _, w => f.Holds w ∧ g.Holds w
  | _, .track f, _, w => ∃ b : _ → Bool, f.Holds (fun i => (w i, b i))

def Machine.run (M : Machine A) {n} (w : Fin n → A) :=
  (List.ofFn w).foldr M.step M.start

@[simp] theorem Machine.run_zero (M : Machine A) (w : Fin 0 → A) : M.run w = M.start := by
  simp [Machine.run]

@[simp] theorem Machine.run_succ (M : Machine A) (w : Fin (n+1) → A) :
    M.run w = M.step (w 0) (M.run (fun i => w i.succ)) := by
  simp [Machine.run, List.ofFn_succ]

@[reducible] def someMachine (p : A → Bool) : Machine A :=
  ⟨Bool, inferInstance, inferInstance, false, fun a s => p a || s, id⟩

private theorem some_spec (p : A → Bool) {n} (w : Fin n → A) :
    (someMachine p).run w = true ↔ ∃ i, p (w i) = true := by
  induction n with
  | zero => simp [someMachine]
  | succ n ih => simpa [someMachine, Fin.exists_fin_succ] using
      (or_congr Iff.rfl (ih (fun i => w i.succ)))

@[reducible] def orderMachine (p q : A → Bool) : Machine A :=
  ⟨Bool × Bool, inferInstance, inferInstance, (false, false),
   fun a s => (q a || s.1, (p a && s.1) || s.2), Prod.snd⟩

private theorem order_spec (p q : A → Bool) {n} (w : Fin n → A) :
    ((orderMachine p q).run w).1 = (someMachine q).run w ∧
    (((orderMachine p q).run w).2 = true ↔ ∃ i j, i < j ∧ p (w i) = true ∧ q (w j) = true) := by
  induction n with
  | zero => simp [orderMachine, someMachine]
  | succ n ih =>
    let tail := fun i : Fin n => w i.succ
    obtain ⟨seen, pair⟩ := ih tail
    simp only [Machine.run_succ]
    change (q (w 0) || ((orderMachine p q).run tail).1) = (q (w 0) || (someMachine q).run tail) ∧ _
    constructor
    · rw [seen]
    · change ((p (w 0) && ((orderMachine p q).run tail).1) || ((orderMachine p q).run tail).2) = true ↔ _
      rw [Bool.or_eq_true, Bool.and_eq_true, seen, some_spec q tail, pair]
      constructor
      · rintro (⟨hp, j, hq⟩ | ⟨i,j,h,hp,hq⟩)
        · exact ⟨0, j.succ, Fin.succ_pos _, hp, hq⟩
        · exact ⟨i.succ, j.succ, Fin.succ_lt_succ_iff.mpr h, hp, hq⟩
      · rintro ⟨i,j,h,hp,hq⟩
        cases j using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ h).elim
        | succ j =>
          cases i using Fin.cases with
          | zero => exact Or.inl ⟨hp,j,hq⟩
          | succ i => exact Or.inr ⟨i,j,Fin.succ_lt_succ_iff.mp h,hp,hq⟩

@[reducible] def negMachine (M : Machine A) : Machine A :=
  { M with accept := fun s => !(M.accept s) }

@[reducible] def andMachine (M N : Machine A) : Machine A :=
  letI := M.finite
  letI := N.finite
  letI := M.eqState
  letI := N.eqState
  ⟨M.State × N.State, inferInstance, inferInstance, (M.start, N.start),
   fun a s => (M.step a s.1, N.step a s.2), fun s => M.accept s.1 && N.accept s.2⟩

private theorem and_run (M N : Machine A) {n} (w : Fin n → A) :
    (andMachine M N).run w = (M.run w, N.run w) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Machine.run_succ]; rw [ih]

@[reducible] def projectMachine (M : Machine (A × Bool)) : Machine A :=
  letI := M.finite
  letI := M.eqState
  ⟨M.State → Bool, inferInstance, inferInstance, fun s => decide (s = M.start),
   fun a u t => decide (∃ s, u s = true ∧ ∃ b : Bool, M.step (a,b) s = t),
   fun u => decide (∃ s, u s = true ∧ M.accept s = true)⟩

private theorem project_run (M : Machine (A × Bool)) {n} (w : Fin n → A) (t : M.State) :
    (projectMachine M).run w t = true ↔
    ∃ b : Fin n → Bool, M.run (fun i => (w i,b i)) = t := by
  let := M.eqState
  let := M.finite
  induction n generalizing t with
  | zero =>
    simp only [Machine.run_zero]
    change decide (t = M.start) = true ↔ _
    simp [eq_comm]
  | succ n ih =>
    rw [Machine.run_succ]
    change decide (∃ s, (projectMachine M).run (fun i => w i.succ) s = true ∧
      ∃ b : Bool, M.step (w 0,b) s = t) = true ↔ _
    simp only [decide_eq_true_eq, ih]
    constructor
    · rintro ⟨s, ⟨b,rfl⟩, a, h⟩
      exact ⟨Fin.cons a b, by simpa only [Machine.run_succ, Fin.cons_zero, Fin.cons_succ] using h⟩
    · rintro ⟨b,h⟩
      exact ⟨_, ⟨fun i => b i.succ,rfl⟩, b 0, by simpa only [Machine.run_succ] using h⟩

def Formula.compile : {A : Type} → Formula A → Machine A
  | _, .someAt p => someMachine p
  | _, .ordered p q => orderMachine p q
  | _, .neg f => negMachine f.compile
  | _, .conj f g => andMachine f.compile g.compile
  | _, .track f => projectMachine f.compile

theorem Formula.compile_spec {A} (f : Formula A) {n} (w : Fin n → A) :
    f.compile.accept (f.compile.run w) = true ↔ f.Holds w := by
  induction f with
  | someAt p => exact some_spec _ _
  | ordered p q => exact (order_spec _ _ _).2
  | neg f ih =>
    change (!(f.compile.accept (f.compile.run w))) = true ↔ ¬ f.Holds w
    rw [← ih w]
    cases f.compile.accept (f.compile.run w) <;> decide
  | conj f g ih jh =>
    change (f.compile.accept ((andMachine f.compile g.compile).run w).1 &&
      g.compile.accept ((andMachine f.compile g.compile).run w).2) = true ↔ _
    rw [and_run, Bool.and_eq_true]
    exact and_congr (ih w) (jh w)
  | track f ih =>
    let := f.compile.finite
    let := f.compile.eqState
    change decide (∃ s, (projectMachine f.compile).run w s = true ∧ f.compile.accept s = true) = true ↔ _
    simp only [decide_eq_true_eq, project_run, Formula.Holds]
    constructor
    · rintro ⟨s, ⟨b,rfl⟩, ha⟩
      exact ⟨b,(ih _).mp ha⟩
    · rintro ⟨b,h⟩
      exact ⟨_,⟨b,rfl⟩,(ih _).mpr h⟩

end BoundedJump
