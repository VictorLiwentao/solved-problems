module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Partrec
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
open MeasureTheory

namespace PromptBound

/-- The membership oracle for a subset of the natural numbers. -/
structure Oracle where
  bit : ℕ → Bool

/-- Total finite computations relative to a Boolean oracle. The instructions are ordinary
computable routines, an oracle call, composition, pairing, finite list traversals and
primitive recursion. The input and output encodings are indices so composition preserves
them at every step. A partial computation is given below by its successive finite stages. -/
inductive Effective (X : Oracle) : {α β : Type} → [Primcodable α] → [Primcodable β] → (α → β) → Prop
  | basic {α β} [Primcodable α] [Primcodable β] {f : α → β} (h : Computable f) :
      Effective X f
  | query : Effective X X.bit
  | comp {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {g : β → γ} {f : α → β} :
      Effective X g → Effective X f → Effective X (fun x => g (f x))
  | pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {g : α → β} {f : α → γ} :
      Effective X g → Effective X f → Effective X (fun x => (g x, f x))
  | mapList {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → List β} {g : α × β → γ} :
      Effective X f → Effective X g → Effective X (fun a => (f a).map fun b => g (a,b))
  | foldList {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → List β} {z : α → γ} {g : (α × β) × γ → γ} :
      Effective X f → Effective X z → Effective X g →
      Effective X (fun a => (f a).foldr (fun b c => g ((a,b),c)) (z a))
  | recNat {α β} [Primcodable α] [Primcodable β] {n : α → ℕ} {z : α → β} {g : (α × ℕ) × β → β} :
      Effective X n → Effective X z → Effective X g →
      Effective X (fun a => Nat.rec (motive := fun _ => β) (z a) (fun k v => g ((a,k),v)) (n a))

abbrev Word (q : ℕ) := List (Fin q)
abbrev Round (q : ℕ) := Word q × Word q
abbrev History (q : ℕ) := List (Round q)
abbrev Family (q : ℕ) := ℕ → Word q → Bool
abbrev Tape := ℕ → Bool

def initial {α : Type} (x : ℕ → α) (n : ℕ) := (List.range n).map x

def coinWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (coinWords n).flatMap fun u => [false :: u, true :: u]

/-- Fair-coin tape law, specified by its finite uniform marginals. -/
structure FairLaw where
  law : Measure Tape
  probability : IsProbabilityMeasure law
  uniform : ∀ (n : ℕ) (f : List Bool → Bool),
    law.real {w | f (initial w n) = true} =
      (((coinWords n).filter f).length : ℝ) / (coinWords n).length

attribute [instance] FairLaw.probability

def sample {q} (h : History q) := h.map Prod.fst

def Fresh {q} (K : Word q → Bool) (S : List (Word q)) (p y : Word q) : Prop :=
  K y = true ∧ y ∉ S ∧ p.IsPrefix y

def Legal {q} (K : Word q → Bool) : History q → Prop
  | [] => True
  | (a,p) :: h => K a = true ∧ (∃ y, Fresh K (a :: sample h) p y) ∧ Legal K h

/-- Observations need only exhaust the target. The finite histories have the latest round first. -/
def Full {q} (K : Word q → Bool) (e : ℕ → Round q) : Prop :=
  ∀ w, K w = true ↔ ∃ n, (e n).1 = w

def rounds {q} (e : ℕ → Round q) (n : ℕ) := (initial e n).reverse

def Correct {q} (K : Word q → Bool) (h : History q) (y : Word q) : Prop :=
  ∃ a p tail, h = (a,p) :: tail ∧ Fresh K (sample h) p y

/-- A finite simulation of a randomized oracle generator. Both its clock and its coin
budget equal the prefix length. Answers persist on extension of the tape segment. -/
abbrev RandomStep (q : ℕ) := History q × List Bool → Option (Word q)

def Returns {q} (A : RandomStep q) (h : History q) (w : Tape) (y : Word q) : Prop :=
  ∃ n, A (h,initial w n) = some y

def RandomGenerates {q} (C : Family q) (X : Oracle) (μ : FairLaw) : Prop :=
  ∃ A : RandomStep q, Effective X A ∧
    (∀ h u v y, u.IsPrefix v → A (h,u) = some y → A (h,v) = some y) ∧
    (∀ i h, h ≠ [] → Legal (C i) h → ∀ᵐ w ∂μ.law, ∃ y, Returns A h w y) ∧
    ∀ i e, Full (C i) e → (∀ n, Legal (C i) (rounds e n)) →
      ∀ᵐ w ∂μ.law, ∃ N, ∀ n ≥ N, ∃ y, Returns A (rounds e (n+1)) w y ∧
        Correct (C i) (rounds e (n+1)) y

abbrev DetStep (q : ℕ) := History q × ℕ → Option (Word q)

def DetGenerates {q} (C : Family q) (X : Oracle) : Prop :=
  ∃ A : DetStep q, Effective X A ∧
    (∀ h n m y, n ≤ m → A (h,n) = some y → A (h,m) = some y) ∧
    (∀ i h, h ≠ [] → Legal (C i) h → ∃ n y, A (h,n) = some y) ∧
    ∀ i e, Full (C i) e → (∀ n, Legal (C i) (rounds e n)) →
      ∃ N, ∀ n ≥ N, ∃ t y, A (rounds e (n+1),t) = some y ∧ Correct (C i) (rounds e (n+1)) y

def Possible {q} (C : Family q) (S : List (Word q)) (p : Word q) : Prop :=
  S ≠ [] ∧ ∃ i, (∀ w ∈ S, C i w = true) ∧ ∃ y, Fresh (C i) S p y

/-- A finite set is supplied as a duplicate-free list in canonical encoding order. -/
def Canon {q} (S : List (Word q)) : Prop := S.Pairwise (fun u v => Encodable.encode u < Encodable.encode v)

abbrev BoundStep (q : ℕ) := (List (Word q) × Word q) × ℕ → Option ℕ

def LengthBound {q} (C : Family q) (X : Oracle) : Prop :=
  ∃ B : BoundStep q, Effective X B ∧
    (∀ S p n m b, n ≤ m → B ((S,p),n) = some b → B ((S,p),m) = some b) ∧
    (∀ S p, Canon S → Possible C S p → ∃ t b, B ((S,p),t) = some b) ∧
    ∀ i, ∃ T : List (Word q), (∀ w ∈ T, C i w = true) ∧ ∀ S p, Canon S →
      S ≠ [] → T ⊆ S → (∀ w ∈ S, C i w = true) →
      (∃ y, Fresh (C i) S p y) → ∀ t b, B ((S,p),t) = some b →
        ∃ y, Fresh (C i) S p y ∧ y.length ≤ b

end PromptBound
