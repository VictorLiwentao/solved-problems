module

public import SolvedProblems.GenerationThresholdModel

@[expose] public section

namespace Progress
open GenerationThreshold (Edge)

abbrev Support := Nat → Bool
abbrev Collection := Support → Prop

/-- An honest observation contributes its unique positive endpoint. -/
def positive (h : Support) (e : Edge) : Option Nat :=
  if h e.lo then (if h e.hi then none else some e.lo)
  else if h e.hi then some e.hi else none

/-- Histories store the latest observation first. -/
def history (s : Nat → Edge) : Nat → List Edge :=
  Nat.rec [] (fun n previous => s n :: previous)

def seen (h : Support) : List Edge → List Nat
  | [] => []
  | e :: s => match positive h e with
    | none => seen h s
    | some x => (seen h s).insert x

def corrupt (h : Support) : List Edge → Nat
  | [] => 0
  | e :: s => corrupt h s + (if (positive h e).isNone then 1 else 0)

def surplus (h : Support) (s : List Edge) : Int := (seen h s).length - (corrupt h s : Int)

def legal (h : Support) (s : Nat → Edge) :=
  (∀ x, h x = true → ∃ n, positive h (s n) = some x) ∧
  ∀ b : Nat, ∃ N, ∀ n ≥ N, (b : Int) ≤ surplus h (history s n)

def identifiable (C : Collection) :=
  ∃ L : List Edge → Support, ∀ h, C h → ∀ s, legal h s →
    ∃ N, ∀ n ≥ N, L (history s n) = h

def finiteHoles (h : Support) := ∃ w : List Nat, ∀ x, h x = false → x ∈ w

def disjointHoles (h g : Support) := ∀ x, h x = false → g x = true

def infiniteSupport (h : Support) := ∀ b, ∃ x > b, h x = true
def proper (h : Support) := ∃ x, h x = false

end Progress

namespace Progress
open GenerationThreshold (Edge)

/-- Finite or countably infinite lists can use repeated names. Success is
eventual semantic identification by indices of hypotheses in this list. -/
def indexedIdentifiable (H : Nat → Support) :=
  ∃ L : List Edge → Nat, ∀ i s, legal (H i) s →
    ∃ N, ∀ n ≥ N, H (L (history s n)) = H i

end Progress
