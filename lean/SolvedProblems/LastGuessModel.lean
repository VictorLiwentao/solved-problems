module

@[expose] public section

namespace LastGuess

/-- The marker represents #. A pair (m,r) represents the word 1^m 0 1^r. -/
inductive Word where
  | marker
  | column (m r : Nat)
  deriving DecidableEq

def target (n : Nat) : Word → Prop
  | .marker => True
  | .column m _ => n ≤ m

def Text (n : Nat) (e : Nat → Word) := ∀ w, target n w ↔ ∃ k, e k = w
def NoRepeats (e : Nat → Word) := ∀ i j, e i = e j → i = j

/-- The symmetric difference is covered by a finite list of words. -/
def Approx (i j : Nat) := ∃ exceptions : List Word,
  ∀ w, w ∉ exceptions → (target i w ↔ target j w)

/-- State after observation k, with an arbitrary first response. -/
def run {S : Type} (first : Word → S) (update : S → Word → S) (e : Nat → Word) : Nat → S
  | 0 => first (e 0)
  | k+1 => update (run first update e k) (e (k+1))

def Eventually (P : Nat → Prop) := ∃ N, ∀ k ≥ N, P k

end LastGuess
