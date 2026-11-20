module

public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace OnlineCertificates

/-- A query is a natural number and its label is a bit. Histories store the most recent answer first. -/
abbrev Sample := Nat × Bool
abbrev Hist := List Sample
/-- A learner returns its prediction and the two successor memories for actual labels false and true. -/
abbrev Reply := Bool × Hist × Hist
/-- A stage-bounded simulation takes the current finite memory, next query and time bound. -/
abbrev Machine := Hist × Nat × Nat → Option Reply
/-- Unbounded convergence of a staged program at a fixed input. -/
def Answers (A : Machine) (s : Hist) (x : Nat) (r : Reply) := ∃ t, A (s,x,t) = some r
/-- Output, once available, persists as the simulation bound increases. -/
def Stable (A : Machine) := ∀ s x t u r, t ≤ u → A (s,x,t) = some r → A (s,x,u) = some r
/-- The finite history agrees with a member of the binary concept class. -/
def Realizes (H : (Nat → Bool) → Prop) (h : Hist) :=
  ∃ f, H f ∧ ∀ z ∈ h, f z.1 = z.2
/-- The learner's state and mistake count after any finite interaction. -/
inductive Run (A : Machine) : Hist → Hist → Nat → Prop
  | nil : Run A [] [] 0
  | step {h s m x b r} : Run A h s m → Answers A s x r →
      Run A ((x,b)::h) (if b then r.2.2 else r.2.1) (m + if r.1 = b then 0 else 1)
/-- A partial computable online transducer with mistake budget d. In total mode it
must also answer every query after histories inconsistent with the class. -/
def Learnable (H : (Nat → Bool) → Prop) (d : Nat) (total : Bool) :=
  ∃ A : Machine, Primrec A ∧ Stable A ∧
    (∀ h s m, Run A h s m → (total = true ∨ Realizes H h) → ∀ x, ∃ r, Answers A s x r) ∧
    ∀ h s m, Run A h s m → Realizes H h → m ≤ d
/-- A finite trace contains at most one observation per queried input. -/
def Simple (s : Hist) := (s.map Prod.fst).Nodup
/-- Two representations have the same unordered signed examples. -/
def Same (s t : Hist) := ∀ p, p ∈ s ↔ p ∈ t
/-- The trace is listed up to reordering by the computable enumeration. -/
def Listed (E : Nat → Hist) (s : Hist) := ∃ n, Same (E n) s
/-- The enumerated unordered traces start at the empty trace, exclude realizable
traces at level d+1, and extend every required fresh query by at least one sign. -/
def Certificates (H : (Nat → Bool) → Prop) (d : Nat) (total : Bool) :=
  ∃ E : Nat → Hist, Primrec E ∧
    (∀ i, Simple (E i) ∧ (E i).length ≤ d+1) ∧ Listed E [] ∧
    (∀ s, Simple s → Listed E s → Realizes H s → s.length ≤ d) ∧
    ∀ s, Simple s → Listed E s → s.length ≤ d → (total = true ∨ Realizes H s) →
      ∀ x, (∀ b, (x,b) ∉ s) → ∃ b, Listed E ((x,b)::s)

end OnlineCertificates
