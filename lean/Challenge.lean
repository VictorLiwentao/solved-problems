module

public import Std
public import Mathlib.Data.Set.Defs

@[expose] public section

/-!
# Results from Mathematical research notes

Each namespace states the definitions and claims for one model. The source drafts,
the correspondence with the Lean declarations, and the scope of each result are
recorded in `formalization.yaml`. The parking-function certificate concerns three
integers. The runtime identity concerns a finite table with an arbitrary colouring.
-/

namespace ParkingExcedances

/-- For the three scaled evaluations printed in the size-17 draft, the integer Laguerre expression has the stated strictly negative value. -/
theorem signedCertificate :
    let value : Int := 91206609124952724258816
    let first : Int := 418628039611206843581184
    let second : Int := 14829931620320319584490240
    let delta := first ^ 2 - value * second
    delta = -1177338341095610033551509654796761547971187113984 ∧ delta < 0 := by
  sorry

end ParkingExcedances

namespace BusyBeaver

/-- The largest recorded runtime, with zero for an empty table. -/
def record (runtime : α → Nat) (table : List α) : Nat :=
  table.foldr (fun machine best => max (runtime machine) best) 0

/-- For any finite runtime table and Boolean coloring, the larger of the two color-class maxima equals the maximum of the whole table. -/
theorem record_split (machines : List α) (time : α → Nat) (colour : α → Bool) :
    max (BusyBeaver.record time (machines.filter colour))
        (BusyBeaver.record time (machines.filter (fun m => !(colour m)))) =
      BusyBeaver.record time machines := by
  sorry

end BusyBeaver

namespace SoundCoverage

/-- Code the countable universe by natural numbers. A language is its membership predicate. -/
abbrev Language := Set Nat
/-- A countably indexed sequence of target or ambient languages. -/
abbrev Family := Nat → Language
/-- A learner assigns a language of possible outputs to each finite observation history. -/
abbrev Learner := List Nat → Language

/-- Every member of the first language belongs to the second. -/
def Sub (A B : Language) := ∀ x, x ∈ A → x ∈ B
/-- Every observation in the finite history belongs to the given language. -/
def Inside (s : List Nat) (A : Language) := ∀ x ∈ s, A x

/-- A full positive text, allowing repetitions. -/
def Enumerates (e : Nat → Nat) (A : Language) := ∀ x, A x ↔ ∃ k, e k = x

/-- The first `n` observations in their order of arrival. -/
def history (e : Nat → Nat) (n : Nat) := (List.range n).map e

/-- The learner's output includes every target word still absent from the history. -/
def Covers (L : Learner) (A : Language) (s : List Nat) :=
  ∀ x, A x → x ∉ s → L s x

/-- One learner eventually covers every unseen target word and outputs only words in the corresponding ambient language on every full text. -/
def Learnable (H F : Family) :=
  ∃ L : Learner, ∀ i e, Enumerates e (H i) →
    ∃ N, ∀ n ≥ N, Covers L (H i) (history e n) ∧ Sub (L (history e n)) (F i)

/-- Each target has a finite positive sample such that any subtarget in the family containing the sample has an ambient language containing the entire original target. -/
def HasWitnesses (H F : Family) :=
  ∀ i, ∃ t : List Nat, Inside t (H i) ∧
    ∀ j, Inside t (H j) → Sub (H j) (H i) → Sub (H i) (F j)

/-- For nonempty targets contained in their ambient languages, eventual sound coverage on all full texts is equivalent to the finite witness condition. -/
theorem finiteWitnessCriterion (H F : Family)
    (nonempty : ∀ i, ∃ x, H i x) (ambient : ∀ i, Sub (H i) (F i)) :
    Learnable H F ↔ HasWitnesses H F := by
  sorry

end SoundCoverage

namespace LastGuess

/-- The marker represents #. A pair (m,r) represents the word 1^m 0 1^r. -/
inductive Word where
  | marker
  | column (m r : Nat)
  deriving DecidableEq

/-- Target `n` contains the marker and every word in columns numbered at least `n`. -/
def target (n : Nat) : Word → Prop
  | .marker => True
  | .column m _ => n ≤ m

/-- The range of the infinite text is precisely target `n`. -/
def Text (n : Nat) (e : Nat → Word) := ∀ w, target n w ↔ ∃ k, e k = w
/-- Distinct positions of the text contain distinct words. -/
def NoRepeats (e : Nat → Word) := ∀ i j, e i = e j → i = j

/-- The symmetric difference is covered by a finite list of words. -/
def Approx (i j : Nat) := ∃ exceptions : List Word,
  ∀ w, w ∉ exceptions → (target i w ↔ target j w)

/-- State after observation k, with an arbitrary first response. -/
def run {S : Type} (first : Word → S) (update : S → Word → S) (e : Nat → Word) : Nat → S
  | 0 => first (e 0)
  | k+1 => update (run first update e k) (e (k+1))

/-- The predicate holds at every index beyond some finite stage. -/
def Eventually (P : Nat → Prop) := ∃ N, ∀ k ≥ N, P k

/-- Every last-guess-only learner fails even up to finite error on some repetition-free text. One extra Boolean bit permits eventual exact identification on every text. -/
theorem oneBitSeparation :
    (∀ (first : Word → Nat) (update : Nat → Word → Nat),
      ∃ n e, Text n e ∧ NoRepeats e ∧
        ¬ Eventually (fun k => Approx (run first update e k) n)) ∧
    (∃ (first : Word → Nat × Bool) (update : Nat × Bool → Word → Nat × Bool),
      ∀ n e, Text n e → Eventually (fun k => (run first update e k).1 = n)) := by
  sorry


/-- The single word in column n with suffix length zero distinguishes every
strict sublanguage of target n in this family. -/
theorem singletonTelltale (n : Nat) :
    ∃ w, target n w ∧ ∀ j, target j w →
      (∀ x, target j x → target n x) → j = n := by
  sorry

end LastGuess

namespace GenerationThreshold

/-- Keep one representative of each datum. Its position in this list is immaterial. -/
def distinct [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then distinct xs else x :: distinct xs

/-- A language on the countable universe of natural numbers, represented by its membership predicate. -/
abbrev Language := Nat → Prop
/-- A collection of languages on the same universe. -/
abbrev Class := Language → Prop

/-- Smaller endpoint first, so an unordered observation has just one encoding. -/
structure Edge where
  lo : Nat
  hi : Nat
  ordered : lo < hi
  deriving DecidableEq

/-- Exactly one endpoint of the observed edge belongs to the language. -/
def crosses (H : Language) (e : Edge) := ¬ (H e.lo ↔ H e.hi)
/-- The proposed word differs from both endpoints of every observed edge. -/
def fresh (s : List Edge) (x : Nat) := ∀ e ∈ s, x ≠ e.lo ∧ x ≠ e.hi

/-- The number of edge occurrences whose endpoints have the same membership in the language. -/
noncomputable def violations (H : Language) (s : List Edge) : Nat := by
  classical exact (s.filter (fun e => decide (¬ crosses H e))).length

/-- After at least `t` distinct edges, the generator returns a fresh target word whenever at most `k` observations violate the target. -/
def works (G : List Edge → Nat) (H : Language) (k t : Nat) :=
  ∀ s, t ≤ (distinct s).length → violations H s ≤ k → fresh s (G s) ∧ H (G s)

/-- One generator works for every target with the same corruption budget and threshold. -/
def uniform (C : Class) (k t : Nat) := ∃ G, ∀ H, C H → works G H k t

/-- At least one target fits the budget, but the targets fitting it have no common fresh word. -/
def obstruction (C : Class) (k : Nat) (E : List Edge) :=
  (∃ H, C H ∧ violations H E ≤ k) ∧
  ¬ ∃ x, fresh E x ∧ ∀ H, C H → violations H E ≤ k → H x

/-- Lists model finite samples and finite transversals. -/
def hits (answers sample : List Nat) (H : Language) :=
  ∃ x ∈ answers, x ∉ sample ∧ H x

/-- A generator offers at most `k` guesses and hits every consistent target after `t` distinct positive examples. -/
def listUniform (C : Class) (k t : Nat) :=
  ∃ G : List Nat → List Nat, ∀ s, (G s).length ≤ k ∧
    ∀ H, C H → (∀ x ∈ s, H x) → t ≤ (distinct s).length → hits (G s) s H

/-- The sample is the intersection of a nonempty subfamily whose residual languages admit no common hitting list of length at most `k`. -/
def listObstruction (C : Class) (k : Nat) (I : List Nat) :=
  ∃ F : Class, (∃ H, F H) ∧ (∀ H, F H → C H) ∧
    (∀ x, x ∈ I ↔ ∀ H, F H → H x) ∧
    ¬ ∃ a : List Nat, a.length ≤ k ∧ ∀ H, F H → hits a I H

end GenerationThreshold

namespace GenerationThreshold

/-- B₀,B₁,B₂,N are the four residue classes modulo four. -/
def threeSupport (i : Fin 3) (x : Nat) := x % 4 < 3 ∧ x % 4 ≠ i.val

/-- A threshold works uniformly exactly when every repetition-free obstruction has fewer distinct edges than the threshold. -/
theorem uniformCriterion (C : Class) (k t : Nat) :
    uniform C k t ↔ ∀ E, E.Nodup → obstruction C k E → E.length < t := by sorry

/-- A repetition-free edge list has at most `k` violations exactly when deleting at most `k` edges leaves only crossing edges. -/
theorem deletionCriterion (H : Language) (E : List Edge) (k : Nat) (simpleE : E.Nodup) :
    violations H E ≤ k ↔ ∃ D : List Edge, D.Sublist E ∧ D.length ≤ k ∧
      ∀ e ∈ E, e ∉ D → crosses H e := by sorry

/-- One generator with target-dependent thresholds exists exactly for increasing countable unions of uniformly generatable subclasses at the given corruption budget. -/
theorem nonuniformCriterion (C : Class) (k : Nat) :
    (∃ G, ∀ H, C H → ∃ t, works G H k t) ↔
    ∃ A : Nat → Class, (∀ i j, i ≤ j → ∀ H, A i H → A j H) ∧
      (∀ H, C H ↔ ∃ i, A i H) ∧ ∀ i, ∃ t, uniform (A i) k t := by sorry

/-- A single generator returns a fresh word for each of the three supports on any prefix with a violation rate strictly below one third for that support. -/
theorem unknownBudget : ∃ G : List Edge → Nat, ∀ s i,
    3 * violations (threeSupport i) s < s.length → fresh s (G s) ∧ threeSupport i (G s) := by sorry

/-- For each positive answer-list size, the admissible thresholds are exactly those exceeding the size of every repetition-free list obstruction. -/
theorem listThresholdCriterion (C : Class) (k t : Nat) (positive : 0 < k) :
    listUniform C k t ↔ ∀ I, I.Nodup → listObstruction C k I → I.length < t := by sorry

end GenerationThreshold

namespace TwoGuess

/-- Vertices are grouped by block. Extra vertex labels outside the first n
have private words only, so need no special encoding as a dependent type. -/
abbrev Vertex := Nat × Nat
/-- A word either belongs privately to a vertex at a given height or encodes an edge with a numbered copy inside a finite block. -/
inductive Word where
  | privateWord (v : Vertex) (height : Nat)
  | edgeWord (block left right serial : Nat)
  deriving DecidableEq

/-- Private words belong to their owner. A valid numbered edge word belongs to its two endpoints. -/
def belongs (v : Vertex) : Word → Prop
  | .privateWord u _ => u = v
  | .edgeWord n a b r => a < b ∧ b < n ∧ r < n ∧ (v = (n,a) ∨ v = (n,b))

/-- Two guesses suffice from the first positive example, while every finite coloring has a color class containing distinct targets with arbitrarily large finite intersections. -/
theorem twoGuessSeparation :
    (∃ G : List Word → List Word, ∀ s, (G s).length ≤ 2 ∧
      ∀ v, s ≠ [] → (∀ x ∈ s, belongs v x) →
        ∃ x ∈ G s, x ∉ s ∧ belongs v x) ∧
    (∀ q (colour : Vertex → Fin q), ∃ c, ∀ t, ∃ u v : Vertex,
      u ≠ v ∧ colour u = c ∧ colour v = c ∧ ∃ s : List Word,
        s.Nodup ∧ t ≤ s.length ∧ ∀ x, x ∈ s ↔ belongs u x ∧ belongs v x) := by sorry

end TwoGuess

namespace PromptGeneration
open SoundCoverage

variable {Y : Type}
/-- A round records the observed word, its label, and the label requested from the generator. -/
structure Round (Y : Type) where
  word : Nat
  label : Y
  request : Y

/-- The observations through round `n`, including the observation at that round. -/
def trace {α} (e : Nat → α) (n : Nat) := (List.range (n+1)).map e

/-- On every full enumeration of a target, one generator eventually returns a fresh target word at every round. -/
def ordinary (B : Language → Prop) := ∃ G : List Nat → Nat,
  ∀ A, B A → ∀ e, Enumerates e A → ∃ N, ∀ n ≥ N,
    A (G (trace e n)) ∧ G (trace e n) ∉ trace e n

/-- The set of words to which the labeling function assigns the requested label. -/
def fiber (h : Nat → Y) (y : Y) (x : Nat) := h x = y

/-- For every correctly labeled stream covering a requested label's fiber, the generator eventually answers each request for that label with an unseen word in the fiber. -/
def prompted (C : (Nat → Y) → Prop) := ∃ G : List (Round Y) → Y → Nat,
  ∀ h, C h → ∀ e : Nat → Round Y, (∀ i, (e i).label = h (e i).word) →
    ∀ y, (∀ x, h x = y → ∃ i, (e i).word = x) → ∃ N, ∀ n ≥ N,
      (e n).request = y →
      let w := G (trace e n) y
      h w = y ∧ ∀ i ≤ n, (e i).word ≠ w

/-- The language contains a natural number above every finite bound. -/
def unbounded (A : Language) := ∀ b, ∃ x, b < x ∧ A x

/-- For a class whose label fibers are all inhabited, prompted generation is equivalent to ordinary generation of each label's class of fibers. -/
theorem fiberReduction {Y : Type} (C : (Nat → Y) → Prop)
    (inhabitedFiber : ∀ h, C h → ∀ y, ∃ x, h x = y) :
    prompted C ↔ ∀ y, ordinary (fun A => ∃ h, C h ∧ A = fiber h y) := by sorry

/-- A countably indexed family with every label fiber infinite admits a prompted generator. -/
theorem countablePrompts {Y : Type} (H : Nat → Nat → Y)
    (inf : ∀ i y, unbounded (fiber (H i) y)) :
    prompted (fun h => ∃ i, h = H i) := by sorry

end PromptGeneration

namespace TapeInclusion
/-- A finite word on the binary alphabet. -/
abbrev Word := List Bool

/-- The concatenation of `n` copies of the given word. -/
def copies (u : Word) : Nat → Word :=
  Nat.rec [] (fun _ previous => u ++ previous)

/-- Every representation as a power of a word uses at most one copy. -/
def primitive (u : Word) := ∀ v k, copies v k = u → k ≤ 1

/-- Two outward-facing stars with their initial, intervening and terminal walls. -/
structure Half where
  start : Word
  first : Word
  middle : Word
  second : Word
  finish : Word

/-- The word is obtained by independently repeating each of the two designated repeaters any nonnegative number of times between the fixed walls. -/
def accepts (h : Half) (w : Word) := ∃ i j,
  w = h.start ++ copies h.first i ++ h.middle ++ copies h.second j ++ h.finish

/-- The first symbol of each nonempty wall after a repeater differs from the first symbol of that repeater. -/
def aligned (h : Half) := (h.middle = [] ∨ h.first.head? ≠ h.middle.head?) ∧
  (h.finish = [] ∨ h.second.head? ≠ h.finish.head?)

/-- The binary language pattern `(001)*(011)*`, with all three walls empty. -/
def target : Half := ⟨[],[false,false,true],[],[false,true,true],[]⟩
/-- The binary language pattern `0(010)*11(011)*`, with empty terminal wall. -/
def source : Half := ⟨[false],[false,true,false],[true,true],[false,true,true],[]⟩

/-- These aligned patterns with primitive, noncommuting repeaters of length three have distinct first repeaters, yet the source language is strictly contained in the target. -/
theorem emptyWallCounterexample :
    aligned source ∧ aligned target ∧
    (∀ h ∈ [source,target], primitive h.first ∧ primitive h.second ∧
      h.first.length = 3 ∧ h.second.length = 3 ∧
      h.first ++ h.second ≠ h.second ++ h.first) ∧
    (∀ w, accepts source w → accepts target w) ∧
    (∃ w, accepts target w ∧ ¬ accepts source w) ∧ source.first ≠ target.first := by sorry

end TapeInclusion

namespace PromiseMass

/-- The coordinatewise ternary addition relation in the k-fold strict template. -/
inductive Adds : List Bool → List Bool → List Bool → Prop
  | nil : Adds [] [] []
  | cons {a b c : Bool} {xs ys zs} :
      a.toNat + b.toNat = c.toNat → Adds xs ys zs → Adds (a::xs) (b::ys) (c::zs)

/-- On Boolean vectors of length `k`, the operation takes values from zero to `m`, preserves the two endpoints and preserves coordinatewise addition when it is defined. -/
def poly (k m : Nat) (f : List Bool → Nat) :=
  f (List.replicate k false) = 0 ∧ f (List.replicate k true) = m ∧
  (∀ xs, xs.length = k → f xs ≤ m) ∧
  ∀ xs ys zs, xs.length = k → Adds xs ys zs → f xs + f ys = f zs

/-- Invariance under the cyclic group, expressed as rotation at any cut. -/
def cyclic (k : Nat) (f : List Bool → Nat) :=
  ∀ u v : List Bool, u.length + v.length = k → f (u ++ v) = f (v ++ u)

/-- On Boolean vectors of length `k`, the value is invariant under all permutations of the coordinates. -/
def symmetric (k : Nat) (f : List Bool → Nat) :=
  ∀ u v : List Bool, u.length = k → u.Perm v → f u = f v

/-- Cyclic and fully symmetric endpoint-preserving addition polymorphisms of arity `k` each exist exactly when `k` divides `m`. -/
theorem cyclicSpectrum (k m : Nat) :
    ((∃ f, poly k m f ∧ cyclic k f) ↔ k ∣ m) ∧
    ((∃ f, poly k m f ∧ symmetric k f) ↔ k ∣ m) := by sorry

end PromiseMass

namespace Displacement

/-- The increasing enumeration of an infinite language on a naturally indexed universe. -/
structure Language where
  word : Nat → Nat
  ordered : ∀ {a b}, a < b → word a < word b

/-- The range of the increasing enumeration of a language. -/
def Language.Has (K : Language) (x : Nat) := ∃ r, K.word r = x

/-- The two languages contain exactly the same words. -/
def Same (J K : Language) := ∀ x, J.Has x ↔ K.Has x
/-- Every word of the first language belongs to the second. -/
def Sub (J K : Language) := ∀ x, J.Has x → K.Has x
/-- Every word in the finite sample belongs to the language. -/
def Inside (s : List Nat) (K : Language) := ∀ x ∈ s, K.Has x

/-- The first `t` observations of the text, in arrival order. -/
def history (e : Nat → Nat) (t : Nat) := (List.range t).map e

/-- D(t) = floor(M t) in the paper. Ranks start at zero, rounds at one. -/
def Text (D : Nat → Nat) (K : Language) (e : Nat → Nat) :=
  (∀ a b, e a = e b → a = b) ∧
  (∀ x, K.Has x ↔ ∃ k, e k = x) ∧
  ∃ b, ∀ k ≥ b, e k < K.word (D (k+1))

/-- A learner eventually outputs an index naming the target on every full text satisfying the rank deadlines. -/
def Identifiable (L : Nat → Language) (D : Nat → Nat) :=
  ∃ G : List Nat → Nat, ∀ j e, Text D (L j) e →
    ∃ N, ∀ n ≥ N, Same (L (G (history e n))) (L j)

/-- The intersection with K's first D(t) words contains at least t distinct elements. -/
def Fits (J K : Language) (D : Nat → Nat) (b : Nat) :=
  ∀ t ≥ b, ∃ w : List Nat, w.Nodup ∧ w.length = t ∧ Inside w J ∧
    ∀ x ∈ w, K.Has x ∧ x < K.word (D t)

/-- For each target and starting round, a finite positive sample excludes every proper sublanguage in the family that fits all subsequent deadlines. -/
def Witnesses (L : Nat → Language) (D : Nat → Nat) :=
  ∀ i b, 1 ≤ b → ∃ T : List Nat, Inside T (L i) ∧
    ∀ j, Inside T (L j) → Sub (L j) (L i) → Fits (L j) (L i) D b → Same (L j) (L i)

/-- For nondecreasing deadlines with `t ≤ D t`, eventual identification is equivalent to the finite witness condition. -/
theorem finiteWitnessCriterion (L : Nat → Language) (D : Nat → Nat)
    (nondecreasing : ∀ i j, i ≤ j → D i ≤ D j) (atLeast : ∀ t, t ≤ D t) :
    Identifiable L D ↔ Witnesses L D := by sorry

end Displacement

namespace Progress
open GenerationThreshold (Edge)

/-- A support on the natural numbers represented by its Boolean membership function. -/
abbrev Support := Nat → Bool
/-- A class of supports on the same countable universe. -/
abbrev Collection := Support → Prop

/-- An honest observation contributes its unique positive endpoint. -/
def positive (h : Support) (e : Edge) : Option Nat :=
  if h e.lo then (if h e.hi then none else some e.lo)
  else if h e.hi then some e.hi else none

/-- Histories store the latest observation first. -/
def history (s : Nat → Edge) : Nat → List Edge :=
  Nat.rec [] (fun n previous => s n :: previous)

/-- The list of distinct positive endpoints contributed by honest observations in the history. -/
def seen (h : Support) : List Edge → List Nat
  | [] => []
  | e :: s => match positive h e with
    | none => seen h s
    | some x => (seen h s).insert x

/-- The number of observations having either zero or two positive endpoints, counting repetitions. -/
def corrupt (h : Support) : List Edge → Nat
  | [] => 0
  | e :: s => corrupt h s + (if (positive h e).isNone then 1 else 0)

/-- The number of distinct honest positive endpoints minus the total number of corrupt observations. -/
def surplus (h : Support) (s : List Edge) : Int := (seen h s).length - (corrupt h s : Int)

/-- Each target word appears as an honest positive and the progress surplus tends to positive infinity. -/
def legal (h : Support) (s : Nat → Edge) :=
  (∀ x, h x = true → ∃ n, positive h (s n) = some x) ∧
  ∀ b : Nat, ∃ N, ∀ n ≥ N, (b : Int) ≤ surplus h (history s n)

/-- A learner eventually outputs the exact target support on every legal stream from the collection. -/
def identifiable (C : Collection) :=
  ∃ L : List Edge → Support, ∀ h, C h → ∀ s, legal h s →
    ∃ N, ∀ n ≥ N, L (history s n) = h

/-- The complement of the support is contained in a finite list. -/
def finiteHoles (h : Support) := ∃ w : List Nat, ∀ x, h x = false → x ∈ w

/-- The complements of the two supports are disjoint. -/
def disjointHoles (h g : Support) := ∀ x, h x = false → g x = true

/-- The support contains arbitrarily large natural numbers. -/
def infiniteSupport (h : Support) := ∀ b, ∃ x > b, h x = true
/-- Some natural number lies outside the support. -/
def proper (h : Support) := ∃ x, h x = false

end Progress

namespace Progress
open GenerationThreshold (Edge)

/-- Finite or countably infinite lists can use repeated names. Success is
eventual semantic identification by indices of hypotheses in this list. -/
def indexedIdentifiable (H : Nat → Support) :=
  ∃ L : List Edge → Nat, ∀ i s, legal (H i) s →
    ∃ N, ∀ n ≥ N, H (L (history s n)) = H i

/-- For a collection of at least two infinite proper supports, identification on legal streams is equivalent to finite and pairwise disjoint complements. -/
theorem identificationCriterion (C : Collection)
    (multi : ∃ a b, C a ∧ C b ∧ a ≠ b)
    (inf : ∀ h, C h → infiniteSupport h) (prop : ∀ h, C h → proper h) :
    identifiable C ↔ (∀ h, C h → finiteHoles h) ∧
      (∀ h, C h → ∀ g, C g → h ≠ g → disjointHoles h g) := by sorry

/-- A countable family of infinite proper supports with at least two distinct members is identifiable by index exactly when each complement is finite and distinct supports have disjoint complements. -/
theorem indexedCriterion (H : Nat → Support) (multi : ∃ i j, H i ≠ H j)
    (inf : ∀ i, infiniteSupport (H i)) (prop : ∀ i, proper (H i)) :
    indexedIdentifiable H ↔ (∀ i, finiteHoles (H i)) ∧
      (∀ i j, H i ≠ H j → disjointHoles (H i) (H j)) := by sorry

end Progress

namespace PackingLift

/-- One-line, zero-based rank permutation. The stride is the window length
minus the prescribed overlap. Prefix and suffix positions have disjoint indices. -/
structure Seed where
  overlap : Nat
  stride : Nat
  positive : 0 < overlap
  disjoint : overlap ≤ stride
  rank : Fin (stride + overlap) → Fin (stride + overlap)
  injective : ∀ a b, rank a = rank b → a = b
  onto : ∀ b, ∃ a, rank a = b
  admissible : ∀ a b : Fin overlap,
    ((rank ⟨a, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_left _ _)⟩).val ≤ (rank ⟨b, Nat.lt_of_lt_of_le b.isLt (Nat.le_add_left _ _)⟩).val ↔
     (rank ⟨stride+a, Nat.add_lt_add_left a.isLt _⟩).val ≤ (rank ⟨stride+b, Nat.add_lt_add_left b.isLt _⟩).val)
  minimumInPrefix : ∃ a : Fin overlap, (rank ⟨a, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_left _ _)⟩).val = 0

/-- Reflexive transitive closure of the window rank comparisons. -/
inductive Reaches {α : Type} (edge : α → α → Prop) : α → α → Prop
  | refl (x) : Reaches edge x x
  | snoc {x y z} : Reaches edge x y → edge y z → Reaches edge x z

/-- A local position in a single copy of the seed window. -/
abbrev Slot (p : Seed) := Fin (p.stride + p.overlap)
/-- A global position among the original overlapping windows. -/
abbrev Old (p : Seed) (j : Nat) := Fin (j*p.stride + p.overlap)

/-- A slot in window number i lies below the final endpoint of j windows. -/
theorem windowBound {i j stride tail slot : Nat} (hi : i < j) (hs : slot < stride + tail) :
    i * stride + slot < j * stride + tail := by
  have h := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h
  have hslot := Nat.add_lt_add_left hs (i * stride)
  rw [← Nat.add_assoc] at hslot
  exact Nat.lt_of_lt_of_le hslot (Nat.add_le_add_right h tail)

/-- The global position reached at the given slot of an original window. -/
def oldAt (p : Seed) {j} (i : Fin j) (a : Slot p) : Old p j :=
  ⟨i.val*p.stride + a.val, windowBound i.isLt a.isLt⟩

/-- The two global positions lie in a common original window in weakly increasing rank order. -/
def OldEdge (p : Seed) (j : Nat) (x y : Old p j) :=
  ∃ (i : Fin j) (a b : Slot p), x = oldAt p i a ∧ y = oldAt p i b ∧ p.rank a ≤ p.rank b

/-- The fresh physical positions are numbered from the last window back to
the first, in blocks D_j,H_j,D_{j-1},...,H_1,D_0. The total size is
j*(t+h)+t = (j+1)*t+j*h. This is only a numbering of positions. -/
abbrev Fresh (j t h : Nat) := Fin (j * (t+h) + t)
/-- The disjoint union of fresh positions and positions inherited from the original windows. -/
abbrev Lifted (p : Seed) (j t h : Nat) := Sum (Fresh j t h) (Old p j)

/-- Within a window, fresh ranks 0..t-1 are the new suffix, the next h
are the new middle, and the final t are the new prefix. The old positions
retain their one-line order within each of those three physical blocks. -/
abbrev LiftSlot (p : Seed) (t h : Nat) := Sum (Fin ((t+h)+t)) (Slot p)

/-- The global fresh index for a local fresh rank, counting the windows from last to first. -/
def newAt {j t h} (i : Fin j) (a : Fin ((t+h)+t)) : Fresh j t h :=
  ⟨(j-1-i.val)*(t+h) + a.val, by
    exact windowBound (Nat.sub_lt_of_lt (Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) Nat.zero_lt_one)) a.isLt⟩

/-- The global position represented by a local slot of a lifted window. -/
def liftAt (p : Seed) {j t h} (i : Fin j) : LiftSlot p t h → Lifted p j t h
  | .inl a => .inl (newAt i a)
  | .inr a => .inr (oldAt p i a)

/-- The local rank in a lifted window, placing all fresh ranks below all original ranks. -/
def liftRank (p : Seed) {t h} : LiftSlot p t h → Nat
  | .inl a => a.val
  | .inr a => ((t+h)+t) + (p.rank a).val

/-- The two global positions lie in a common lifted window in weakly increasing rank order. -/
def LiftEdge (p : Seed) (j t h : Nat) (x y : Lifted p j t h) :=
  ∃ (i : Fin j) (a b : LiftSlot p t h),
    x = liftAt p i a ∧ y = liftAt p i b ∧ liftRank p a ≤ liftRank p b

/-- The ordinal sum of the chain on all fresh positions and the original packing poset. -/
def Ordinal (p : Seed) {j t h} : Lifted p j t h → Lifted p j t h → Prop
  | .inl a, .inl b => a.val ≤ b.val
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr a, .inr b => Reaches (OldEdge p j) a b

end PackingLift

namespace PackingLift

/-- A packing as actual permutation ranks: each integer below n occurs
precisely once, and the rank assignment extends the window constraints. -/
structure Ranking (α : Type) (n : Nat) (le : α → α → Prop) where
  rank : α → Fin n
  injective : ∀ x y, rank x = rank y → x = y
  onto : ∀ r, ∃ x, rank x = r
  respects : ∀ x y, le x y → rank x ≤ rank y

/-- Splice the s smallest ranks in front of an existing ranking. -/
def insertChain {α : Type} {n : Nat} (s : Nat) (f : α → Fin n) : Fin s ⊕ α → Fin (s+n)
  | .inl x => ⟨x.val, Nat.lt_add_right n x.isLt⟩
  | .inr x => ⟨s+(f x).val, Nat.add_lt_add_left (f x).isLt s⟩

/-- A permutation ranking of the original global positions that extends all original window comparisons. -/
abbrev OldRanking (p : Seed) (j : Nat) :=
  Ranking (Old p j) (j*p.stride+p.overlap) (Reaches (OldEdge p j))

/-- A permutation ranking of the lifted positions that extends all lifted window comparisons. -/
abbrev LiftRanking (p : Seed) (j t h : Nat) :=
  Ranking (Lifted p j t h) ((j*(t+h)+t)+(j*p.stride+p.overlap)) (Reaches (LiftEdge p j t h))

/-- An explicit bijection between the sets of rank permutations. -/
def PreservesCounts (p : Seed) (j t h : Nat) :=
  ∃ f : OldRanking p j → LiftRanking p j t h,
    (∀ r, (f r).rank = insertChain (j*(t+h)+t) r.rank) ∧
    (∀ r s, f r = f s → r = s) ∧ ∀ z, ∃ r, f r = z

/-- Left-to-right offset of a slot in the lifted one-line pattern, before
assigning any ranks. The blocks are new prefix, old prefix, new middle,
old middle, new suffix, old suffix. -/
def offset (p : Seed) {t h : Nat} : LiftSlot p t h → Nat
  | .inl a => if a.val < t then p.stride+t+h+a.val
        else if a.val < t+h then p.overlap+a.val else a.val-(t+h)
  | .inr a => if a.val < p.overlap then t+a.val
        else if a.val < p.stride then t+h+a.val else t+h+t+a.val

/-- Every lifted slot lies inside the length of its window. -/
theorem offset_bounds (p : Seed) {t h} (a : LiftSlot p t h) :
    offset p a < (p.stride+t+h)+(p.overlap+t) := by
  cases a with
  | inl a =>
    simp only [offset]
    split
    · rename_i ha
      exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le ha (Nat.le_add_left _ _)) _
    · split
      · rename_i ha
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.lt_add_right (p.stride+t) (Nat.add_lt_add_left ha p.overlap)
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.lt_add_right (p.stride+p.overlap) (Nat.sub_lt_of_lt (b := t+h) a.isLt)
  | inr a =>
    simp only [offset]
    split
    · rename_i ha
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.lt_add_right (p.stride+t+h) (Nat.add_lt_add_left ha t)
    · split
      · rename_i ha
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.lt_add_right (p.overlap+t) (Nat.add_lt_add_left ha (t+h))
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.add_lt_add_left a.isLt (t+h+t)

/-- The absolute physical position of a lifted slot when the windows overlap at the prescribed stride. -/
def position (p : Seed) {j t h} (i : Fin j) (a : LiftSlot p t h) :
    Fin (j*(p.stride+t+h)+(p.overlap+t)) :=
  ⟨i.val*(p.stride+t+h)+offset p a, windowBound i.isLt (offset_bounds p a)⟩

/-- The closure of the lifted comparisons is precisely a fresh chain below
the original packing poset, for every admissible seed and number of windows. -/
theorem ordinalSum (p : Seed) (j t h : Nat) (copies : 0 < j) (width : 0 < t)
    (x y : Lifted p j t h) : Reaches (LiftEdge p j t h) x y ↔ Ordinal p x y := by
  sorry

/-- Splicing the fresh chain gives a bijection on packing permutations. -/
theorem preservesCounts (p : Seed) (j t h : Nat) (hj : 0 < j) (ht : 0 < t) :
    PreservesCounts p j t h := by
  sorry

/-- Two lifted window slots name the same global position exactly when their absolute physical positions coincide. -/
theorem samePosition (p : Seed) {j t h} (i k : Fin j) (a b : LiftSlot p t h) :
    position p i a = position p k b ↔ liftAt p i a = liftAt p k b := by
  sorry

end PackingLift

namespace SetDriven
open GenerationThreshold

/-- A set of unordered edges, represented by its membership predicate. -/
abbrev Edges := Edge → Prop
/-- A countably indexed family of languages. -/
abbrev Family := Nat → Language
/-- A rule assigning a proposed word to each finite sequence of observed edges. -/
abbrev Generator := List Edge → Nat

/-- The first `n` edges of a presentation, in arrival order. -/
def obs (e : Nat → Edge) (n : Nat) := (List.range n).map e
/-- The set of edges occurring at least once in the finite sequence. -/
def content (s : List Edge) : Edges := fun x => x ∈ s
/-- The word is one of the two endpoints of the edge. -/
def touches (p : Edge) (x : Nat) := p.lo = x ∨ p.hi = x
/-- Every observed edge crosses the target, and every target word appears as an endpoint. -/
def present (H : Language) (e : Nat → Edge) :=
  (∀ k, crosses H (e k)) ∧ ∀ x, H x → ∃ k, touches (e k) x

/-- The candidate belongs to the target and has appeared in none of the observed edges. -/
def good (H : Language) (s : List Edge) (x : Nat) := H x ∧ fresh s x
/-- The generator eventually returns a fresh target word at every prefix of every full honest presentation. -/
def succeeds (H : Family) (G : Generator) :=
  ∀ j e, present (H j) e → ∃ N, ∀ n ≥ N, good (H j) (obs e n) (G (obs e n))

/-- Each target and honest covering edge set have a finite witness subset. For each history, one fresh word belongs to all targets whose witness it contains and whose covering set contains its edges. -/
def compatibleWitnesses (H : Family) :=
  ∃ W : Nat → Edges → List Edge,
    (∀ j P, (∀ p, P p → crosses (H j) p) →
      (∀ x, H j x → ∃ p, P p ∧ touches p x) → ∀ p ∈ W j P, P p) ∧
    ∀ s : List Edge, ∃ x, ∀ j (P : Edges),
      (∀ p, P p → crosses (H j) p) → (∀ y, H j y → ∃ p, P p ∧ touches p y) →
      (∀ p ∈ W j P, p ∈ s) → (∀ p ∈ s, P p) → good (H j) s x

/-- A countable family of infinite languages admits a successful generator exactly when it admits one that only uses the set of observed edges. -/
theorem setDrivenGeneration (H : Family) (inf : ∀ j b, ∃ x > b, H j x) :
    (∃ G, succeeds H G) ↔ ∃ F : Edges → Nat, succeeds H (fun s => F (content s)) := by sorry

/-- For countably indexed infinite languages, successful generation on all full honest presentations is equivalent to the finite edge-witness condition. -/
theorem witnessCriterion (H : Family) (inf : ∀ j b, ∃ x > b, H j x) :
    (∃ G, succeeds H G) ↔ compatibleWitnesses H := by sorry

end SetDriven

namespace PositiveWitness

/-- anchorPart distinguishes A or B, and whether satellites contain the part.
stripe s 0 is S or T; stripe s (j+1) is the indexed block Xⱼ or Yⱼ. -/
inductive Word
  | anchorPart (side included : Bool) (row : Nat)
  | stripe (side : Bool) (slot row : Nat)
  | neutralCore (row : Nat)
  | partner (side : Bool) (index : Nat)
  deriving DecidableEq, Repr

/-- A stripe has rank equal to the larger of its slot and row. Every other word has rank equal to its row or index. -/
def rank : Word → Nat
  | .stripe _ k r => max k r
  | .anchorPart _ _ r | .neutralCore r | .partner _ r => r

/-- The family consists of two anchor languages and two sequences of satellite languages indexed by natural numbers. -/
inductive Target
  | anchor (side : Bool)
  | satellite (side : Bool) (index : Nat)
  deriving DecidableEq, Repr

/-- Finite increasing core squares exhaust C, as do the prefixes Pₘ in the paper. -/
def member : Target → Word → Bool
  | .anchor a, .anchorPart b _ _ => a == b
  | .anchor _, .partner .. => false
  | .anchor _, _ => true
  | .satellite _ _, .anchorPart _ inc _ => inc
  | .satellite b j, .partner s i => (b == s) && decide (j ≠ i)
  | .satellite _ j, .neutralCore r => decide (r ≤ j)
  | .satellite b j, .stripe s k r =>
      decide (k ≤ j ∧ r ≤ j) ||
        (if k = 0 then b == s else (b == s) == (decide (k = j+1)))

/-- A binary relation on words used to represent observed pairs in both orientations. -/
abbrev Edges := Word → Word → Prop
/-- The symmetric edge relation generated by the finite history of word pairs. -/
def observed (s : List (Word × Word)) : Edges := fun x y =>
  (x,y) ∈ s ∨ (y,x) ∈ s
/-- The word occurs as a first endpoint in the edge relation, hence as either endpoint for a symmetric relation. -/
def seen (E : Edges) (x : Word) := ∃ y, E x y
/-- The two endpoints have different membership in the target. -/
def honest (h : Target) (e : Word × Word) := member h e.1 ≠ member h e.2
/-- Every edge in the relation has exactly one endpoint in the target. -/
def consistent (h : Target) (E : Edges) := ∀ x y, E x y → member h x ≠ member h y

/-- The symmetric relation of observed pairs through observation `n`, counting from zero. -/
def prefixEdges (e : Nat → Word × Word) (n : Nat) := observed ((List.range (n+1)).map e)
/-- One rule depending only on the observed edge set eventually outputs an unseen target word on every honest stream covering the target. -/
def generates := ∃ G : Edges → Word, ∀ h (e : Nat → Word × Word),
  (∀ i, honest h (e i)) → (∀ x, member h x → ∃ i, (e i).1 = x ∨ (e i).2 = x) →
  ∃ N, ∀ n ≥ N, member h (G (prefixEdges e n)) ∧ ¬ seen (prefixEdges e n) (G (prefixEdges e n))

/-- The target is consistent with the edge set and every word in its assigned witness has appeared. -/
def active (W : Target → List Word) (E : Edges) (h : Target) :=
  consistent h E ∧ ∀ x ∈ W h, seen E x

/-- Finite positive witnesses can be assigned so that every finite history with active targets has an unseen word common to them all. -/
def compatible := ∃ W : Target → List Word, (∀ h x, x ∈ W h → member h x) ∧
  ∀ s : List (Word × Word), (∃ h, active W (observed s) h) →
    ∃ x, ¬ seen (observed s) x ∧ ∀ h, active W (observed s) h → member h x

/-- Every target and its complement contain words of arbitrarily large rank. This family admits a set-driven generator but no compatible assignment of finite positive witnesses. -/
theorem separation :
    (∀ h n, ∃ x y, n < rank x ∧ member h x ∧ n < rank y ∧ ¬ member h y) ∧
    generates ∧ ¬ compatible := by sorry

end PositiveWitness
