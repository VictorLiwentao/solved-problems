module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Permutation

@[expose] public section

namespace PackingFactorization

/-- The graph of a permutation, local position to zero-based rank. -/
abbrev Pattern (K : Nat) := Fin K ≃ Fin K

/-- Local physical slot of a prefix or suffix entry. Both bounds follow from
the standard inclusions of finite intervals. -/
def prefixSlot {K n : Nat} (hn : n < K) (i : Fin n) : Fin K :=
  Fin.castLE (Nat.le_of_lt hn) i

def suffixSlot {K n : Nat} (hn : n < K) (i : Fin n) : Fin K :=
  Fin.cast (Nat.sub_add_cancel (Nat.le_of_lt hn)) (Fin.natAdd (K-n) i)

/-- A legal boundary is a positive proper overlap whose physical prefix and
suffix slots have the same relative order. -/
structure Overlap {K : Nat} (p : Pattern K) where
  size : Nat
  positive : 0 < size
  proper : size < K
  agrees : ∀ i h : Fin size,
    p (prefixSlot proper i) ≤ p (prefixSlot proper h) ↔
      p (suffixSlot proper i) ≤ p (suffixSlot proper h)

/-- A cut counts ranks strictly below the frontier, including both sentinels. -/
abbrev Cut (K : Nat) := Fin (K+1)

def anchorCount {K} {p : Pattern K} (a : Overlap p) (suffix : Bool) (c : Cut K) : Nat :=
  (Finset.univ.filter (fun i : Fin a.size =>
    let slot : Fin K := if suffix then suffixSlot a.proper i
      else prefixSlot a.proper i
    (p slot).val < c.val)).card

/-- At an outward step the two cuts must contain exactly the same shared ranks.
When walking to the right the current window uses its suffix. -/
def Cross {K} {p : Pattern K} (right : Bool) (a : Overlap p) (c d : Cut K) : Prop :=
  anchorCount a right c = anchorCount a (!right) d

/-- The list records all cuts after the initial cut, in the outward direction. -/
inductive Walk {K} {p : Pattern K} (right : Bool) :
    Cut K → List (Overlap p) → List (Cut K) → Prop
  | nil (c) : Walk right c [] []
  | step {a c d w ds} : Cross right a c d → Walk right d w ds →
      Walk right c (a::w) (d::ds)

def Profile {K} {p : Pattern K} (right : Bool) (m : Overlap p) (h : Nat)
    (w : List (Overlap p)) (cs : List (Cut K)) : Prop :=
  ∃ c ds, cs = c::ds ∧ anchorCount m (!right) c = h ∧ Walk right c w ds

def TwoProfiles {K} {p : Pattern K} (right : Bool) (m : Overlap p) (h : Nat)
    (w : List (Overlap p)) := ∃ cs ds, Profile right m h w cs ∧ Profile right m h w ds ∧ cs ≠ ds

/-- The finite test compares all cut walks through at most K+1 added windows.
A discrepancy is an immediately occupiable seam gap. -/
def Marked {K} {p : Pattern K} (A : Set (Overlap p)) (right : Bool) (m : Overlap p) (h : Nat) :=
  ∃ w, (∀ a ∈ w, a ∈ A) ∧ w.length ≤ K+1 ∧ TwoProfiles right m h w

def slot {K} {p : Pattern K} (a : Overlap p) (suffix : Bool) (i : Fin a.size) : Fin K :=
  if suffix then suffixSlot a.proper i
  else prefixSlot a.proper i

def shared {K} {p : Pattern K} (a : Overlap p) (suffix : Bool) (i : Fin K) : Prop :=
  if suffix then K-a.size ≤ i.val else i.val < a.size

instance {K} {p : Pattern K} (a : Overlap p) (s : Bool) (i : Fin K) : Decidable (shared a s i) := by
  unfold shared
  split <;> infer_instance

def seamIndex {K} {p : Pattern K} (a : Overlap p) (s : Bool) (i : Fin K) (h : shared a s i) :
    Fin a.size :=
  match s, h with
  | true, h => ⟨i.val-(K-a.size), (Nat.sub_lt_iff_lt_add' h).mpr
      (Nat.lt_of_lt_of_eq i.isLt (Nat.sub_add_cancel (Nat.le_of_lt a.proper)).symm)⟩
  | false, h => ⟨i.val,h⟩

/-- Beyond the common seam, new physical slots have distinct labels for each
side, window, and slot. The shared seam slots have residue 1 modulo 3. -/
def fresh (K : Nat) (right : Bool) (n i : Nat) := 3*((n+1)*K+i) + if right then 2 else 0

def initial {K} {p : Pattern K} (right : Bool) (m : Overlap p) (i : Fin K) : Nat :=
  if h : shared m (!right) i then 3*(seamIndex m (!right) i h).val+1 else fresh K right 0 i.val

def attach {K} {p : Pattern K} (right : Bool) (a : Overlap p) (v : Fin K → Nat)
    (n : Nat) (i : Fin K) : Nat :=
  if h : shared a (!right) i then v (slot a right (seamIndex a (!right) i h))
    else fresh K right n i.val

/-- Physical slot maps for successive windows, ordered outwards from the seam. -/
def framesAux {K} {p : Pattern K} (right : Bool) (v : Fin K → Nat) (n : Nat) :
    List (Overlap p) → List (Fin K → Nat)
  | [] => [v]
  | a::w => v :: framesAux right (attach right a v n) (n+1) w

def frames {K} {p : Pattern K} (right : Bool) (m : Overlap p) (w : List (Overlap p)) :=
  framesAux right (initial right m) 1 w

/-- Each local rank names its physical position. The resulting list records the
prescribed increasing order of those positions. -/
def rankOrder {K} (p : Pattern K) (v : Fin K → Nat) : List Nat :=
  List.ofFn (fun r => v (p.symm r))

def orders {K} {p : Pattern K} (right : Bool) (m : Overlap p) (w : List (Overlap p)) :=
  (frames right m w).map (rankOrder p)

/-- A permutation of all positions which restricts to the prescribed order in
each window. Additional occurrences are permitted. -/
def Packs (ws : List (List Nat)) (xs : List Nat) :=
  xs.Nodup ∧ (∀ x, x ∈ xs ↔ ∃ w ∈ ws, x ∈ w) ∧ ∀ w ∈ ws, w.Sublist xs

/-- Finite enumeration of all permutations of the physical union that realize every window. -/
noncomputable def packings (windows : List (List Nat)) : Finset (List Nat) := by
  classical
  exact (windows.flatten.toFinset.toList.permutations.toFinset).filter (Packs windows)

/-- The two physical sides are listed outwards from their common seam. The
left-hand word in the usual reading direction is the reverse of u. -/
def Factors {K} {p : Pattern K} (m : Overlap p) (u v : List (Overlap p)) :=
  let L := orders false m u
  let R := orders true m v
  (packings (L++R)).card = (packings L).card * (packings R).card

/-- An alphabet's designated seam splits every overlap word precisely when its
two finite sets of occupiable gaps are disjoint. The actual packing counts
enumerate permutations realizing all the specified physical windows. Both words
are read outwards: the overlap word in left-to-right order is u.reverse ++ [m] ++ v. -/
theorem factorization_criterion {K} {p : Pattern K} (A : Set (Overlap p)) (m : Overlap p) :
    (∀ u v, (∀ a ∈ u, a∈A) → (∀ a ∈ v, a∈A) → Factors m u v) ↔
      ∀ h, ¬(Marked A false m h ∧ Marked A true m h) := by sorry

/-- Failure has a witness using at most K+1 added windows on either side, and
the number of global permutations is strictly greater than the product. -/
theorem short_counterexample {K} {p : Pattern K} (A : Set (Overlap p)) (m : Overlap p)
    (failure : ¬∀ u v, (∀ a ∈ u, a∈A) → (∀ a ∈ v, a∈A) → Factors m u v) :
    ∃ u v, (∀ a ∈ u, a∈A) ∧ (∀ a ∈ v, a∈A) ∧ u.length ≤ K+1 ∧ v.length ≤ K+1 ∧
      (packings (orders false m u)).card * (packings (orders true m v)).card <
        (packings (orders false m u++orders true m v)).card := by sorry

def boundedWords (A : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => [] :: A.flatMap (fun a => (boundedWords A n).map (a :: ·))

def cutWalks {K} {p : Pattern K} (r : Bool) (c : Cut K) (w : List (Overlap p)) : List (List (Cut K)) :=
  w.foldr (fun a next x => (List.finRange (K+1)).flatMap (fun d =>
    if anchorCount a r x = anchorCount a (!r) d then (next d).map (d :: ·) else []))
    (fun _ => [[]]) c

def cutProfiles {K} {p : Pattern K} (r : Bool) (m : Overlap p) (h : Nat) (w : List (Overlap p)) :=
  (List.finRange (K+1)).flatMap (fun c =>
    if anchorCount m (!r) c = h then (cutWalks r c w).map (c :: ·) else [])

def forks {K} {p : Pattern K} (r : Bool) (m : Overlap p) (h : Nat) (w : List (Overlap p)) : Bool :=
  let profiles := cutProfiles r m h w
  profiles.any (fun cs => profiles.any (fun ds => cs != ds))

def markedWord? {K} {p : Pattern K} (A : List (Overlap p)) (r : Bool) (m : Overlap p) (h : Nat) :=
  (boundedWords A (K+1)).find? (forks r m h)

def marked? {K} {p : Pattern K} (A : List (Overlap p)) (r : Bool) (m : Overlap p) (h : Nat) :=
  (markedWord? A r m h).isSome

/-- Check all m+1 seam gaps against the actual finite list of allowed overlaps. -/
def factorTest {K} {p : Pattern K} (A : List (Overlap p)) (m : Overlap p) : Bool :=
  (List.range (m.size+1)).all (fun h => !(marked? A false m h && marked? A true m h))

/-- The executable test returns true precisely when every word splits at this seam. -/
theorem factorTest_correct {K} {p : Pattern K} (A : List (Overlap p)) (m : Overlap p) :
    factorTest A m = true ↔
      ∀ u v, (∀ a ∈ u, a∈A) → (∀ a ∈ v, a∈A) → Factors m u v := by sorry

end PackingFactorization
