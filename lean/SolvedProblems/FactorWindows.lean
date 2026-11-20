module

public import SolvedProblems.FactorCuts
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace PackingFactorization

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

theorem slot_shared {K} {p : Pattern K} (a : Overlap p) (s) (i : Fin a.size) :
    shared a s (slot a s i) := by
  cases s <;> simp [shared,slot,prefixSlot,suffixSlot]

theorem local_slot {K} {p : Pattern K} (a : Overlap p) (s) (i : Fin a.size) :
    seamIndex a s (slot a s i) (slot_shared a s i) = i := by
  cases s <;> simp [seamIndex,slot,prefixSlot,suffixSlot]

theorem slot_local {K} {p : Pattern K} (a : Overlap p) (s) (i : Fin K) (h : shared a s i) :
    slot a s (seamIndex a s i h) = i := by
  apply Fin.ext
  cases s with
  | false => rfl
  | true => exact Nat.add_sub_of_le (show K-a.size ≤ i.val from h)

def anchors {K} {p : Pattern K} (a : Overlap p) (s : Bool) (c : Cut K) : Finset (Fin a.size) :=
  Finset.univ.filter (fun i => (p (slot a s i)).val < c.val)

theorem members_eq {K} {p : Pattern K} (a : Overlap p) (s) {c d : Cut K}
    (eq : anchorCount a s c = anchorCount a (!s) d) : anchors a s c = anchors a (!s) d := by
  change (anchors a s c).card = (anchors a (!s) d).card at eq
  have compat (i j : Fin a.size) :
      p (slot a s i) ≤ p (slot a s j) ↔ p (slot a (!s) i) ≤ p (slot a (!s) j) := by
    cases s
    · simpa [slot] using a.agrees i j
    · simpa [slot] using (a.agrees i j).symm
  apply Finset.Subset.antisymm
  · by_contra bad
    obtain ⟨i,hi,hi'⟩ := Finset.not_subset.mp bad
    have bad' : ¬ anchors a (!s) d ⊆ anchors a s c := by
      intro sub
      exact bad ((Finset.eq_of_subset_of_card_le sub eq.le).symm.le)
    obtain ⟨j,hj,hj'⟩ := Finset.not_subset.mp bad'
    simp only [anchors,Finset.mem_filter,Finset.mem_univ,true_and] at hi hi' hj hj'
    rcases le_total (p (slot a s j)) (p (slot a s i)) with le|le
    · omega
    · have le' := (compat i j).mp le
      omega
  · by_contra bad
    obtain ⟨i,hi,hi'⟩ := Finset.not_subset.mp bad
    have bad' : ¬ anchors a s c ⊆ anchors a (!s) d := by
      intro sub
      exact bad ((Finset.eq_of_subset_of_card_le sub eq.ge).symm.le)
    obtain ⟨j,hj,hj'⟩ := Finset.not_subset.mp bad'
    simp only [anchors,Finset.mem_filter,Finset.mem_univ,true_and] at hi hi' hj hj'
    rcases le_total (p (slot a s i)) (p (slot a s j)) with le|le
    · omega
    · have le' := (compat j i).mp le
      omega

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

end PackingFactorization
