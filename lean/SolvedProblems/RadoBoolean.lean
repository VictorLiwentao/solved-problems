module

public import SolvedProblems.RadoFine
public import SolvedProblems.RadoOrder
public import Mathlib.Order.BooleanAlgebra.Defs

@[expose] public section

namespace RadoSelection

-- Use the Boolean algebra’s given lattice and bounds directly.
attribute [-instance] BooleanAlgebra.toBiheytingAlgebra BooleanAlgebra.toGeneralizedBooleanAlgebra

/-- A homomorphism to the two-element Boolean algebra, given on the standard
generators of the Boolean signature (join then follows by De Morgan). -/
def BooleanPoint (B : Type u) [BooleanAlgebra B] : Prop :=
  ∃ f : B → Bool, f ⊥ = false ∧ f ⊤ = true ∧
    (∀ x y, f (x ⊓ y) = (f x && f y)) ∧ ∀ x, f xᶜ = !(f x)

/-- Increasing listings of one unordered sample. Existence and uniqueness below
enable a definition of the local truth value by a formula, without making choices. -/
private def Listing {A : Type u} (r : A → A → Prop) (s : Sample A) (l : List A) : Prop :=
  (∀ x, x ∈ s ↔ x ∈ l) ∧ l.Pairwise r

private theorem insert_sorted {A : Type u} [∀ p : Prop, Decidable p] {r : A → A → Prop}
    (o : StrictOn (fun _ => True) r) (a : A) (l : List A) (hl : List.Pairwise r l)
    (ha : a ∉ l) : ∃ w : List A, (∀ x, x ∈ w ↔ x = a ∨ x ∈ l) ∧ w.Pairwise r := by
  induction l with
  | nil => exact ⟨[a],fun x => List.mem_cons, List.pairwise_singleton ..⟩
  | cons b l ih =>
    obtain ⟨hb, hl⟩ := List.pairwise_cons.mp hl
    have hn : a ≠ b := fun e => ha (List.mem_cons.mpr (Or.inl e))
    rcases o.compare trivial trivial hn with hab | hba
    · refine ⟨a :: b :: l, fun _ => List.mem_cons, List.pairwise_cons.mpr ⟨?_, ?_⟩⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxl
        · exact hab
        · exact o.trans trivial trivial trivial hab (hb _ hxl)
      · exact List.pairwise_cons.mpr ⟨hb,hl⟩
    · obtain ⟨w,hw,pw⟩ := ih hl (fun h => ha (List.mem_cons_of_mem _ h))
      refine ⟨b :: w, ?_, List.pairwise_cons.mpr ⟨?_,pw⟩⟩
      · intro x
        rw [List.mem_cons, hw, List.mem_cons, or_left_comm]
      · intro x hx
        rcases (hw x).mp hx with rfl | hxl
        · exact hba
        · exact hb _ hxl

private theorem listing_exists {A : Type u} [∀ p : Prop, Decidable p] {r : A → A → Prop}
    (o : StrictOn (fun _ => True) r) (s : Sample A) : ∃ l, Listing r s l := by
  induction s using Sample.induction with
  | empty => exact ⟨[],fun _ => Iff.rfl,.nil⟩
  | step a s ih =>
    obtain ⟨l, hl, pl⟩ := ih
    by_cases ha : a ∈ s
    · refine ⟨l, ?_, pl⟩
      intro x
      exact (or_iff_right_of_imp fun h => h ▸ ha).trans (hl x)
    · obtain ⟨w,hw,pw⟩ := insert_sorted o a l pl (fun h => ha ((hl _).mpr h))
      exact ⟨w, fun x => (or_congr Iff.rfl (hl x)).trans (hw x).symm, pw⟩

private theorem listing_unique {A : Type u} [∀ p : Prop, Decidable p] {r : A → A → Prop}
    (o : StrictOn (fun _ => True) r) {l w : List A} (hl : l.Pairwise r) (hw : w.Pairwise r)
    (same : ∀ x, x ∈ l ↔ x ∈ w) : l = w := by
  induction l generalizing w with
  | nil =>
    cases w with
    | nil => rfl
    | cons a w => exact (List.not_mem_nil ((same a).mpr List.mem_cons_self)).elim
  | cons a l ih =>
    cases w with
    | nil => exact (List.not_mem_nil ((same a).mp List.mem_cons_self)).elim
    | cons b w =>
      obtain ⟨ah, hl⟩ := List.pairwise_cons.mp hl
      obtain ⟨bh, hwTail⟩ := List.pairwise_cons.mp hw
      have eq : a = b := by
        apply Decidable.byContradiction
        intro hn
        have hab := (List.mem_cons.mp ((same a).mp List.mem_cons_self)).resolve_left hn
        have hba := (List.mem_cons.mp ((same b).mpr List.mem_cons_self)).resolve_left (Ne.symm hn)
        exact o.irrefl _ trivial (o.trans trivial trivial trivial (ah b hba) (bh a hab))
      subst b
      congr 1
      apply ih hl hwTail
      intro x
      by_cases hx : x = a
      · subst x
        exact ⟨fun h => (o.irrefl _ trivial (ah _ h)).elim,
          fun h => (o.irrefl _ trivial (bh _ h)).elim⟩
      · simpa only [List.mem_cons, hx, false_or] using same x

private theorem below_complement {B : Type u} [BooleanAlgebra B] {b x : B}
    (h : b ⊓ x = ⊥) : b ≤ xᶜ := by
  calc
    b = b ⊓ ⊤ := (inf_top_eq _).symm
    _ = b ⊓ (x ⊔ xᶜ) := congrArg (b ⊓ ·) (le_antisymm (BooleanAlgebra.top_le_sup_compl x) le_top)
    _ = (b ⊓ x) ⊔ (b ⊓ xᶜ) := inf_sup_left .. 
    _ ≤ xᶜ := sup_le (h ▸ bot_le) inf_le_right

/-- Greedily retain a nonzero cell of the generating literals along the unique
ordered listing. A zero intersection leaves the previous cell below the complement. -/
private def piece {B : Type u} [BooleanAlgebra B] [∀ p : Prop, Decidable p] : List B → B
  | [] => ⊤
  | x :: l => let b := piece l; if b ⊓ x = ⊥ then b else b ⊓ x

private theorem piece_invariants {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    [∀ p : Prop, Decidable p] (l : List B) :
    piece l ≠ ⊥ ∧ ∀ x ∈ l, piece l ≤ x ∨ piece l ≤ xᶜ := by
  induction l with
  | nil => exact ⟨top_ne_bot,fun _ h => (List.not_mem_nil h).elim⟩
  | cons a l ih =>
    change (if piece l ⊓ a = ⊥ then piece l else piece l ⊓ a) ≠ ⊥ ∧ _
    by_cases h : piece l ⊓ a = ⊥
    · simp only [piece, ite_eq_left h]
      refine ⟨ih.1, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact Or.inr (below_complement h)
      · exact ih.2 x hxl
    · simp only [piece, ite_eq_right h]
      refine ⟨h, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact Or.inl inf_le_right
      · exact (ih.2 x hxl).imp (le_trans inf_le_left) (le_trans inf_le_left)

private theorem fine_boolean {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    [∀ p : Prop, Decidable p] {U : (Sample B → Prop) → Prop} (F : Fine U)
    {r : B → B → Prop} (o : StrictOn (fun _ => True) r) : BooleanPoint B := by
  let atSample := fun (s : Sample B) (x : B) => ∃ l, Listing r s l ∧ piece l ≤ x
  have eval (s : Sample B) : ∃ b : B, b ≠ ⊥ ∧ (∀ x ∈ s, b ≤ x ∨ b ≤ xᶜ) ∧
      ∀ x, atSample s x ↔ b ≤ x := by
    obtain ⟨l,hl⟩ := listing_exists o s
    have inv := piece_invariants l
    refine ⟨piece l, inv.1, fun x hx => inv.2 x ((hl.1 x).mp hx), fun x => ⟨?_,?_⟩⟩
    · rintro ⟨w,hw,hx⟩
      have eq := listing_unique o hw.2 hl.2 (fun y => (hw.1 y).symm.trans (hl.1 y))
      exact eq ▸ hx
    · exact fun h => ⟨l,hl,h⟩
  let truth := fun x => U (atSample · x)
  have botF (s : Sample B) : ¬ atSample s ⊥ := by
    obtain ⟨b,hb,_,hs⟩ := eval s
    exact fun h => hb (le_bot_iff.mp ((hs _).mp h))
  have topT (s : Sample B) : atSample s ⊤ := by
    obtain ⟨_,_,_,hs⟩ := eval s
    exact (hs _).mpr le_top
  have meet (s : Sample B) (x y : B) :
      atSample s (x ⊓ y) ↔ atSample s x ∧ atSample s y := by
    obtain ⟨_,_,_,hs⟩ := eval s
    rw [hs, hs, hs, le_inf_iff]
  have complement (s : Sample B) (x : B) (hx : x ∈ s) :
      atSample s xᶜ ↔ ¬ atSample s x := by
    obtain ⟨b,hb,dec,hs⟩ := eval s
    rw [hs, hs]
    constructor
    · intro h₁ h₂
      apply hb
      have h := le_inf h₂ h₁
      exact le_bot_iff.mp (le_trans h (BooleanAlgebra.inf_compl_le_bot x))
    · exact (dec _ hx).resolve_left
  have neg (x : B) : truth xᶜ ↔ ¬ truth x := by
    constructor
    · intro hn hp
      exact F.proper (F.mono (fun s h => ((complement s x h.1).mp h.2.1) h.2.2)
        (F.inter (F.cone x) (F.inter hn hp)))
    · intro h
      rcases F.decide (atSample · x) with yes | no
      · exact (h yes).elim
      · exact F.mono (fun s hn => (complement s x hn.1).mpr hn.2) (F.inter (F.cone x) no)
  have conj (x y : B) : truth (x ⊓ y) ↔ truth x ∧ truth y := by
    constructor
    · intro h
      exact ⟨F.mono (fun s hs => ((meet s x y).mp hs).1) h,
        F.mono (fun s hs => ((meet s x y).mp hs).2) h⟩
    · exact fun h => F.mono (fun s => (meet s x y).mpr) (F.inter h.1 h.2)
  have yes : truth ⊤ := F.mono (fun s _ => topT s) (F.cone (⊤ : B))
  have no : ¬ truth ⊥ := fun h => F.proper (F.mono botF h)
  refine ⟨fun x => decide (truth x), by simp [no], by simp [yes], ?_, ?_⟩
  · intro x y
    by_cases hx : truth x <;> by_cases hy : truth y <;> simp [propext (conj x y), hx, hy]
  · intro x
    simp only [propext (neg x), decide_not]

/-- Pull an unordered finite sample back along an injection. The proof of
finiteness enumerates its finite preimage one point at a time, inside Prop. -/
private def preimage {A : Type u} {B : Type v} [∀ p : Prop, Decidable p]
    (e : B → A) (hi : Function.Injective e) (s : Sample A) : Sample B where
  contains x := e x ∈ s
  finite := by
    induction s using Sample.induction with
    | empty => exact ⟨[], fun x => ⟨fun h => (List.not_mem_nil h).elim,
          fun h => (List.not_mem_nil h).elim⟩⟩
    | step a s ih =>
      obtain ⟨l,hl⟩ := ih
      by_cases h : ∃ b, e b = a
      · obtain ⟨b,rfl⟩ := h
        exact ⟨b :: l, fun x => (or_congr hi.eq_iff (hl x)).trans List.mem_cons.symm⟩
      · refine ⟨l, fun x => (or_iff_right_of_imp ?_).trans (hl x)⟩
        exact fun hx => (h ⟨x,hx⟩).elim

/-- The local implication over a pure transitive hierarchy: every nontrivial
Boolean algebra whose carrier is included in the hierarchy has a two-valued
homomorphism, using just the given fine ultrafilter on the hierarchy. -/
theorem boolean_from_fine {T : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    [∀ p : Prop, Decidable p] (H : Hierarchy T I) {U : (Sample T → Prop) → Prop}
    (F : Fine U) (B : Type w) [BooleanAlgebra B] [Nontrivial B]
    (e : B → T) (hi : Function.Injective e) : BooleanPoint B := by
  obtain ⟨r,o⟩ := order_from_fine H F
  let rb := fun x y => r (e x) (e y)
  have ob : StrictOn (fun _ => True) rb :=
    ⟨fun x _ => o.irrefl (e x) trivial,
      fun _ _ _ => o.trans trivial trivial trivial,
      fun _ _ hn => o.compare trivial trivial (fun h => hn (hi h))⟩
  let V := fun (p : Sample B → Prop) => U (fun s => p (preimage e hi s))
  have G : Fine V := {
    proper := F.proper
    mono := fun h => F.mono (fun s => h (preimage e hi s))
    inter := F.inter
    decide := fun p => F.decide (fun s => p (preimage e hi s))
    cone := fun x => F.cone (e x) }
  exact fine_boolean G ob

end RadoSelection
