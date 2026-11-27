module

public import SolvedProblems.MISModel

@[expose] public section

namespace MISQueries

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A clique on `e ∪ B` with the distinguished pair optionally deleted.
Every other vertex is isolated. -/
def hidden (e B : Finset V) (keep : Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ x ∈ e ∪ B ∧ y ∈ e ∪ B ∧ (keep = true ∨ ¬(x ∈ e ∧ y ∈ e))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.imp id (fun h' k => h' k.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype V] in
theorem pair_spanned {e : Finset V} (he : e.card = 2) {x y : V}
    (hx : x ∈ e) (hy : y ∈ e) (hxy : x ≠ y) : e = {x,y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
  · simp [he,hxy]

omit [Fintype V] in
theorem hidden_distinct {e : Finset V} (he : e.card = 2) (B : Finset V) : hidden e B false ≠ hidden e B true := by
  obtain ⟨x,y,hn, rfl⟩ := Finset.card_eq_two.mp he
  intro h
  have ha : (hidden {x,y} B true).Adj x y := ⟨hn, by simp, by simp, .inl rfl⟩
  rw [← h] at ha
  exact ha.2.2.2.elim (by decide) (fun h' => h' ⟨by simp, by simp⟩)

theorem hidden_degree {e B : Finset V} (hc : e.card = 2) {D : ℕ} (hB : B.card < D) (keep : Bool) :
    DegreeBound (hidden e B keep) D := by
  classical
  intro x
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hx : x ∈ e ∪ B
  · have hs : (hidden e B keep).neighborFinset x ⊆ (e ∪ B).erase x := by
      intro y hy
      have ha := ((hidden e B keep).mem_neighborFinset ..).mp hy
      exact Finset.mem_erase.mpr ⟨ha.1.symm,ha.2.2.1⟩
    have hle := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hx] at hle
    have hu := Finset.card_union_le e B
    omega
  · have hempty : (hidden e B keep).neighborFinset x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun _ h => hx (((hidden e B keep).mem_neighborFinset ..).mp h).2.1
    simp [hempty]

omit [DecidableEq V] in
theorem legal_exists (G : SimpleGraph V) (Q : Finset V) : ∃ A, Legal G Q A := by
  let P (S : Finset V) := S ⊆ Q ∧ ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y
  have h0 : P ∅ := by simp [P]
  obtain ⟨A,_,hA⟩ := exists_maximal_ge_of_wellFoundedGT P ∅ h0
  exact ⟨A,hA⟩

omit [Fintype V] [DecidableEq V] in
theorem legal_congr {G H : SimpleGraph V} {Q A : Finset V}
    (hh : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y ↔ H.Adj x y) (h : Legal G Q A) : Legal H Q A := by
  have hcond (T : Finset V) :
      (T ⊆ Q ∧ ∀ x ∈ T, ∀ y ∈ T, ¬G.Adj x y) ↔ (T ⊆ Q ∧ ∀ x ∈ T, ∀ y ∈ T, ¬H.Adj x y) := by
    constructor <;> rintro ⟨hT,hi⟩ <;> refine ⟨hT, fun x hx y hy he => hi _ hx _ hy ?_⟩
    · exact (hh _ (hT hx) _ (hT hy)).2 he
    · exact (hh _ (hT hx) _ (hT hy)).1 he
  exact ⟨(hcond A).1 h.1, fun T hT hsub => h.2 ((hcond T).2 hT) hsub⟩

omit [Fintype V] in
/-- A queried blocker masks the hidden bit: choose that blocker and every
queried outside isolate. This one answer is maximal under either edge status. -/
theorem blocker_answer {e B Q : Finset V} {b : V} (hb : b ∈ B) (hbe : b ∉ e) (hq : b ∈ Q) (k : Bool) :
    Legal (hidden e B k) Q (insert b (Q \ (e ∪ B))) := by
  classical
  constructor
  · refine ⟨Finset.insert_subset hq (Finset.sdiff_subset), ?_⟩
    intro x hx y hy ha
    rcases Finset.mem_insert.mp hx with rfl | hi
    · rcases Finset.mem_insert.mp hy with rfl | hj
      · exact ha.1 rfl
      · exact (Finset.mem_sdiff.mp hj).2 ha.2.2.1
    · exact (Finset.mem_sdiff.mp hi).2 ha.2.1
  · intro T ht hsub v hv
    by_cases he : v ∈ e ∪ B
    · by_cases hvb : v = b
      · exact Finset.mem_insert.mpr (.inl hvb)
      · have hadj : (hidden e B k).Adj v b := ⟨hvb, he, Finset.mem_union_right _ hb, .inr fun h => hbe h.2⟩
        exact False.elim (ht.2 v hv b (hsub (Finset.mem_insert_self ..)) hadj)
    · exact Finset.mem_insert.mpr (.inr (Finset.mem_sdiff.mpr ⟨ht.1 hv,he⟩))

omit [Fintype V] in
/-- When the distinguished pair is not queried in full, the two induced
query graphs have exactly the same edges. -/
theorem omitted_pair {e Q : Finset V} (hc : e.card = 2) (hn : ¬e ⊆ Q) (B : Finset V) :
    ∀ x ∈ Q, ∀ y ∈ Q, (hidden e B false).Adj x y ↔ (hidden e B true).Adj x y := by
  intro x hx y hy
  constructor
  · exact fun h => ⟨h.1,h.2.1,h.2.2.1,.inl rfl⟩
  · intro h
    refine ⟨h.1,h.2.1,h.2.2.1,.inr ?_⟩
    rintro ⟨he,he'⟩
    apply hn
    rw [pair_spanned hc he he' h.1]
    exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)

/-- The two fixed deterministic oracles agree on every query except a query
containing both endpoints and containing no blocker. -/
theorem coupled_oracles {e B : Finset V} (hc : e.card = 2) (hdis : Disjoint e B) :
    ∃ O : Bool → Oracle V, (∀ k, LegalOracle (hidden e B k) (O k)) ∧
      ∀ Q, (¬e ⊆ Q ∨ ¬Disjoint Q B) → O false Q = O true Q := by
  classical
  have hQ (Q : Finset V) : ∃ f : Bool → Finset V, (∀ k, Legal (hidden e B k) Q (f k)) ∧
      ((¬e ⊆ Q ∨ ¬Disjoint Q B) → f false = f true) := by
    by_cases hQB : Disjoint Q B
    · by_cases hfull : e ⊆ Q
      · exact ⟨fun k => (legal_exists (hidden e B k) Q).choose,
          fun k => (legal_exists (hidden e B k) Q).choose_spec, fun h => (h.elim (· hfull) (· hQB)).elim⟩
      · obtain ⟨A,hA⟩ := legal_exists (hidden e B false) Q
        exact ⟨fun _ => A, fun k => by cases k; exact hA; exact legal_congr (omitted_pair hc hfull B) hA,
          fun _ => rfl⟩
    · obtain ⟨b,hbQ,hbB⟩ := Finset.not_disjoint_iff.mp hQB
      exact ⟨fun _ => insert b (Q \ (e ∪ B)),
        blocker_answer hbB (fun he => Finset.disjoint_left.mp hdis he hbB) hbQ, fun _ => rfl⟩
  exact ⟨fun k Q => (hQ Q).choose k, fun k Q => (hQ Q).choose_spec.1 k,
    fun Q => (hQ Q).choose_spec.2⟩

end MISQueries
