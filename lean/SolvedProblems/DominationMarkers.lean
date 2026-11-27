module

public import SolvedProblems.DominationAntichain

@[expose] public section

namespace DominationVC

abbrev Slots (a m : ℕ) := Fin a ⊕ (Fin a ⊕ (Fin m × Bool))
abbrev Index (b : ℕ) := Fin b × Fin b

/-- Two data blocks record the row and column cross-neighborhoods. Exactly one
of each marker pair is selected, according to the address of the witness. -/
def trace {a b m : ℕ} (P : Fin a → Fin b → Prop) (code : Index b ↪ (Fin m → Bool))
    (i : Index b) : Slots a m → Prop
  | .inl x => P x i.1
  | .inr (.inl x) => P x i.2
  | .inr (.inr (k,bit)) => bit = code i k

structure WitnessArray (V : Type*) [PartialOrder V] {a b m : ℕ}
    (P : Fin a → Fin b → Prop) (code : Index b ↪ (Fin m → Bool)) where
  A : Slots a m ↪ V
  antichain : ∀ r s, ¬A r < A s
  w : Index b → V
  sees : ∀ i r, Visible (w i) (A r) ↔ trace P code i r

theorem array_exists {V : Type*} [PartialOrder V] [Fintype V] [DecidableEq V]
    {a b m : ℕ} {S : Finset V} (hs : (closedFamily (incomparability V)).Shatters S)
    (hsize : 2 * (2*a + 2*m) ≤ S.card) (P : Fin a → Fin b → Prop)
    (code : Index b ↪ (Fin m → Bool)) : Nonempty (WitnessArray V P code) := by
  classical
  have hc : Fintype.card (Slots a m) = 2*a + 2*m := by simp [Slots]; omega
  obtain ⟨A, ha, anti⟩ := large_antichain (I := Slots a m) hs (hc ▸ hsize)
  have ex (i : Index b) : ∃ w, ∀ r, Visible w (A r) ↔ trace P code i r := by
    obtain ⟨w, hw⟩ := realize hs (fun v => ∃ q, A q = v ∧ trace P code i q)
    refine ⟨w, fun r => (hw _ (ha r)).trans ?_⟩
    constructor
    · rintro ⟨q, he, hq⟩
      exact A.injective he ▸ hq
    · exact fun h => ⟨r, rfl, h⟩
  exact ⟨⟨A, anti, fun i => (ex i).choose, fun i => (ex i).choose_spec⟩⟩

namespace WitnessArray
variable {V : Type*} [PartialOrder V] {a b m : ℕ}
    {P : Fin a → Fin b → Prop} {code : Index b ↪ (Fin m → Bool)} (d : WitnessArray V P code)

theorem distinguishes {i j : Index b} (hn : i ≠ j) :
    ∃ r, Visible (d.w i) (d.A r) ∧ ¬Visible (d.w j) (d.A r) := by
  classical
  obtain ⟨k,hk⟩ : ∃ k, code i k ≠ code j k := by
    by_contra! he
    exact hn (code.injective (funext he))
  refine ⟨.inr (.inr (k, code i k)), (d.sees _ _).2 rfl, ?_⟩
  exact fun h => hk ((d.sees _ _).1 h)

theorem w_injective : Function.Injective d.w := by
  intro i j h
  by_contra hn
  obtain ⟨r, hi, hj⟩ := d.distinguishes hn
  exact hj (h ▸ hi)

theorem outside (hm : 0 < m) (i : Index b) (r : Slots a m) : d.w i ≠ d.A r := by
  intro he
  let k : Fin m := ⟨0, hm⟩
  let s : Slots a m := .inr (.inr (k, !(code i k)))
  have h : Visible (d.w i) (d.A s) := he ▸ ⟨d.antichain r s, d.antichain s r⟩
  have hv : (!(code i k)) = code i k := (d.sees i s).1 h
  cases c : code i k <;> simp [c] at hv

/-- A positive witness lies strictly below some member of the antichain. -/
def positive (i : Index b) : Prop := ∃ r, d.w i < d.A r

theorem same_orientation {i j : Index b} (hne : i ≠ j) (hc : d.positive i ↔ d.positive j) :
    ¬d.w i < d.w j := by
  intro hlt
  by_cases hpos : d.positive j
  · obtain ⟨r,hi,hj⟩ := d.distinguishes hne
    obtain ⟨s,hs⟩ := hpos
    have hbefore : d.w j < d.A r := by
      by_contra h
      exact hj ⟨h, fun h' => d.antichain r s (h'.trans hs)⟩
    exact hi.1 (hlt.trans hbefore)
  · obtain ⟨r,hj,hi⟩ := d.distinguishes hne.symm
    have hi' : ¬d.positive i := fun h => hpos (hc.1 h)
    have hafter : d.A r < d.w i := by
      by_contra h
      exact hi ⟨fun h' => hi' ⟨r,h'⟩, h⟩
    exact hj.2 (hafter.trans hlt)

end WitnessArray
end DominationVC
