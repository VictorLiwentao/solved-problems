module

public import SolvedProblems.PrivateIdEvents
public import SolvedProblems.PrivateIdCompletion
public import SolvedProblems.PrivateIdCapacity
public import SolvedProblems.PrivateIdProjection
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open MeasureTheory Set Function Filter Topology

namespace PrivateIdentification

/-- Extend an input entirely within L to a valid enumeration, preserving a measurable
event up to any prescribed additive loss. -/
theorem extend_event {s k : ℕ} {P : Mechanism s k} (hp : ProbLaw P)
    (hc : Causal P) {ω : ℝ → ℝ} (hw : Vanishes ω) (hpriv : PrivateWith P ω)
    (x : Input) (L : Set ℕ) (r : Bool) (hx : ∀ j, x j ∈ L)
    (hr : r = true → Injective x) {B : Set (Transcript s k)} (hB : MeasurableSet B)
    {η : ℝ} (hη : 0 < η) :
    ∃ y, Valid r L y ∧ (P x).real B - η ≤ (P y).real B := by
  classical
  let := hp x
  let : MetricSpace (Transcript s k) := PiNat.metricSpace
  obtain ⟨C, hCB, hclosed, hclose⟩ := hB.exists_isClosed_sdiff_lt
    (measure_ne_top (P x) B) (ENNReal.ofReal_ne_zero_iff.mpr hη)
  have h₀ : (P x).real (B \ C) < η := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hclose
    simpa only [measureReal_def, ENNReal.toReal_ofReal hη.le] using h
  rw [measureReal_sdiff hCB hclosed.measurableSet] at h₀
  let c := (P x).real B - η
  let good (u : Input) := c < (P u).real C
  have hxg : good x := by dsimp [good, c]; linarith
  have edit : ∀ u, good u → ∃ t, ∀ b q, t ≤ q → good (update u q b) := by
    intro u hu
    let a := ((P u).real C - c) / 2
    have ha : 0 < a := by dsimp [a]; exact half_pos (sub_pos.mpr hu)
    obtain ⟨t, ht⟩ := late_edit hp hc hw hpriv u hclosed ha
    refine ⟨t, fun b q hq ↦ ?_⟩
    by_cases hsame : b = u q
    · simpa [hsame] using hu
    have hn : Neighbors (update u q b) u :=
      ⟨q, by simpa using hsame, fun j hj ↦ update_of_ne hj _ _⟩
    have hpre : PrefixEq u (update u q b) t :=
      fun j hj ↦ (update_of_ne (hj.trans_le hq).ne b u).symm
    have h := ht _ hn hpre
    dsimp [a] at h
    change c < (P u).real C at hu
    change c < (P (update u q b)).real C
    linarith
  obtain ⟨y, hyj, hyL, hy⟩ := complete_streams L r x hx hr good hxg edit
  let := hp y
  have hCy : c ≤ (P y).real C := by
    apply ge_of_tendsto' (tendsto_envelope (P y) hclosed)
    intro t
    obtain ⟨u, hug, huy⟩ := hy t
    let := hp u
    rw [← hc u y t huy (envelope C t) (measurable_envelope C t) (envelope_prefix C t)]
    exact le_trans (le_of_lt hug) (measureReal_mono (subset_envelope C t))
  exact ⟨y, ⟨hyj, hyL⟩, hCy.trans (measureReal_mono hCB)⟩

private theorem common_input {s : ℕ} {L : Fin s → Set ℕ} (r : Bool)
    (h : Common r L) : ∃ x : Input, (r = true → Injective x) ∧ ∀ i j, x j ∈ L i := by
  classical
  cases r with
  | false =>
    obtain ⟨b, hb⟩ := h
    exact ⟨fun _ ↦ b, by simp, fun i _ ↦ mem_iInter.mp hb i⟩
  | true =>
    let f := Set.Infinite.natEmbedding (⋂ i, L i) h
    exact ⟨fun j ↦ (f j).val, fun _ ↦ Subtype.val_injective.comp f.injective,
      fun i j ↦ mem_iInter.mp (f j).property i⟩

/-- The sharp k/s minimax bound under a uniform privacy modulus, for repetition-free
enumerations with infinite common intersection and for arbitrary repetitions with a common word. -/
theorem private_identification_minimax : Minimax := by
  intro s k hk L _hL _hdistinct r hcommon
  have hs : 0 < s := Nat.zero_le k |>.trans_lt hk
  refine ⟨?_, lottery hk.le hs⟩
  intro P ω hp hc hw hpriv η hη
  obtain ⟨x, hr, hx⟩ := common_input r hcommon
  let := hp x
  obtain ⟨i, hi⟩ := some_low (P x) hs
  have hB := measurableSet_success (k := k) i
  obtain ⟨y, hyL, hy⟩ := extend_event hp hc hw hpriv x (L i) r (hx i) hr hB.compl hη
  let := hp y
  rw [probReal_compl_eq_one_sub hB, probReal_compl_eq_one_sub hB] at hy
  exact ⟨i, y, hyL, by linarith⟩

end PrivateIdentification
