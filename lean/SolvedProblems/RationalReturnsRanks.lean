module

public import SolvedProblems.RationalReturnsBags

@[expose] public section

namespace RationalReturns

theorem lt_flag_iff {A B : Finset ℕ} {D : ℕ → ℕ} {L U h z : ℕ} :
    z < flag A B D L U h ↔ z < A.card ∧
      ∀ c ∈ Finset.Icc L U, before B c + h < D c → z < before A c := by
  simp [flag, Finset.lt_min'_iff]
  grind

theorem flag_mono (A B : Finset ℕ) (D : ℕ → ℕ) (L U : ℕ) :
    Monotone (flag A B D L U) := by
  intro i j hij
  by_contra! smaller
  have h := lt_flag_iff.mp smaller
  exact (Nat.lt_irrefl _) (lt_flag_iff.mpr ⟨h.1,fun c hc large ↦ h.2 c hc (by omega)⟩ :
    flag A B D L U j < flag A B D L U j)

theorem rank_before (A : Finset ℕ) (q : Fin A.card) (c : ℕ) :
    q.val < before A c ↔ ((A.orderIsoOfFin rfl) q).val < c := by
  let f := A.orderEmbOfFin rfl
  have sorted : bag f = A.val := by
    unfold bag
    rw [List.ofFn_eq_map, Finset.listMap_orderEmbOfFin_finRange]
    exact Multiset.sort_eq _ _
  have h := lt_less_iff f.monotone q c
  rw [sorted, less_val] at h
  exact h

/-- Convert between physical column numbers in a residual path segment and
zero-based ranks below every arrival flag. -/
noncomputable def residualRanks (A B : Finset ℕ) (D : ℕ → ℕ) (L U R : ℕ)
    (feas : ∀ c ∈ Finset.Icc L U, D c ≤ before B c + R) :
    {w : Fin R → ℕ // Monotone w ∧ (∀ q, w q ∈ A) ∧
      ∀ c ∈ Finset.Icc L U, D c ≤ before B c + less (bag w) c} ≃
    {z : (q : Fin R) → Fin (flag A B D L U q.val) // Monotone (fun q ↦ (z q).val)} := by
  let e := A.orderIsoOfFin rfl
  let enc (w : Fin R → ℕ) (mem : ∀ q, w q ∈ A) (q : Fin R) := e.symm ⟨w q, mem q⟩
  let dec (z : (q : Fin R) → Fin (flag A B D L U q.val)) (q : Fin R) : Fin A.card :=
    ⟨(z q).val,(lt_flag_iff.mp (z q).isLt).1⟩
  have back (w) (mem : ∀ q, w q ∈ A) (q : Fin R) : (e (enc w mem q)).val = w q := by
    simp [enc]
  refine ⟨fun w ↦ ⟨fun q ↦ ⟨(enc w.val w.property.2.1 q).val, ?_⟩, ?_⟩,
    fun z ↦ ⟨fun q ↦ (e (dec z.val q)).val, ?_, fun q ↦ (e (dec z.val q)).property, ?_⟩,
    ?_, ?_⟩
  · apply lt_flag_iff.mpr
    refine ⟨(enc _ _ q).isLt, ?_⟩
    intro c hc high
    apply (rank_before A _ c).mpr
    change (e (enc _ _ q)).val < c
    rw [back]
    apply (lt_less_iff w.property.1 q c).mp
    have := w.property.2.2 c hc
    omega
  · intro i j le
    exact e.symm.monotone (show (⟨w.val i,w.property.2.1 i⟩ : A) ≤ ⟨w.val j,w.property.2.1 j⟩
      from w.property.1 le)
  · intro i j le
    exact e.monotone (show dec z.val i ≤ dec z.val j from z.property le)
  · intro c hc
    have hm : Monotone (fun q ↦ (e (dec z.val q)).val) :=
      fun i j le ↦ e.monotone (show dec z.val i ≤ dec z.val j from z.property le)
    have limit : D c - before B c ≤ R := by have := feas c hc; omega
    have need := (less_bound hm (c:=c) limit).mpr (by
      intro q hq
      apply (rank_before A (dec z.val q) c).mp
      exact (lt_flag_iff.mp (z.val q).isLt).2 c hc (by omega))
    omega
  · intro w
    apply Subtype.ext
    funext q
    exact back _ _ q
  · intro z
    apply Subtype.ext; funext q; apply Fin.ext
    change (e.symm (e (dec z.val q))).val = (dec z.val q).val
    rw [e.symm_apply_apply]

end RationalReturns
