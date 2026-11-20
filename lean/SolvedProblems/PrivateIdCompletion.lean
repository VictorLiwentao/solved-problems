module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

open Set Function

namespace PrivateIdentification

private theorem injective_update_missing {u : ℕ → ℕ} (hu : Injective u) {b : ℕ}
    (hb : b ∉ range u) (t : ℕ) : Injective (update u t b) := by
  intro i j hij
  by_cases hi : i = t
  · subst i
    by_cases hj : j = t
    · exact hj.symm
    · rw [update_self, update_of_ne hj] at hij
      exact (hb ⟨j, hij.symm⟩).elim
  · by_cases hj : j = t
    · subst j
      rw [update_of_ne hi, update_self] at hij
      exact (hb ⟨i, hij⟩).elim
    · rw [update_of_ne hi, update_of_ne hj] at hij
      exact hu hij

/-- Build a full enumeration as the prefix limit of streams in an open margin
of a closed-event probability bound. A fresh word is inserted only when absent. -/
theorem complete_streams (L : Set ℕ) (r : Bool) (x : ℕ → ℕ)
    (hx : ∀ j, x j ∈ L) (hr : r = true → Injective x)
    (good : (ℕ → ℕ) → Prop) (hgood : good x)
    (edit : ∀ u, good u → ∃ t, ∀ b q, t ≤ q → good (update u q b)) :
    ∃ y : ℕ → ℕ, (r = true → Injective y) ∧ range y = L ∧
      ∀ t, ∃ u, good u ∧ ∀ j < t, u j = y j := by
  classical
  let Q (n : ℕ) (z : (ℕ → ℕ) × ℕ) : Prop :=
    (∀ j, z.1 j ∈ L) ∧ (r = true → Injective z.1) ∧ n ≤ z.2 ∧
      (∀ b < n, b ∈ L → ∃ j < z.2, z.1 j = b) ∧ good z.1
  have advance : ∀ n z, Q n z → ∃ w, Q (n+1) w ∧
      z.2 ≤ w.2 ∧ ∀ j < z.2, z.1 j = w.1 j := by
    intro n z hz
    obtain ⟨hL, hinj, hn, hprev, hg⟩ := hz
    have finish (v : ℕ → ℕ) (m : ℕ) (hm : z.2 < m)
        (hp : ∀ j < z.2, z.1 j = v j) (hnw : n ∈ L → ∃ j < m, v j = n)
        (hvL : ∀ j, v j ∈ L) (hvj : r = true → Injective v) (hgv : good v) :
        Q (n + 1) (v, m) := by
      refine ⟨hvL, hvj, by dsimp; omega, ?_, hgv⟩
      intro b hb hbL
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hb) with hlt | rfl
      · obtain ⟨j, hj, hjb⟩ := hprev b hlt hbL
        exact ⟨j, hj.trans hm, (hp j hj).symm.trans hjb⟩
      · exact hnw hbL
    by_cases hmem : n ∈ L
    · by_cases halready : n ∈ range z.1
      · obtain ⟨j, hj⟩ := halready
        let m := max z.2 j + 1
        have hm : z.2 < m := by dsimp [m]; omega
        have hjm : j < m := by dsimp [m]; omega
        exact ⟨(z.1, m), finish _ _ hm (fun _ _ ↦ rfl) (fun _ ↦ ⟨j, hjm, hj⟩)
          hL hinj hg, hm.le, fun _ _ ↦ rfl⟩
      · obtain ⟨t, ht⟩ := edit z.1 hg
        let q := max t z.2
        let v := update z.1 q n
        have hm : z.2 < q+1 := by dsimp [q]; omega
        have hp : ∀ j < z.2, z.1 j = v j := by
          intro j hj
          exact (update_of_ne (by dsimp [q]; omega : j ≠ q) n z.1).symm
        have hVL : ∀ j, v j ∈ L := by
          intro j
          by_cases h : j = q
          · simpa [v, h] using hmem
          · simpa [v, update_of_ne h] using hL j
        exact ⟨(v, q+1), finish _ _ hm hp (fun _ ↦ ⟨q, by omega, update_self ..⟩)
          hVL (fun h ↦ injective_update_missing (hinj h) halready q)
          (ht n q (Nat.le_max_left ..)), hm.le, hp⟩
    · exact ⟨(z.1, z.2+1), finish _ _ (by omega) (fun _ _ ↦ rfl)
        (fun h ↦ (hmem h).elim) hL hinj hg, by omega, fun _ _ ↦ rfl⟩
  let start : {z // Q 0 z} := ⟨(x,0), hx, hr, Nat.zero_le _, by simp, hgood⟩
  let next (n : ℕ) (z : {z // Q n z}) : {w // Q (n+1) w} :=
    ⟨(advance n z.val z.property).choose, (advance n z.val z.property).choose_spec.1⟩
  let stage (n : ℕ) : {z // Q n z} := Nat.rec start next n
  let u (n : ℕ) := (stage n).val.1
  let f (n : ℕ) := (stage n).val.2
  have qs (n : ℕ) : Q n ((u n), f n) := (stage n).property
  have step (n : ℕ) : f n ≤ f (n+1) ∧ ∀ j < f n, u n j = u (n+1) j :=
    (advance n (stage n).val (stage n).property).choose_spec.2
  have fm : Monotone f := monotone_nat_of_le_succ fun n ↦ (step n).1
  have chain (n m : ℕ) (hnm : n ≤ m) : ∀ j < f n, u n j = u m j := by
    induction m, hnm using Nat.le_induction with
    | base => exact fun _ _ ↦ rfl
    | succ m hm ih =>
      exact fun j hj ↦ (ih j hj).trans ((step m).2 j (hj.trans_le (fm hm)))
  let y (j : ℕ) := u (j+1) j
  have limit (n j : ℕ) (hj : j < f n) : u n j = y j := by
    let m := max n (j+1)
    have hj' : j < f (j+1) := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (qs (j+1)).2.2.1
    exact (chain n m (Nat.le_max_left ..) j hj).trans
      (chain (j+1) m (Nat.le_max_right ..) j hj').symm
  refine ⟨y, ?_, ?_, ?_⟩
  · intro h i j heq
    let m := max i j + 1
    have hm := (qs m).2.2.1
    have hi : i < f m := by dsimp [m] at *; omega
    have hj : j < f m := by dsimp [m] at *; omega
    exact (qs m).2.1 h ((limit m i hi).trans (heq.trans (limit m j hj).symm))
  · apply Subset.antisymm
    · rintro _ ⟨j,rfl⟩
      exact (qs (j+1)).1 j
    · intro b hb
      obtain ⟨j, hj, hjb⟩ := (qs (b+1)).2.2.2.1 b (by omega) hb
      exact ⟨j, (limit (b+1) j hj).symm.trans hjb⟩
  · exact fun t ↦ ⟨u t, (qs t).2.2.2.2,
      fun j hj ↦ limit t j (hj.trans_le (qs t).2.2.1)⟩

end PrivateIdentification
