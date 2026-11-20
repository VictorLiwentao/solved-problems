module

public import SolvedProblems.RationalReturnsSplit

@[expose] public section

namespace RationalReturns

/-- The columns of successive north steps form a rational Dyck path if they
are weakly increasing and each step starts above the line between the endpoints. -/
def IsPath {m n : ℕ} (w : Word m n) : Prop :=
  Monotone w ∧ ∀ r, (w r).val ≤ edge m n r.val

/-- The first missing positive stride multiple is `k*d`. -/
def HasRun {m n : ℕ} (d k : ℕ) (w : Word m n) : Prop :=
  0 < k ∧ (∀ q, 0 < q → q < k → ∃ r, (w r).val = q*d) ∧
    ∀ r, (w r).val ≠ k*d

/-- A return is an equality between a north-step column and its row boundary. -/
noncomputable def returnCount {m n : ℕ} (w : Word m n) : ℕ := by
  classical
  exact ((Finset.range n).filter (fun a ↦ ∃ r : Fin n,
    r.val = a ∧ (w r).val = edge m n a)).card

/-- Number of physical north-step words with the two prescribed statistics. -/
noncomputable def jointCount (m n d k ℓ : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Word m n // IsPath w ∧ HasRun d k w ∧ returnCount w = ℓ}

private theorem full_valid {m n d k : ℕ} (hn : 0 < n) (hd : 0 < d) (hstride : d ≤ m/n)
    (hk : 0 < k) (hkn : k ≤ n) (w : Word m n) :
    Valid m n d k 0 n w ↔ IsPath w ∧ HasRun d k w := by
  have last : edge m n n = m := by simp [edge,Nat.mul_div_cancel_left _ hn]
  have width : k*d ≤ m := (Nat.mul_le_mul_right d hkn).trans <|
    (Nat.mul_le_mul_left n hstride).trans (by simpa [Nat.mul_comm] using Nat.div_mul_le_self m n)
  constructor
  · intro h
    refine ⟨⟨h.1,fun r ↦ by simpa using (h.2.1 r).2⟩,hk,?_,h.2.2.1⟩
    intro q _ hq
    apply h.2.2.2 (q*d) (by simp [edge]) (by rw [last]; exact (Nat.mul_lt_mul_of_pos_right hq hd).trans_le width)
    exact ⟨q,hq,rfl⟩
  · rintro ⟨⟨mono,bound⟩,_,hit,avoid⟩
    refine ⟨mono, fun r ↦ ⟨by simp [edge], by simpa using bound r⟩, avoid, ?_⟩
    rintro c _ _ ⟨q,hq,rfl⟩
    cases q with
    | zero =>
      let z : Fin n := ⟨0,hn⟩
      exact ⟨z, by simpa [z,edge] using bound z⟩
    | succ a => exact hit _ (Nat.succ_pos _) hq

private theorem contact_count {m n d k : ℕ} (hn : 0<n) (w : Segment m n d k 0 n) :
    returnCount w.val = (contactRows w).card+1 := by
  classical
  let z : Fin n := ⟨0,hn⟩
  have atZero : (w.val z).val = edge m n 0 := by simpa [edge,z] using (w.property.2.1 z).2
  have eqv : (Finset.range n).filter (fun a ↦ ∃ r : Fin n,
      r.val = a ∧ (w.val r).val = edge m n a) = insert 0 (contactRows w) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, contactRows,
      Finset.mem_Ioo, Nat.zero_add]
    constructor
    · rintro ⟨lt,h⟩
      by_cases eq : a=0
      · exact Or.inl eq
      · exact Or.inr ⟨⟨Nat.pos_of_ne_zero eq,lt⟩,h⟩
    · rintro (rfl | ⟨⟨_,hi⟩,hit⟩)
      · exact ⟨hn,z,rfl,atZero⟩
      · exact ⟨hi,hit⟩
  have h0 : 0 ∉ contactRows w := by simp [contactRows]
  change ((Finset.range n).filter (fun a ↦ ∃ r : Fin n, r.val = a ∧ (w.val r).val = edge m n a)).card = _
  rw [eqv, Finset.card_insert_of_notMem h0]

open scoped Classical in
/-- The full rectangle has one compulsory return at its initial row. Its remaining
returns agree with the strict interior contacts used to form the transfer matrix. -/
theorem jointCount_eq_segment {m n d k ℓ : ℕ} (hn : 0<n) (_hm : n≤m) (hd : 0<d)
    (hstride : d≤m/n) (hk : 0<k) (hkn : k≤n) :
    jointCount m n d k ℓ = Fintype.card {w : Segment m n d k 0 n // (contactRows w).card+1 = ℓ} := by
  classical
  unfold jointCount
  apply Fintype.card_congr
  refine ⟨fun w ↦ ⟨⟨w.val,(full_valid hn hd hstride hk hkn _).mpr ⟨w.property.1,w.property.2.1⟩⟩,?_⟩,
    fun w ↦ ⟨w.val.val, ?_⟩,fun _ ↦ rfl,fun _ ↦ rfl⟩
  · rw [← contact_count hn]; exact w.property.2.2
  · obtain ⟨path,run⟩ := (full_valid hn hd hstride hk hkn _).mp w.val.property
    exact ⟨path,run,(contact_count hn w.val).trans w.property⟩

end RationalReturns
