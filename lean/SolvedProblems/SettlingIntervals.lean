module

public import SolvedProblems.SettlingMajorants

@[expose] public section

open Filter

namespace StrongSettling

namespace Enumeration

/-- A genuine positive entry at a successor stage (stage zero carries no delay). -/
def Entry (E : Enumeration) (t i : ℕ) : Prop := 0 < t ∧ E.read (t-1) i < E.read t i

theorem entry_le_modulus (E : Enumeration) {t i x : ℕ} (h : E.Entry t i) (hi : i≤x) :
    t ≤ E.modulus x := by
  by_contra! lt
  have late : E.modulus x ≤ t-1 := by omega
  exact h.2.not_ge ((E.read_le _ _).trans_eq (E.final_at late i hi).symm)

theorem last_entry (E : Enumeration) {x : ℕ} (pos : 0 < E.modulus x) :
    ∃ i ≤ x, E.Entry (E.modulus x) i := by
  have lower : ¬E.modulus x ≤ E.modulus x-1 := by omega
  rw [E.modulus_le_iff] at lower
  push Not at lower
  obtain ⟨i,hi,unequal⟩ := lower
  refine ⟨i,hi,pos,?_⟩
  rw [E.final_at (x := x) le_rfl i hi]
  exact lt_of_le_of_ne (E.read_le _ _) unequal

end Enumeration

/-- A signal at stage s activates a response in the earlier block of A.
Each later entry in B below its cutoff generates a second kind of request.
Only actual entry stages and positions of the two enumerations occur here. -/
def Responses (A B : Enumeration) (F : ℕ → ℕ) (lo s cutoff : ℕ) : Prop :=
  (∃ t i, i≤lo ∧ F s<t ∧ A.Entry t i) ∧
  ∀ t i, s<t → i≤cutoff → B.Entry t i → ∃ u j, j≤lo ∧ F t<u ∧ A.Entry u j

/-- The domination inequality on the whole interval between successive
final markers, including the case of a last entry after activation. -/
theorem interval_domination (A B : Enumeration) (F G : ℕ → ℕ) (f : Monotone F) (g : Monotone G)
    {lo hi x s cutoff : ℕ} (low : lo≤x) (high : x<hi) (size : G hi ≤ cutoff)
    (responses : Responses A B F lo s cutoff) : F (B.modulus (G x)) < A.modulus x := by
  by_cases early : B.modulus (G x) ≤ s
  · obtain ⟨t,i,whereAt,delay,enters⟩ := responses.1
    exact (lt_of_le_of_lt (f early) delay).trans_le (A.entry_le_modulus enters (whereAt.trans low))
  · have late := Nat.lt_of_not_ge early
    obtain ⟨i,whereAt,enters⟩ := B.last_entry (Nat.zero_lt_of_lt late)
    obtain ⟨u,j,whereNext,delay,respond⟩ := responses.2 _ i late (whereAt.trans ((g high.le).trans size)) enters
    exact delay.trans_le (A.entry_le_modulus respond (whereNext.trans low))

private theorem computable_majorant {f : ℕ → ℕ} (hf : Computable f) :
    ∃ F : ℕ → ℕ, Computable F ∧ Monotone F ∧ ∀ i, f i ≤ F i := by
  let F (n : ℕ) := Nat.rec (motive := fun _ => ℕ) (f 0) (fun k z => max z (f (k+1))) n
  have effective : Computable F := Computable.nat_rec Computable.id (Computable.const (f 0))
    (((Primrec.to_comp Primrec.nat_max).to₂.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂)
  exact ⟨F,effective,monotone_nat_of_le_succ (fun _ => le_max_left _ _),fun i => by
    cases i with | zero => exact le_rfl | succ i => exact le_max_right ..⟩

/-- In a given ordered pair of rows, successful response processing at all
sufficiently late levels yields Csima and Shore's full strong comparison. -/
theorem row_comparison (A B : Enumeration) (M : ℕ → ℕ) (grow : StrictMono M)
    (signals : ∀ F G : ℕ → ℕ, Computable F → Computable G → Monotone F → Monotone G →
      ∀ᶠ k in atTop, ∃ s u, G (M (k+1)) ≤ u ∧ Responses A B F (M k) s u) : Strong B A := by
  intro f g hf hg
  obtain ⟨F,cf,mf,bf⟩ := computable_majorant hf
  obtain ⟨G,cg,mg,bg⟩ := computable_majorant hg
  obtain ⟨N,later⟩ := eventually_atTop.mp (signals F G cf cg mf mg)
  apply eventually_atTop.mpr
  refine ⟨M N,fun x hx => ?_⟩
  have stop : ∃ k, x < M k := ⟨x+1,Nat.lt_succ_self x |>.trans_le (grow.id_le _)⟩
  let j := Nat.find stop
  have upper : x<M j := Nat.find_spec stop
  have index : N<j := by
    by_contra! low
    exact upper.not_ge ((grow.monotone low).trans hx)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (n:=j) (by omega)
  rw [hk] at upper
  have lower : M k ≤ x := Nat.le_of_not_gt (Nat.find_min stop (show k<j by omega))
  obtain ⟨s,u,size,valid⟩ := later k (by omega)
  have whole := interval_domination A B F G mf mg lower upper size valid
  exact (bf _).trans_lt ((mf (B.modulus_mono (bg x))).trans_lt whole)

end StrongSettling
